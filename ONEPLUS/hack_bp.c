#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/kprobes.h>
#include <linux/kallsyms.h>
#include <linux/syscalls.h>
#include <linux/uaccess.h>
#include <linux/mm.h>
#include <linux/mmzone.h>
#include <linux/slab.h>
#include <linux/mutex.h>
#include <linux/hw_breakpoint.h>
#include <linux/perf_event.h>
#include <linux/miscdevice.h>
#include <linux/fs.h>
#include <linux/io.h>
#include <linux/pid.h>
#include <linux/sched.h>
#include <linux/kobject.h>
#include <linux/list.h>
#include <asm/io.h>
#include <asm/memory.h>
#include <asm/pgtable.h>
#include <asm/page.h>
#include <asm/cacheflush.h>

#if defined(__clang__) && defined(__has_attribute)
# if __has_attribute(no_sanitize)
#  define CFI_SAFE __attribute__((no_sanitize("cfi")))
# else
#  define CFI_SAFE
# endif
#else
# define CFI_SAFE
#endif

#ifndef VM_FAULT_ERROR
#define VM_FAULT_ERROR (VM_FAULT_OOM | VM_FAULT_SIGBUS | VM_FAULT_SIGSEGV | VM_FAULT_HWPOISON | VM_FAULT_HWPOISON_LARGE | VM_FAULT_FALLBACK)
#endif

#define DEVICE_NAME "hack_bp"
#define MAX_XFER    0x100000UL

/* IOCTL */
#define CMD_READ_MEM    0x1001
#define CMD_WRITE_MEM   0x1002
#define CMD_SET_BP      0x2001
#define CMD_DEL_BP      0x2002

struct ioctl_req {
    pid_t pid;
    unsigned long addr;
    unsigned long buf;
    size_t size;
    int type;
    int len;
    int bp_id;
    int delta;
    int reg_idx;
};

/* ================= 符号解析 ================= */

typedef unsigned long (*kallsyms_lookup_name_t)(const char *name);
static kallsyms_lookup_name_t real_kln;

typedef struct perf_event *(*pe_create_kcounter_t)(struct perf_event_attr *attr,
                                                   int cpu,
                                                   struct task_struct *task,
                                                   perf_overflow_handler_t cb,
                                                   void *context);
typedef void (*pe_release_kernel_t)(struct perf_event *event);
typedef struct pid *(*find_get_pid_t)(pid_t);
typedef struct task_struct *(*get_pid_task_t)(struct pid *, enum pid_type);
typedef void (*put_pid_t)(struct pid *);
typedef void (*put_task_struct_t)(struct task_struct *);
typedef struct mm_struct *(*get_task_mm_t)(struct task_struct *);
typedef void (*mmput_t)(struct mm_struct *);
typedef void (*flush_dcache_t)(const void *addr, size_t len);
typedef int (*printk_deferred_t)(const char *fmt, ...);
typedef struct vm_area_struct *(*find_vma_t)(struct mm_struct *, unsigned long);
typedef vm_fault_t (*handle_mm_fault_t)(struct vm_area_struct *, unsigned long,
                                        unsigned int, struct pt_regs *);

static pe_create_kcounter_t  _perf_create_kcounter;
static pe_release_kernel_t   _perf_release_kernel;
static find_get_pid_t        _find_get_pid;
static get_pid_task_t        _get_pid_task;
static put_pid_t             _put_pid;
static put_task_struct_t     _put_task_struct;
static get_task_mm_t         _get_task_mm;
static mmput_t               _mmput;
static flush_dcache_t        _flush_dcache;
static printk_deferred_t     _printk_deferred;
static find_vma_t            _find_vma;
static handle_mm_fault_t     _handle_mm_fault;

static int __kprobes kln_pre_handler(struct kprobe *p, struct pt_regs *regs) { return 0; }
static struct kprobe kln_kp = { .symbol_name = "kallsyms_lookup_name", .pre_handler = kln_pre_handler };

static CFI_SAFE unsigned long kln(const char *name)
{
    return real_kln ? real_kln(name) : 0;
}

#define LOG(fmt, ...) do { \
    if (_printk_deferred) _printk_deferred("[hack_bp] " fmt, ##__VA_ARGS__); \
    else pr_info("[hack_bp] " fmt, ##__VA_ARGS__); \
} while (0)

/* ================= 页表遍历 → 物理地址 ================= */

static bool translate_linear_address(struct mm_struct *mm, unsigned long va, phys_addr_t *out)
{
    pgd_t *pgd;
    p4d_t *p4d;
    pud_t *pud;
    pmd_t *pmd;
    pte_t *pte;

    if (!mm || !mm->pgd) return false;

    pgd = pgd_offset(mm, va);
    if (pgd_none(*pgd) || pgd_bad(*pgd)) return false;

    p4d = p4d_offset(pgd, va);
    if (p4d_none(*p4d) || p4d_bad(*p4d)) return false;

    pud = pud_offset(p4d, va);
    if (pud_none(*pud) || pud_bad(*pud)) return false;
    if (pud_sect(*pud)) {
        *out = (phys_addr_t)(pud_val(*pud) & PUD_MASK) | (va & ~PUD_MASK);
        return true;
    }

    pmd = pmd_offset(pud, va);
    if (pmd_none(*pmd) || pmd_bad(*pmd)) return false;
    if (pmd_sect(*pmd)) {
        *out = (phys_addr_t)(pmd_val(*pmd) & PMD_MASK) | (va & ~PMD_MASK);
        return true;
    }

    pte = pte_offset_kernel(pmd, va);
    if (!pte || pte_none(*pte) || !pte_present(*pte)) return false;

    *out = (phys_addr_t)(pte_val(*pte) & PAGE_MASK) | (va & ~PAGE_MASK);
    return true;
}

/* 补缺页：调用者须已持有 mm->mmap_sem 读锁 */
static int fault_in_page(struct mm_struct *mm, unsigned long va, bool write)
{
    struct vm_area_struct *vma;
    vm_fault_t fret;
    unsigned int flags = FAULT_FLAG_REMOTE;

    if (!_find_vma || !_handle_mm_fault) return -EFAULT;

    vma = _find_vma(mm, va);
    if (!vma || va < vma->vm_start) return -EFAULT;

    if (write) {
        if (!(vma->vm_flags & VM_WRITE)) return -EPERM;
        flags |= FAULT_FLAG_WRITE;
    } else {
        if (!(vma->vm_flags & (VM_READ | VM_EXEC))) return -EPERM;
    }

    fret = _handle_mm_fault(vma, va, flags, NULL);
    if (fret & VM_FAULT_ERROR) return -EFAULT;
    return 0;
}

static int phys_read_chunk(phys_addr_t pa, void *dst, size_t len)
{
    unsigned long pfn = (unsigned long)(pa >> PAGE_SHIFT);

    if (pfn_valid(pfn)) {
        memcpy(dst, __va(pa), len);
    } else {
        void __iomem *m = ioremap_cache(pa & PAGE_MASK, PAGE_SIZE);
        size_t off = pa & ~PAGE_MASK;
        if (!m) return -ENOMEM;
        memcpy(dst, (char *)m + off, len);
        iounmap(m);
    }
    return 0;
}

static int phys_write_chunk(phys_addr_t pa, const void *src, size_t len)
{
    unsigned long pfn = (unsigned long)(pa >> PAGE_SHIFT);

    if (pfn_valid(pfn)) {
        void *dst = __va(pa);
        memcpy(dst, src, len);
        if (_flush_dcache) _flush_dcache(dst, len);
    } else {
        void __iomem *m = ioremap_cache(pa & PAGE_MASK, PAGE_SIZE);
        size_t off = pa & ~PAGE_MASK;
        if (!m) return -ENOMEM;
        memcpy((char *)m + off, src, len);
        iounmap(m);
    }
    return 0;
}

static int phys_read(struct mm_struct *mm, unsigned long va, void *dst, size_t size)
{
    size_t done = 0;
    int ret = 0;

    down_read(&mm->mmap_sem);
    while (done < size) {
        unsigned long cur = va + done;
        size_t page_off = cur & ~PAGE_MASK;
        size_t chunk = PAGE_SIZE - page_off;
        phys_addr_t pa;

        if (chunk > size - done) chunk = size - done;

        if (!translate_linear_address(mm, cur, &pa)) {
            if (fault_in_page(mm, cur, false) ||
                !translate_linear_address(mm, cur, &pa)) {
                ret = -EFAULT;
                break;
            }
        }

        ret = phys_read_chunk(pa, (char *)dst + done, chunk);
        if (ret) break;
        done += chunk;
    }
    up_read(&mm->mmap_sem);
    return ret;
}

static int phys_write(struct mm_struct *mm, unsigned long va, const void *src, size_t size)
{
    size_t done = 0;
    int ret = 0;

    down_read(&mm->mmap_sem);
    while (done < size) {
        unsigned long cur = va + done;
        size_t page_off = cur & ~PAGE_MASK;
        size_t chunk = PAGE_SIZE - page_off;
        phys_addr_t pa;

        if (chunk > size - done) chunk = size - done;

        if (!translate_linear_address(mm, cur, &pa)) {
            if (fault_in_page(mm, cur, true) ||
                !translate_linear_address(mm, cur, &pa)) {
                ret = -EFAULT;
                break;
            }
        }

        ret = phys_write_chunk(pa, (const char *)src + done, chunk);
        if (ret) break;
        done += chunk;
    }
    up_read(&mm->mmap_sem);
    return ret;
}

static struct mm_struct *get_mm_by_pid(pid_t pid)
{
    struct pid *pid_struct;
    struct task_struct *task;
    struct mm_struct *mm;

    pid_struct = _find_get_pid(pid);
    if (!pid_struct) return NULL;
    task = _get_pid_task(pid_struct, PIDTYPE_PID);
    _put_pid(pid_struct);
    if (!task) return NULL;

    mm = _get_task_mm(task);
    _put_task_struct(task);
    return mm;
}

static int do_read_mem(pid_t pid, unsigned long addr, void *kbuf, size_t size)
{
    struct mm_struct *mm;
    int ret;

    mm = get_mm_by_pid(pid);
    if (!mm) return -ESRCH;

    ret = phys_read(mm, addr, kbuf, size);
    _mmput(mm);
    return ret;
}

static int do_write_mem(pid_t pid, unsigned long addr, void *kbuf, size_t size)
{
    struct mm_struct *mm;
    int ret;

    mm = get_mm_by_pid(pid);
    if (!mm) return -ESRCH;

    ret = phys_write(mm, addr, kbuf, size);
    _mmput(mm);
    return ret;
}

/* ================= 硬件断点 ================= */

#define MAX_BP_COUNT 4

struct hw_bp_info {
    int used;
    pid_t pid;
    unsigned long addr;
    struct perf_event *bp;
    long delta;
    int reg_idx;
};

static struct hw_bp_info g_bps[MAX_BP_COUNT];
static DEFINE_MUTEX(bp_mutex);

static CFI_SAFE void hw_bp_triggered(struct perf_event *bp,
                                     struct perf_sample_data *data,
                                     struct pt_regs *regs)
{
    struct hw_bp_info *info = bp->overflow_handler_context;
    int idx;

    if (!info || !regs) return;

    idx = (int)(info - g_bps);
    if (idx < 0 || idx >= MAX_BP_COUNT) return;

    if (info->reg_idx >= 0 && info->reg_idx <= 30 && info->delta)
        regs->regs[info->reg_idx] += info->delta;

    LOG("hit id=%d pid=%d pc=%llx reg[%d]=%lx delta=%ld\n",
        idx, current->pid,
        (unsigned long long)regs->pc,
        info->reg_idx,
        (unsigned long)regs->regs[info->reg_idx],
        info->delta);
}

static int do_register_bp(pid_t pid, unsigned long addr, int type, int len,
                          int delta, int reg_idx)
{
    struct task_struct *task = NULL;
    struct perf_event_attr attr;
    struct perf_event *bp_event;
    int i, ret = -1;

    if (!(type & (HW_BREAKPOINT_R | HW_BREAKPOINT_W | HW_BREAKPOINT_X)))
        return -EINVAL;
    if (reg_idx < 0 || reg_idx > 30)
        return -EINVAL;

    if (type & HW_BREAKPOINT_X) {
        len = HW_BREAKPOINT_LEN_4;
    } else {
        switch (len) {
        case HW_BREAKPOINT_LEN_1:
        case HW_BREAKPOINT_LEN_2:
        case HW_BREAKPOINT_LEN_4:
        case HW_BREAKPOINT_LEN_8:
            break;
        default:
            return -EINVAL;
        }
    }

    if (addr & (len - 1))
        return -EINVAL;

    mutex_lock(&bp_mutex);
    for (i = 0; i < MAX_BP_COUNT; i++)
        if (!g_bps[i].used) break;
    if (i == MAX_BP_COUNT) { mutex_unlock(&bp_mutex); return -ENOSPC; }

    {
        struct pid *pid_struct;
        pid_struct = _find_get_pid(pid);
        if (!pid_struct) { mutex_unlock(&bp_mutex); return -ESRCH; }
        task = _get_pid_task(pid_struct, PIDTYPE_PID);
        _put_pid(pid_struct);
        if (!task) { mutex_unlock(&bp_mutex); return -ESRCH; }
    }

    g_bps[i].used = 1;
    g_bps[i].pid = pid;
    g_bps[i].addr = addr;
    g_bps[i].bp = NULL;
    g_bps[i].delta = delta;
    g_bps[i].reg_idx = reg_idx;

    memset(&attr, 0, sizeof(attr));
    attr.type = PERF_TYPE_BREAKPOINT;
    attr.size = sizeof(attr);
    attr.bp_addr = addr;
    attr.bp_type = type;
    attr.bp_len = len;
    attr.sample_period = 1;
    attr.disabled = 0;
    attr.exclude_kernel = 1;
    attr.exclude_hv = 1;
    attr.exclude_idle = 1;

    bp_event = _perf_create_kcounter(&attr, -1, task, hw_bp_triggered, &g_bps[i]);
    _put_task_struct(task);

    if (IS_ERR(bp_event)) {
        WRITE_ONCE(g_bps[i].delta, 0);
        WRITE_ONCE(g_bps[i].reg_idx, 0);
        smp_store_release(&g_bps[i].used, 0);
        mutex_unlock(&bp_mutex);
        return PTR_ERR(bp_event);
    }

    WRITE_ONCE(g_bps[i].bp, bp_event);
    ret = i;
    mutex_unlock(&bp_mutex);
    return ret;
}

static int do_unregister_bp(int id)
{
    struct perf_event *bp = NULL;

    if (id < 0 || id >= MAX_BP_COUNT) return -EINVAL;

    mutex_lock(&bp_mutex);
    if (smp_load_acquire(&g_bps[id].used)) {
        WRITE_ONCE(g_bps[id].delta, 0);
        WRITE_ONCE(g_bps[id].reg_idx, 0);
        bp = READ_ONCE(g_bps[id].bp);
        WRITE_ONCE(g_bps[id].bp, NULL);
        smp_store_release(&g_bps[id].used, 0);
    }
    mutex_unlock(&bp_mutex);

    if (bp) _perf_release_kernel(bp);
    return 0;
}

/* ================= IOCTL ================= */

static long dispatch_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
    struct ioctl_req req;
    void *kbuf = NULL;
    int ret = 0;

    if (copy_from_user(&req, (void __user *)arg, sizeof(req))) return -EFAULT;

    switch (cmd) {
    case CMD_READ_MEM:
    case CMD_WRITE_MEM:
        if (!req.size || req.size > MAX_XFER) return -EINVAL;

        kbuf = kvzalloc(req.size, GFP_KERNEL);
        if (!kbuf) return -ENOMEM;

        if (cmd == CMD_READ_MEM) {
            ret = do_read_mem(req.pid, req.addr, kbuf, req.size);
            if (ret == 0 && copy_to_user((void __user *)req.buf, kbuf, req.size))
                ret = -EFAULT;
        } else {
            if (copy_from_user(kbuf, (void __user *)req.buf, req.size)) {
                ret = -EFAULT;
            } else {
                ret = do_write_mem(req.pid, req.addr, kbuf, req.size);
            }
        }
        kvfree(kbuf);
        break;

    case CMD_SET_BP:
        ret = do_register_bp(req.pid, req.addr, req.type, req.len,
                             req.delta, req.reg_idx);
        if (ret >= 0) {
            req.bp_id = ret;
            ret = copy_to_user((void __user *)arg, &req, sizeof(req)) ? -EFAULT : 0;
        }
        break;

    case CMD_DEL_BP:
        ret = do_unregister_bp(req.bp_id);
        break;

    default:
        ret = -EINVAL;
    }

    return ret;
}

static int dispatch_open(struct inode *inode, struct file *file) { return 0; }
static int dispatch_close(struct inode *inode, struct file *file) { return 0; }

static const struct file_operations hack_fops = {
    .owner = THIS_MODULE,
    .open = dispatch_open,
    .release = dispatch_close,
    .unlocked_ioctl = dispatch_ioctl,
};

static struct miscdevice hack_misc = {
    .minor = MISC_DYNAMIC_MINOR,
    .name = DEVICE_NAME,
    .fops = &hack_fops,
};

/* ================= init / exit ================= */

static int __init hack_init(void)
{
    int ret;
    unsigned long addr;

    pr_info("[hack_bp] init\n");

    ret = register_kprobe(&kln_kp);
    if (ret < 0) return ret;
    addr = (unsigned long)kln_kp.addr;
    unregister_kprobe(&kln_kp);
    real_kln = (kallsyms_lookup_name_t)addr;
    if (!real_kln) return -ENOENT;

    _perf_create_kcounter = (pe_create_kcounter_t)kln("perf_event_create_kernel_counter");
    _perf_release_kernel  = (pe_release_kernel_t)kln("perf_event_release_kernel");

    _find_get_pid    = (find_get_pid_t)kln("find_get_pid");
    _get_pid_task    = (get_pid_task_t)kln("get_pid_task");
    _put_pid         = (put_pid_t)kln("put_pid");
    _put_task_struct = (put_task_struct_t)kln("put_task_struct");
    _get_task_mm     = (get_task_mm_t)kln("get_task_mm");
    _mmput           = (mmput_t)kln("mmput");

    _find_vma        = (find_vma_t)kln("find_vma");
    _handle_mm_fault = (handle_mm_fault_t)kln("handle_mm_fault");

    _flush_dcache    = (flush_dcache_t)kln("__flush_dcache_area");
    if (!_flush_dcache)
        _flush_dcache = (flush_dcache_t)kln("dcache_clean_inval_poc");

    _printk_deferred = (printk_deferred_t)kln("printk_deferred");

    if (!_perf_create_kcounter || !_perf_release_kernel ||
        !_find_get_pid || !_get_pid_task || !_put_pid ||
        !_put_task_struct || !_get_task_mm || !_mmput ||
        !_find_vma || !_handle_mm_fault) {
        pr_err("[hack_bp] symbol resolve failed: create=%px release=%px vma=%px fault=%px\n",
               _perf_create_kcounter, _perf_release_kernel,
               _find_vma, _handle_mm_fault);
        return -ENOENT;
    }

    if (!_flush_dcache)
        pr_warn("[hack_bp] no dcache flush symbol, write may be stale\n");
    if (!_printk_deferred)
        pr_warn("[hack_bp] no printk_deferred, use pr_info\n");

    ret = misc_register(&hack_misc);
    if (ret) return ret;

    pr_info("[hack_bp] loaded /dev/%s\n", DEVICE_NAME);
    return 0;
}

static void __exit hack_exit(void)
{
    int i;
    for (i = 0; i < MAX_BP_COUNT; i++)
        do_unregister_bp(i);
    misc_deregister(&hack_misc);
    pr_info("[hack_bp] unloaded\n");
}

module_init(hack_init);
module_exit(hack_exit);
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("hw bp + phys rw mem");
