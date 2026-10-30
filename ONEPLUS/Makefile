obj-m += hack_bp.o

KDIR ?= /tmp/kernel
PWD  := $(shell pwd)

ccflags-y += -Wno-error

all:
	$(MAKE) -C $(KDIR) M=$(PWD) O=$(KDIR)/out ARCH=arm64 \
		CC=clang LD=ld.lld AR=llvm-ar NM=llvm-nm \
		OBJCOPY=llvm-objcopy OBJDUMP=llvm-objdump STRIP=llvm-strip \
		CLANG_TRIPLE=aarch64-linux-gnu- CROSS_COMPILE=aarch64-linux-gnu- \
		LOCALVERSION=$(LOCALVERSION) modules

clean:
	$(MAKE) -C $(KDIR) M=$(PWD) O=$(KDIR)/out clean

.PHONY: all clean
