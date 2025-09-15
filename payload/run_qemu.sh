#/usr/bin/bash

source common.sh

qemu-system-riscv64 \
    -m 64 \
    -machine virt \
    -nographic \
    -bios linux/arch/riscv/boot/Image \
    -drive file=rootfs/rootfs.ext2,if=none,format=raw,id=hd0 \
    -device virtio-blk-device,drive=hd0
