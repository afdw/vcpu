#/usr/bin/bash

source common.sh

(
    cd linux
    if [ ! -f .config ]
    then
        echo "Creating an initial kernel config"
        make ARCH=riscv vcpu_defconfig
    fi
    echo "Building the kernel"
    make \
        -j$JOBS \
        ARCH=riscv \
        CC="$RISCV_CC" \
        LD="$RISCV_LD" \
        OBJCOPY="$RISCV_OBJCOPY" \
        LD_LIBS="$RISCV_GNU_TOOLCHAIN_INSTALL_DIR/lib/gcc/riscv64-unknown-linux-gnu/12.2.0/libgcc.a" \
        loader
)
