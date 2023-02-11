#/usr/bin/bash

source common.sh

(
    cd busybox
    if [ ! -f .config ]
    then
        echo "Creating an initial BusyBox config"
        make ARCH=riscv vcpu_defconfig
    fi
    echo "Building BusyBox"
    make \
        -j$JOBS \
        CC="$RISCV_CC_FLAT" \
        SKIP_STRIP=y \
        CONFIG_PREFIX="$MY_PATH/busybox/install" \
        install
)
