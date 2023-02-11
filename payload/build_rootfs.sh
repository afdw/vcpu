#/usr/bin/bash

source common.sh

(
    cd rootfs
    echo "Creating rootfs"
    rm -f rootfs.ext2
    truncate -s 128M rootfs.ext2
    mkfs.ext2 rootfs.ext2
    mkdir -p mnt
    sudo mount rootfs.ext2 mnt
    sudo chown $USER: mnt
    cp -a src/. mnt/
    cp -a ../busybox/install/. mnt/
    cp -a ../calc/install/. mnt/
    sudo umount mnt
)
