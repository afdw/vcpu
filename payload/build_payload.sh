#/usr/bin/bash

source common.sh

./build_linux.sh
./build_busybox.sh
./build_calc.sh
./build_rootfs.sh
