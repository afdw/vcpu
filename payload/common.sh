#/usr/bin/bash

MY_PATH="$(dirname -- "${BASH_SOURCE[0]}")"
MY_PATH="$(cd -- "$MY_PATH" && pwd)"

cd $MY_PATH

: ${RISCV_GNU_TOOLCHAIN_INSTALL_DIR="$MY_PATH/../../riscv-gnu-toolchain/install"}

RISCV_CC="$RISCV_GNU_TOOLCHAIN_INSTALL_DIR/bin/riscv64-unknown-linux-gnu-gcc-flat"
RISCV_CC_FLAT="$RISCV_GNU_TOOLCHAIN_INSTALL_DIR/bin/riscv64-unknown-linux-gnu-gcc-flat"
RISCV_LD="$RISCV_GNU_TOOLCHAIN_INSTALL_DIR/bin/riscv64-unknown-linux-gnu-ld"
RISCV_OBJCOPY="$RISCV_GNU_TOOLCHAIN_INSTALL_DIR/bin/riscv64-unknown-linux-gnu-objcopy"

: ${JOBS=16}
