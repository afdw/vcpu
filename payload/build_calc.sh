#/usr/bin/bash

source common.sh

(
    cd calc
    echo "Building calc"
    make \
        CC="$RISCV_CC_FLAT" \
        BLD_TYPE=calc-static-only \
        USE_READLINE= \
        READLINE_LIB= \
        READLINE_EXTRAS= \
        DEBUG="-g -O1" \
        CHMOD=true \
        RPM_TOP=1 \
        T="$MY_PATH/calc/install" \
        install
)
