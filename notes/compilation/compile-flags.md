# OpenSBI specific
* `FW_TEXT_START`
    * address at which RAM starts (sadly this is never stated directly in OpenSBI => no source :()
* `FW_PAYLOAD_OFFSET`
    * needs to be 2MB aligned for 64-bit systems
        * this is necessary since 64-bit kernels have to be 2MB aligned
            * it seems that this guy is talking about Linux which apparantly requires this alignment because it maps the entire RAM using hugepages (which are 2MB on 64-bit systems)
                * TODO: test/research if this is something that is really necessary (i.e. if it is needed even when not using Linux as a payload) or if it just a "hint"
* `FW_PAYLOAD_ALIGN`



# Sources
* https://github.com/riscv/opensbi/commit/a5f06b30c1503ecd09691f1ad9909287489228f5
* https://patchwork.kernel.org/patch/10868465/
