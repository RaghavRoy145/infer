Linux Kernel NPE Bug - Manual Setup Required

Bug ID: null-ptr-9-linux-kernel-5
File: tools/lib/subcmd/help.c
NPE Lines: 18 -> 20

To setup manually:
1. Clone Linux kernel:
   git clone --depth 1 https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git src
   cd src
   git checkout 5b78ed24e8ec48602c1d6f5a188e58d000c81e2b

2. Configure:
   make CC=clang defconfig

3. Build:
   make CC=clang -j32

The NPE bug is in: tools/lib/subcmd/help.c
