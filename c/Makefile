# Bare-metal RV64I build of libtommath (vendor/libtommath, v1.3.0) and its
# test driver (xPack GCC 15.2.0, newlib, -march=rv64i -mabi=lp64
# -mcmodel=medany -O2 -std=gnu11). The proof image c/tommath-arith.elf is
# build/MP_32BIT/arith.elf.
#
# DIGIT selects the libtommath digit size:
#   MP_32BIT (default): 28-bit digits in uint32_t, mp_word = uint64_t, so the
#     multiply/divide helpers are libgcc's __muldi3/__udivdi3/__umoddi3;
#   MP_64BIT: 60-bit digits, mp_word = unsigned __int128 (__multi3, __udivti3).
XPACK    ?= $(firstword $(wildcard $(HOME)/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin))
RISCV_CC ?= $(XPACK)/riscv-none-elf-gcc
RISCV_AR ?= $(XPACK)/riscv-none-elf-ar
DIGIT    ?= MP_32BIT
CFLAGS_RV := -std=gnu11 -O2 -Wall -Wno-unused-result -march=rv64i -mabi=lp64 -mcmodel=medany -D$(DIGIT)
CFLAGS_HOST := -std=gnu11 -O2 -Wall -Wno-unused-result -D$(DIGIT)

TOM  := ../vendor/libtommath
SRC  := $(wildcard $(TOM)/*.c)
B    := build/$(DIGIT)
OBJ  := $(patsubst $(TOM)/%.c,$(B)/rv/%.o,$(SRC))
HOBJ := $(patsubst $(TOM)/%.c,$(B)/host/%.o,$(SRC))
TESTS := $(basename $(notdir $(wildcard tests/*.c)))

all: $(B)/libtommath-rv64i.a $(addprefix $(B)/,$(addsuffix .elf,$(TESTS))) \
     $(addprefix $(B)/,$(addsuffix .host,$(TESTS)))

$(B)/rv/%.o: $(TOM)/%.c
	@mkdir -p $(dir $@)
	$(RISCV_CC) $(CFLAGS_RV) -I$(TOM) -c $< -o $@

$(B)/host/%.o: $(TOM)/%.c
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS_HOST) -I$(TOM) -c $< -o $@

$(B)/libtommath-rv64i.a: $(OBJ)
	rm -f $@; $(RISCV_AR) rcs $@ $^

$(B)/libtommath-host.a: $(HOBJ)
	rm -f $@; ar rcs $@ $^

$(B)/%.elf: tests/%.c harness/crt0.S harness/htif.c harness/link.ld $(B)/libtommath-rv64i.a
	$(RISCV_CC) $(CFLAGS_RV) -I$(TOM) -nostartfiles -T harness/link.ld -o $@ \
	    harness/crt0.S harness/htif.c $< $(B)/libtommath-rv64i.a -lc -lgcc -lc

$(B)/%.host: tests/%.c $(B)/libtommath-host.a
	$(CC) $(CFLAGS_HOST) -I$(TOM) -o $@ $< $(B)/libtommath-host.a

clean:
	rm -rf build

.PHONY: all clean
