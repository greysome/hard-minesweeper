CC := gcc
CFLAGS := -std=c23 -D_XOPEN_SOURCE=500 -lm -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wdouble-promotion -Wno-sign-conversion

ifdef RELEASE
	BUILD := release
	CFLAGS += -O3 -march=native
else
	BUILD := debug
	CFLAGS += -g -fsanitize=address -fsanitize=undefined
endif

all: crocodile/test/crocodile_static genboard

genboard: genboard.c
	gcc ${CFLAGS} -o $@ $^

crocodile/test/crocodile_static: crocodile/crocodile.h
	gcc -DCROCODILE_TEST_HARNESS -xc ${CFLAGS} -o $@ $^

clean:
	rm -f genboard crocodile/test/crocodile_static