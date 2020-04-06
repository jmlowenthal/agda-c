STDLIB=/usr/share/agda-stdlib/
AGDA_C=agda --compile --ghc-dont-call-ghc -i $(STDLIB)
GHC=ghc
GHC_PKGS=-package text -package ghc -O2
GHC_FLAGS=-fwarn-incomplete-patterns -fno-warn-overlapping-patterns -XGADTs
CC=clang -Wl,-z,stack-size=0x40000000 # 1GB stack
# Sudo is required here to ensure CAP_SYS_ADMIN permissions
PERF=sudo perf stat -r 100 --

all: test main.o

main.agda.o: *.agda **/*.agda
	$(AGDA_C) Main.agda
	$(GHC) $(GHC_PKGS) $(GHC_FLAGS) \
		MAlonzo/Code/Main.hs \
		-main-is MAlonzo.Code.Main \
		-o main.agda.o

main.c: main.agda.o
	./main.agda.o > main.c

main.o: main.c
	$(CC) main.c -o main.o

test.agda.o: *.agda **/*.agda
	$(AGDA_C) Test.agda
	$(GHC) $(GHC_PKGS) $(GHC_FLAGS) \
		MAlonzo/Code/Test.hs \
		-main-is MAlonzo.Code.Test \
		-o test.agda.o

test.c: test.agda.o
	./test.agda.o > test.c

test.o: test.c
	$(CC) test.c -o test.o

test: test.o
	./test.o

benchmark.agda.o: *.agda **/*.agda
	$(AGDA_C) Benchmark.agda
	$(GHC) $(GHC_PKGS) $(GHC_FLAGS) \
		MAlonzo/Code/Benchmark.hs \
		-main-is MAlonzo.Code.Benchmark \
		-o benchmark.agda.o

benchmarks.c: benchmark.agda.o
	./benchmark.agda.o > benchmarks.c

benchmark-%.o: benchmarks.c
	$(CC) -DBENCHMARK_$* benchmarks.c -o benchmark-$*.o

benchmark-%: benchmark-%.o
	$(PERF) ./benchmark-$*.o

benchmark.deps: benchmarks.c
	grep -e "#if BENCHMARK_[a-z_\-]*" benchmarks.c \
		| { echo "depends:"; sed -r "s/.{14}/benchmark-/"; } \
		| { tr '\n' ' '; echo ""; } \
		| tee benchmark.deps

include benchmark.deps

benchmark: depends

clean:
	rm -r MAlonzo *.agdai **/*.agdai *.c *.o *.deps
