STDLIB=/usr/share/agda-stdlib/
AGDA_C=agda --compile --ghc-dont-call-ghc -i $(STDLIB)
GHC=ghc
GHC_PKGS=-package text -package ghc -O2
GHC_FLAGS=-fwarn-incomplete-patterns -fno-warn-overlapping-patterns -XGADTs
CC=clang
N=10

.PHONY: all test benchmark benchmark-% clean

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

benchmarkslow-%.o: benchmarks.c
	$(CC) -DBENCHMARK_$* benchmarks.c -o benchmarkslow-$*.o

benchmark-%.o: benchmarks.c
	$(CC) -O3 -DBENCHMARK_$* benchmarks.c -o benchmark-$*.o

benchmarkslow-%.csv: benchmarkslow-%.o
#	Sudo required to ensure CAP_SYS_ADMIN permissions
	sudo perf stat -r $(N) -e task-clock -x , \
		-o benchmarkslow-$*.csv -- ./benchmarkslow-$*.o

benchmark-%.csv: benchmark-%.o
#	Sudo required to ensure CAP_SYS_ADMIN permissions
	sudo perf stat -r $(N) -e task-clock -x , \
		-o benchmark-$*.csv -- ./benchmark-$*.o

# Generates benchmark and benchmarkslow rules
benchmark.deps: benchmarks.c
	grep -e "#if BENCHMARK_[a-z_\-]*" benchmarks.c \
		| { echo "depends-benchmark:" ; sed -r "s/^.{14}(.*)/benchmark-\1.csv/" ; } \
		| { tr "\n" " " ; echo ; } \
		| tee benchmark.deps
	grep -e "#if BENCHMARK_[a-z_\-]*" benchmarks.c \
		| { echo "depends-benchmarkslow:" ;
		    sed -r "s/^.{14}(.*)/benchmarkslow-\1.csv/g" ; } \
		| tr "\n" " " \
		| tee -a benchmark.deps

include benchmark.deps

benchmark.csv: depends-benchmark
	grep ^ /dev/null *.csv \
		| grep "^benchmark-.*.csv" \
		| grep "task-clock" \
		| sed -r "s/^benchmark-(.*).csv:(.*),task-clock.*,([0-9\.]*%).*/\1,\2,\3/" \
		| tee benchmark.csv > /dev/null

benchmark: benchmark.csv
	{ echo "BENCHMARK,TIME, ,VAR" ; cat benchmark.csv ; } | column -ts,

clean:
	rm -r MAlonzo *.agdai **/*.agdai *.c *.o *.deps *.csv
