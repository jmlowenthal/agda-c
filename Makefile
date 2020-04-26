STDLIB=/usr/share/agda-stdlib/
AGDA_C=agda --compile --ghc-dont-call-ghc -i $(STDLIB)
GHC=ghc -O2 -optc-O3
AGDA_GHC_PKGS=-package text -package ghc
AGDA_GHC_FLAGS=-fwarn-incomplete-patterns -fno-warn-overlapping-patterns -XGADTs
CC=clang -O3
N=50

.PHONY: all test benchmark benchmark-% clean depends-benchmark

all: test main.o

main.agda.o: src/*.agda src/**/*.agda
	cd src/ && $(AGDA_C) --compile-dir=.. Main.agda
	$(GHC) $(AGDA_GHC_PKGS) $(AGDA_GHC_FLAGS) \
		MAlonzo/Code/Main.hs \
		-main-is MAlonzo.Code.Main \
		-o main.agda.o

main.c: main.agda.o
	./main.agda.o > main.c

main.o: main.c
	$(CC) main.c -o main.o

test.agda.o: src/*.agda src/**/*.agda
	cd src/ && $(AGDA_C) --compile-dir=.. Test.agda
	$(GHC) $(AGDA_GHC_PKGS) $(AGDA_GHC_FLAGS) \
		MAlonzo/Code/Test.hs \
		-main-is MAlonzo.Code.Test \
		-o test.agda.o

test.c: test.agda.o
	./test.agda.o > test.c

test.o: test.c
	$(CC) test.c -o test.o

test: test.o
	./test.o

benchmark.agda.o: src/*.agda src/**/*.agda
	cd src/ && $(AGDA_C) --compile-dir=.. Benchmark.agda
	$(GHC) $(AGDA_GHC_PKGS) $(AGDA_GHC_FLAGS) \
		MAlonzo/Code/Benchmark.hs \
		-main-is MAlonzo.Code.Benchmark \
		-o benchmark.agda.o

benchmark.c: benchmark.agda.o
	./benchmark.agda.o > benchmark.c

benchmark-staged-%.o: benchmark.c
	$(CC) -DBENCHMARK_$* benchmark.c -o benchmark-staged-$*.o

benchmark-byhand-%.o: src/Benchmark.c
	$(CC) -DBENCHMARK_$* src/Benchmark.c -o benchmark-byhand-$*.o

benchmark-haskell-%.o: src/Benchmark.hs
	$(GHC) -DEXTERNAL_PACKAGE -DBENCHMARK_$* -ilib/stream-fusion-0.1.2.5 \
		src/Benchmark.hs -o benchmark-haskell-$*.o

benchmark-%.csv: benchmark-%.o
#	Sudo required to ensure CAP_SYS_ADMIN permissions
	sudo perf stat -r $(N) -x , \
		-o benchmark-$*.csv -- ./benchmark-$*.o > /dev/null

benchmark-%.log: benchmark-%.o
	./benchmark-$*.o > benchmark-$*.log

test-benchmark-%: benchmark-staged-%.log benchmark-haskell-%.log benchmark-byhand-%.log
	diff -q --from-file=benchmark-byhand-$*.log \
		benchmark-staged-$*.log benchmark-haskell-$*.log

benchmark-staged.deps: benchmark.c
	grep -e "^#if BENCHMARK_[a-z_\-]*" benchmark.c \
		| { echo "depends-benchmark-staged:" \
		  ; sed -r "s/^.{14}(.*)/benchmark-staged-\1.csv/" ; } \
		| { tr "\n" " " ; echo ; } \
		| tee benchmark-staged.deps

benchmark-haskell.deps: src/Benchmark.hs
	grep -e "^#if BENCHMARK_[a-z_\-]*" src/Benchmark.hs \
		| { echo "depends-benchmark-haskell:" \
		  ; sed -r "s/^.{14}(.*)/benchmark-haskell-\1.csv/" ; } \
		| { tr "\n" " " ; echo ; } \
		| tee benchmark-haskell.deps

benchmark-byhand.deps: src/Benchmark.c
	grep -e "^#if BENCHMARK_[a-z_\-]*" src/Benchmark.c \
		| { echo "depends-benchmark-byhand:" \
		  ; sed -r "s/^.{14}(.*)/benchmark-byhand-\1.csv/" ; } \
		| { tr "\n" " " ; echo ; } \
		| tee benchmark-byhand.deps

benchmark-test.deps: benchmark-staged.deps benchmark-haskell.deps benchmark-byhand.deps
	cat benchmark-staged.deps benchmark-haskell.deps benchmark-byhand.deps \
		| sed -r "s/^[^:]*:\s//; s/benchmark-[a-z]*-([a-zA-Z\-_]*)\.csv\s/\1\n/g" \
		| sort \
		| uniq -c \
		| grep -e "^\s*3\s..*" \
		| { echo "depends-benchmark-test:" \
		  ; sed -r "s/^\s*3\s*(.*)/test-benchmark-\1/" ; } \
		| tr "\n" " " \
		| tee benchmark-test.deps

ifneq (,$(filter benchmark benchmark.csv test-benchmark,$(MAKECMDGOALS)))
  include benchmark-staged.deps
  include benchmark-haskell.deps
  include benchmark-byhand.deps
  include benchmark-test.deps
endif

benchmark.csv: depends-benchmark-staged depends-benchmark-haskell depends-benchmark-byhand
	@grep ^ /dev/null *.csv \
		| grep "^benchmark-.*.csv" \
		| grep "task-clock" \
		| sed -r "s/^benchmark-(.*)-(.*)\.csv:(.*),task-clock.*,([0-9\.]*%).*/\2,\1,\3,\3/" \
		| tee benchmark.csv > /dev/null

benchmark: benchmark.csv
	@{ echo "BENCHMARK,TEST SET,TIME, ,VAR" ; cat benchmark.csv | sort ; } | column -ts,

test-benchmark: depends-benchmark-test

clean:
	rm -rf MAlonzo *.agdai **/*.agdai *.c *.o *.deps *.csv *.log
