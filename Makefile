STDLIB=/usr/share/agda-stdlib/
AGDA_C=agda --compile --ghc-dont-call-ghc -i $(STDLIB)
GHC=ghc
GHC_PKGS=-package text -package ghc
GHC_FLAGS=-fwarn-incomplete-patterns -fno-warn-overlapping-patterns -XGADTs
CC=clang

all: test main.o

main.agda.o: *.agda
	$(AGDA_C) Main.agda
	$(GHC) $(GHC_PKGS) $(GHC_FLAGS) \
		MAlonzo/Code/Main.hs \
		-main-is MAlonzo.Code.Main \
		-o main.agda.o

main.c: main.agda.o
	./main.agda.o > main.c

main.o: main.c
	$(CC) main.c -o main.o

test.agda.o : *.agda
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

clean:
	rm -r MAlonzo
	rm *.agdai
	rm *.c
	rm *.o
