STDLIB=/usr/share/agda-stdlib/
AGDA_C=agda --compile --ghc-dont-call-ghc -i $(STDLIB)
GHC=ghc -O2 -optc-O3
AGDA_GHC_PKGS=-package text -package ghc
AGDA_GHC_FLAGS=-fwarn-incomplete-patterns -fno-warn-overlapping-patterns -XGADTs

.PHONY: all test clean

all:

test:

clean:
