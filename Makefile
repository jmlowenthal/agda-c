all:
	agda --compile --ghc-dont-call-ghc -i /usr/share/agda-stdlib/ Main.agda
	ghc                                                               \
            -package text -package ghc                           	  \
            MAlonzo/Code/Main.hs                                      \
            -main-is MAlonzo.Code.Main                                \
            -fwarn-incomplete-patterns -fno-warn-overlapping-patterns \
            -XGADTs                                                   \
            -o main

clean:
	rm -fr MAlonzo
	rm -f *.agdai
