all:
	agda --compile --ghc-dont-call-ghc -i /usr/share/agda-stdlib/ streams.agda
	ghc                                                               \
            -package text -package ghc                           	  \
            MAlonzo/Code/Qstreams.hs                                  \
            -main-is MAlonzo.Code.Qheterostage                        \
            -fwarn-incomplete-patterns -fno-warn-overlapping-patterns \
            -XGADTs                                                   \
            -o streams

clean:
	rm -fr MAlonzo
	rm -f streams.agdai
