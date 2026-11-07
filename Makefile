GHC ?= ghc

all : Main

Main : Tokens.hs Lexer.hs Parser.hs Abstract.hs Concrete.hs SPos.hs ScopeChecker.hs TraceError.hs TypeChecker.hs Value.hs Termination.hs Completness.hs Main.hs
	$(GHC) --make Main.hs -o Main

# Optional regeneration with Alex and Happy if installed
lexer-parser : Lexer.x Parser.y
	alex Lexer.x
	happy Parser.y

clean :
	rm -f *.o *.hi Control/Monad/*.o Control/Monad/*.hi Main mugda
