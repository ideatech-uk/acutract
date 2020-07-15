PWD=$(CURDIR)
PREFIX="$(PWD)/.stack-work/prefix"

all: setup build

setup:
	stack build --only-dependencies

build-libff:
	./scripts/build-libff.sh

build-z3:
	mkdir -p $(PREFIX)
	cd z3 && test -f build/Makefile || python scripts/mk_make.py -p $(PREFIX)
	cd z3/build && make -j $(shell nproc)
	cd z3/build && make install

build:
	stack build --copy-bins --fast

build-watch:
	stack build --copy-bins --fast --file-watch

build-opt: clean
	stack build --copy-bins --ghc-options "-O3 -fllvm"

build-format:
	stack install ormolu

lint:
	stack exec -- hlint app src test

format:
	find . -path ./.stack-work -prune -o -path ./archived -prune -o -type f -name "*.hs" -exec ormolu --mode inplace {} --ghc-opt -XTypeApplications --ghc-opt -XUnicodeSyntax --ghc-opt -XPatternSynonyms --ghc-opt -XTemplateHaskell \;

test:
	stack test --fast --jobs=1 --test-arguments "--hide-successes --ansi-tricks false"

bench:
	stack bench --benchmark-arguments="--output ./doc/Code/bench.html"


repl-lib:
	stack ghci juvix:lib

repl-exe:
	stack ghci juvix:exe:juvix

clean:
	stack clean

clean-full:
	stack clean --full

.PHONY: all setup build build-libff build-z3 build-watch build-opt lint format test repl-lib repl-exe clean clean-full bench build-format
