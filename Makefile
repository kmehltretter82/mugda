# Makefile for Mugda (Constructive Lean 4 Edition)

LAKE ?= lake
MUGDA := .lake/build/bin/mugda

.PHONY: all build test clean

all: build

build:
	$(LAKE) build

test: build
	$(MUGDA) examples/fib.ma
	$(MUGDA) examples/sqsort.ma
	$(MUGDA) examples/slist.ma
	$(MUGDA) examples/sp.ma
	$(MUGDA) examples/stree.ma
	$(MUGDA) examples/sord.ma

clean:
	$(LAKE) clean
