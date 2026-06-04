.PHONY: build tyche test

build:
	lake build

tyche:
	lake build tyche-viz
	.lake/build/bin/tyche-viz

test:
	lake build test-lexpr
	.lake/build/bin/test-lexpr
