.PHONY: build tyche test

build:
	lake build

tyche:
	lake build tyche-viz
	.lake/build/bin/tyche-viz

test:
	lake test
