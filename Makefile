.PHONY: build tyche test

build:
	lake build

# The merged driver generates Tyche visualizations by default, so `make tyche`
# just runs it; `make test` skips the visualization pass for a faster test-only run.
tyche:
	lake build test
	.lake/build/bin/test

test:
	lake test -- --no-tyche
