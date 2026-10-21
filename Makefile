.PHONY: build test audit demo lowering-demo check

build:
	lake build --wfail

test: build
	python3 -m unittest discover -s tests -v

audit: build
	python3 -m experiments.audit

demo: build
	python3 -m experiments.demo
	python3 -m experiments.lowering

lowering-demo: build
	python3 -m experiments.lowering

check: test audit demo
