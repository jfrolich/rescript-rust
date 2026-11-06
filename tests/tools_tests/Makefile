SHELL = /bin/bash

build:
	yarn build

# In-process builds write no .cmt files: the doc command reads them from a watcher.
test: build
	../analysis_tests/with-watcher.sh bash ./test.sh
	yarn build

clean:
	yarn clean

.DEFAULT_GOAL := test

.PHONY: clean test
