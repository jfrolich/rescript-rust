SHELL = /bin/bash

build:
	yarn build

# In-process builds write no .cmt files: analysis reads them from a watcher.
test: build
	../with-watcher.sh bash ./test.sh

clean:
	yarn clean

.DEFAULT_GOAL := test

.PHONY: clean test
