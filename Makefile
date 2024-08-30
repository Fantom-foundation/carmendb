# --------------------------------------------------------------------------
# Makefile for Carmen
#
# v1.0 (2023/09/05) - Initial version
#
# (c) Fantom Foundation, 2023
# --------------------------------------------------------------------------

.PHONY: all clean

.PHONY: all
all: main

GOPROXY ?= "https://proxy.golang.org,direct"
.PHONY: main
main:
	GIT_COMMIT=`git rev-list -1 HEAD 2>/dev/null || echo ""` && \
	GIT_DATE=`git log -1 --date=short --pretty=format:%ct 2>/dev/null || echo ""` && \
	GOPROXY=$(GOPROXY) \
	go build \
	    -ldflags "-s -w -X github.com/Fantom-foundation/carmendb/launcher.gitCommit=$${GIT_COMMIT} -X github.com/Fantom-foundation/camendb/launcher.gitDate=$${GIT_DATE}" \
	    -o build/carmen \
	    .

.PHONY: build
build:
	go build -v ./...

.PHONY: test
test:
	go test ./... -parallel 1 -timeout 60m

.PHONY: stress-test
stress-test:
	go run ./database/mpt/tool stress-test --num-blocks 2000

.PHONY: clean
clean:
	rm -fr ./build/*

