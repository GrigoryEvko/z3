# Thin wrapper around CMake presets.
# Usage:
#   make                - configure + build with default preset
#   make preset=asan    - use asan preset
#   make test-z3        - build and run unit tests
#   make regressions    - run z3test regression suite

preset ?= default

builddir.default := build
builddir.asan    := build-asan
builddir.tsan    := build-tsan
BUILD_DIR        := $(builddir.$(preset))

.PHONY: all configure build clean test-z3 regressions nuke pgo

all: build

configure:
	@cmake --preset $(preset)

build: configure
	@cmake --build --preset $(preset)

test-z3: configure
	@cmake --build --preset $(preset) --target test-z3
	$(BUILD_DIR)/test-z3 -a

regressions: build
	python3 ../z3test/scripts/test_benchmarks.py $(BUILD_DIR)/z3 ../z3test/regressions/smt2

clean:
	@cmake --build --preset $(preset) --target clean

nuke:
	rm -rf build build-asan build-tsan build-pgo build-pgo-gen

# Profile-Guided Optimization build.
# Trains on the critical corpus, then builds an optimized binary at build-pgo/z3.
# Requires: blast.sh test harness at ../z3_testing/blast.sh
PGO_PROFDIR := /tmp/z3-pgo-data
PGO_COMMON  := -O2 -march=native
TRAINING_CORPUS ?= critical

pgo:
	@echo "=== PGO Step 1/3: Instrumented build ==="
	cmake -B build-pgo-gen -G Ninja \
	  -DCMAKE_BUILD_TYPE=Release \
	  -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang \
	  -DCMAKE_CXX_FLAGS="-fprofile-generate=$(PGO_PROFDIR) $(PGO_COMMON)" \
	  -DCMAKE_C_FLAGS="-fprofile-generate=$(PGO_PROFDIR) $(PGO_COMMON)" \
	  -DCMAKE_EXE_LINKER_FLAGS="-fprofile-generate=$(PGO_PROFDIR)"
	cmake --build build-pgo-gen -j$$(nproc)
	@echo "=== PGO Step 2/3: Training on $(TRAINING_CORPUS) corpus ==="
	rm -rf $(PGO_PROFDIR) && mkdir -p $(PGO_PROFDIR)
	bash ../z3_testing/blast.sh build-pgo-gen/z3 -c $(TRAINING_CORPUS) --fast -j 4
	llvm-profdata merge -output=$(PGO_PROFDIR)/merged.profdata $(PGO_PROFDIR)/*.profraw
	@echo "=== PGO Step 3/3: Optimized build ==="
	cmake -B build-pgo -G Ninja \
	  -DCMAKE_BUILD_TYPE=Release \
	  -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang \
	  -DCMAKE_CXX_FLAGS="-fprofile-use=$(PGO_PROFDIR)/merged.profdata $(PGO_COMMON)" \
	  -DCMAKE_C_FLAGS="-fprofile-use=$(PGO_PROFDIR)/merged.profdata $(PGO_COMMON)" \
	  -DCMAKE_EXE_LINKER_FLAGS="-fprofile-use=$(PGO_PROFDIR)/merged.profdata"
	cmake --build build-pgo -j$$(nproc)
	@echo "=== PGO build complete: build-pgo/z3 ==="
