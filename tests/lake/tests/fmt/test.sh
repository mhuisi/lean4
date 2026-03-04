#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the `lake fmt` command

# Copy input project to working directory
cp -r input/* .

# Build the project first (fmt needs .olean files)
test_run build

# Run fmt on a single Lean file and verify it succeeds
test_run fmt Lib.lean

# Run fmt on all project modules (no file argument) and verify it succeeds
test_run fmt
