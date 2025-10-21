#!/usr/bin/env bash
# Test runner for p-np2 project
set -euo pipefail

echo "=== Running p-np2 tests ==="

# Build the project first
echo "Building project..."
lake build

# Run tests
echo ""
echo "Running tests..."
lake test

echo ""
echo "=== All tests passed! ==="
