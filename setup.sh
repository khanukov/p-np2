#!/usr/bin/env bash
# Setup script for p-np2 project
# Installs Lean toolchain and downloads build cache

set -euo pipefail

echo "=== Setting up p-np2 development environment ==="

# Install elan if not already installed
if ! command -v elan &> /dev/null; then
    echo "Installing elan (Lean version manager)..."
    sudo apt-get update
    sudo apt-get install -y elan
else
    echo "elan is already installed"
fi

# Install the correct Lean toolchain
echo "Installing Lean toolchain from lean-toolchain file..."
elan toolchain install "$(cat lean-toolchain)"

# Set the toolchain as default for this directory
echo "Setting toolchain as default..."
elan override set "$(cat lean-toolchain)"

# Download cached build artifacts
echo "Downloading build cache (this may take a while)..."
lake exe cache get || {
    echo "Warning: Failed to download cache. Building from scratch will take longer."
}

echo ""
echo "=== Setup complete! ==="
echo "You can now run:"
echo "  lake build        - Build the project"
echo "  lake test         - Run tests"
echo "  ./scripts/check.sh - Full project check"
