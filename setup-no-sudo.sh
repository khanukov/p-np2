#!/usr/bin/env bash
# Setup script for p-np2 project (without sudo)
# Installs Lean toolchain and downloads build cache

set -euo pipefail

echo "=== Setting up p-np2 development environment (no sudo) ==="

# Install elan if not already installed
if ! command -v elan &> /dev/null; then
    echo "Installing elan (Lean version manager)..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

    # Add to current shell PATH
    export PATH="$HOME/.elan/bin:$PATH"

    echo ""
    echo "NOTE: elan has been installed to ~/.elan/bin"
    echo "Add this to your ~/.bashrc or ~/.zshrc:"
    echo '  export PATH="$HOME/.elan/bin:$PATH"'
    echo ""
else
    echo "elan is already installed"
fi

# Make sure elan is in PATH for this script
export PATH="$HOME/.elan/bin:$PATH"

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
echo ""
echo "If this is your first time installing elan, run this command:"
echo '  export PATH="$HOME/.elan/bin:$PATH"'
echo ""
echo "Or restart your shell, then you can run:"
echo "  lake build        - Build the project"
echo "  lake test         - Run tests"
echo "  ./scripts/check.sh - Full project check"
