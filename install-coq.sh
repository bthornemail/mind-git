#!/bin/bash
# Coq Installation Script for Ubuntu/Debian
echo "Installing Coq theorem prover..."

# Check if already installed
if command -v coqc &> /dev/null; then
    echo "Coq already installed: $(coqc --version)"
    exit 0
fi

# Try different installation methods
if command -v apt &> /dev/null; then
    echo "Installing via apt (requires sudo)..."
    sudo apt update
    sudo apt install -y coq coqide
elif command -v brew &> /dev/null; then
    echo "Installing via Homebrew..."
    brew install coq
elif command -v opam &> /dev/null; then
    echo "Installing via opam..."
    opam update
    opam install coq.8.18.0
else
    echo "No package manager found. Please install Coq manually:"
    echo "  Ubuntu/Debian: sudo apt install coq coqide"
    echo "  macOS: brew install coq"
    echo "  Or download from: https://coq.inria.fr/download"
    exit 1
fi

echo "Coq installation complete!"