#!/bin/bash

# Check Java version
if ! java -version 2>&1 | grep -q 'version "1[789]\|version "[2-9][0-9]'; then
    echo "Error: Java version 17 or higher is required"
    exit 1
fi

# Check Go version
if ! go version | grep -q 'go1\.1[89]\.\|go1\.[2-9][0-9]\.'; then
    echo "Error: Go version 1.18 or higher is required"
    exit 1
fi

# Install Scala CLI if not installed
if ! command -v scala-cli &> /dev/null; then
    echo "Installing Scala CLI..."
    curl -sSLf https://scala-cli.virtuslab.org/get | sh
    source ~/.profile
fi

# Create directories
mkdir -p tools examples

# Remove existing PGo directory if it exists
rm -rf tools/pgo

# Clone PGo repository
git clone https://github.com/DistCompiler/pgo.git tools/pgo

# Initialize Go module if not exists
if [ ! -f "go.mod" ]; then
    go mod init pgo-webapp
fi

echo "Setup complete!"
