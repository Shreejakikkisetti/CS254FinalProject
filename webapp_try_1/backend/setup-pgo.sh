#!/bin/bash

# Create tools directory if it doesn't exist
mkdir -p tools/pgo

# Download the latest PGo release
curl -L -o tools/pgo/pgo.jar "https://github.com/DistCompiler/pgo/releases/latest/download/pgo.jar"

# Create temp directory for PGo operations
mkdir -p temp
