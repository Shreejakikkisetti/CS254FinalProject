#!/bin/bash

# Create tools directory if it doesn't exist
mkdir -p tools

# Download tla2tools.jar
curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -o tools/tla2tools.jar

# Make the script executable
chmod +x tools/tla2tools.jar

echo "TLA+ tools setup complete!"
