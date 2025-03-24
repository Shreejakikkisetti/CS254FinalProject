# Setup Guide

## Prerequisites

1. Install Visual Studio Code
2. Install the TLA+ Extension for VSCode
   - Open VSCode
   - Go to Extensions (Ctrl+Shift+X or Cmd+Shift+X)
   - Search for "TLA+"
   - Install "TLA+ by Microsoft"

## Getting Started

1. Clone the repository:
   ```bash
   git clone <repository-url>
   cd traffic_light
   ```

2. Open in VSCode:
   ```bash
   code .
   ```

3. Open the TLA+ files:
   - Navigate to `tla/TrafficLight.tla`
   - The TLA+ extension should automatically recognize the file

4. Running the Model Checker:
   - With `TrafficLight.tla` open, click on "Check model" in the TLA+ extension
   - Or use Command Palette (Cmd+Shift+P) and search for "TLA+: Check model"
   - The results will appear in the "TLA+ Model Checking Results" panel

## Troubleshooting

If you encounter any issues:
1. Make sure both `TrafficLight.tla` and `TrafficLight.cfg` are in the same directory
2. Verify that the TLA+ extension is properly installed and activated
3. Try reloading VSCode if the extension doesn't recognize the files
