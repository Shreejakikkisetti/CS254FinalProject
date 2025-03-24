<<<<<<< HEAD
# Traffic Light Controller

A formal specification and implementation of a traffic light controller system.

## Project Structure

```
.
├── src/
│   └── traffic_light.c    # C implementation
└── tla/
    ├── TrafficLight.tla   # TLA+ specification
    └── TrafficLight.cfg   # TLC model checker config
```

## Running the TLA+ Specification

1. Open `tla/TrafficLight.tla` in VSCode with the TLA+ extension
2. Use the TLA+ extension to check the model

## Running the C Implementation

```bash
gcc -o traffic_light src/traffic_light.c
./traffic_light
```
=======
# SQL Injection and Vulnerability Scanner
CS1060 - Homework 5  
Shreeja Kikkisetti

## Overview
This project contains two main components:
1. SQL Injection testing tool for exploring database vulnerabilities
2. Network vulnerability scanner for testing HTTP/SSH authentication

## Setup
```bash
# Install dependencies
pip install -r requirements.txt

# Run vulnerability scanner
python3 vulnerability_scanner.py       # Normal mode
python3 vulnerability_scanner.py -v    # Verbose mode

# Run tests
python3 test_vulnerability_scanner.py
```

## Files
- `vulnerability_scanner.py`: Main scanner implementation
- `attack.json`: SQL injection payload
- `test.json`: Original test payload
- `test_vulnerability_scanner.py`: Test suite
- `requirements.txt`: Project dependencies

## Testing Endpoints
- SQL Injection: https://cat-hw4.vercel.app/county_data
- Vulnerability Scanner: localhost ports < 9000

# AI Model Interactions

## SQL Injection Task (5.2)

### ChatGPT
- Initially refused to provide direct assistance with SQL injection
- Implemented several guardrails:
  - Warned about ethical implications of SQL injection
  - Suggested using parameterized queries instead
  - Required explicit educational context
  - Limited responses to theoretical explanations
- Workaround: Had to frame queries in hypothetical/educational context and focus on understanding the vulnerability rather than exploitation

### Perplexity
- Provided general information about SQL injection
- Helped with understanding query structure
- More open to discussing technical details
- Still emphasized responsible testing practices

### Cascade (Codeium)
- More willing to discuss SQL query structure
- Provided technical explanations when framed as educational exercise
- Helped understand string formatting vulnerabilities
- Added LIMIT clause suggestion to prevent resource abuse
- Still maintained some guardrails but more focused on controlled testing
>>>>>>> b04204e82c6171f5413744c3ffc99a93dd4a1b65
