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
