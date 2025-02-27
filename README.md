# Vulnerability Scanner

This project contains two main components:
1. A vulnerability scanner that tests for weak credentials on HTTP and SSH services
2. A SQL injection test case for a web service

## Files
- `vulnerability_scanner.py`: Python script that scans for open ports and tests for weak credentials
- `attack.json`: Contains a SQL injection payload to test database vulnerabilities
- `test.json`: Contains a normal, non-malicious query for testing
- `requirements.txt`: Lists Python package dependencies
- `.gitignore`: Specifies which files Git should ignore

## Setup and Usage

1. Install dependencies:
```bash
pip install -r requirements.txt
```

2. Run the vulnerability scanner:
```bash
python3 vulnerability_scanner.py
```

Add -v flag for verbose output:
```bash
python3 vulnerability_scanner.py -v
```

## Testing SQL Injection

To test the SQL injection payload:
```bash
curl -X POST https://cat-hw4.vercel.app/county_data -H "Content-Type: application/json" -d @attack.json
```

## Implementation Details

The vulnerability scanner:
- Scans for open TCP ports below 9000 on localhost (127.0.0.1)
- Tests HTTP basic auth and SSH password auth on each open port
- Uses a predefined set of credentials:
  ```python
  credentials = {
      'admin': 'admin',
      'root': 'abc123',
      'skroob': '12345'
  }
  ```
- Outputs successful connections in RFC 3986 format

## Credits
This project was created with assistance from Generative AI as part of CS1060 coursework.
