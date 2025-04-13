# Go to TLA+ Web Application

This web application helps convert Go code to TLA+ specifications and vice versa. It provides a user-friendly interface for writing PlusCal code, translating it to TLA+, and verifying it with PGo.

## Prerequisites

1. Node.js >= 18.0.0
2. npm >= 8.0.0
3. Go >= 1.16
4. Scala CLI (for PGo)
5. Java Runtime Environment (JRE) for TLA+ tools

## Setup

1. Clone the repository
2. Install frontend dependencies:
   ```bash
   npm install
   ```
3. Set up PGo:
   ```bash
   cd backend
   ./setup-pgo.sh
   ```

## Running the Application

1. Start the frontend:
   ```bash
   npm start
   ```
   This will run the app in development mode at [http://localhost:3000](http://localhost:3000)

2. Start the backend server:
   ```bash
   cd backend
   node server.js
   ```
   The backend will run on port 3002

## Features

- Write PlusCal code in a Monaco editor
- Translate PlusCal to TLA+ specifications
- Verify TLA+ code with PGo
- Generate Go code from TLA+ specifications
- Test PGo functionality with example code

## Project Structure

- `/src` - Frontend React application
  - `/components` - React components including PlusCal editor and code comparison
  - `/utils` - Utility functions for TLA+ translation
- `/backend` - Node.js backend server
  - `/pgoHandler.js` - PGo integration
  - `/server.js` - Express server
  - `/examples` - Generated TLA+ and Go files
  - `/tools/pgo` - PGo installation

## Development

- The frontend uses React with TypeScript and Material-UI
- The backend uses Express.js and integrates with PGo
- PGo is used for verifying TLA+ specifications and generating Go code
