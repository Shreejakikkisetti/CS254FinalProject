# Mutex Lock System

A simple mutex lock implementation with formal specification in TLA+ and implementation in C.

## Project Structure

```
mutex/
├── src/          # C implementation
│   └── mutex.c   # Mutex implementation using pthreads
└── tla/          # TLA+ specification
    ├── Mutex.tla # Base mutex specification
    └── Mutex.cfg # Model checking config
```

## TLA+ Specification

The TLA+ specification models a mutex lock system with the following features:

1. State Space:
   - Program counter (`pc`) for each process: noncritical, trying, critical
   - Lock state: FREE (0) or held by process ID

2. Actions:
   - Try: Process attempts to acquire lock
   - Enter: Process enters critical section if lock is free
   - Exit: Process leaves critical section and releases lock

3. Properties:
   - Safety (Mutual Exclusion): No two processes can be in critical section simultaneously
   - Liveness: If a process is trying to enter, it eventually will
   - Deadlock Freedom: System can always make progress

### Running Model Checker

```bash
cd tla
tlc Mutex.tla -config Mutex.cfg
```

## C Implementation

The C implementation uses pthreads to demonstrate mutex locking with:

1. Multiple threads competing for a shared lock
2. Visual state display showing each thread's current state
3. Random delays to simulate work and create contention

### Building and Running

```bash
cd src
gcc -o mutex mutex.c -pthread
./mutex
```

The program will show each thread's state (NONCRIT, TRYING, CRITICAL) in real-time as they compete for the lock.
