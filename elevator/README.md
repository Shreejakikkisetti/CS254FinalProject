# Elevator Control System

A simple elevator control system with formal specification in TLA+ and implementation in C.

## Project Structure

```
elevator/
├── src/           # C implementation
│   └── elevator.c # Main elevator control logic
└── tla/           # TLA+ specification
    ├── elevator.tla        # Base elevator specification
    ├── elevator.cfg        # Base config
    ├── ElevatorCheck.tla   # Model checking specification
    └── ElevatorCheck.cfg   # Model checking config
```

## TLA+ Specification

The TLA+ specification models an elevator system with the following features:

1. Position tracking:
   - Odd numbers (2f-1) represent being at floor f
   - Even numbers represent being between floors

2. Movement states:
   - Ascending (moving up)
   - Descending (moving down)

3. Actions:
   - StartAscending: Begin moving up from a floor
   - ContinueAscending: Continue moving up between floors
   - StartDescending: Begin moving down from a floor
   - ContinueDescending: Continue moving down between floors

4. Properties verified by model checker:
   - Safety: Elevator stays within valid position bounds
   - Liveness: Elevator eventually visits every floor
   - Liveness: Elevator doesn't get stuck between floors

### Running Model Checker

```bash
cd tla
tlc ElevatorCheck.tla -config ElevatorCheck.cfg
```

## C Implementation

The C implementation mirrors the TLA+ specification's state machine, providing:

1. Same position encoding (2f-1 for floors)
2. Same movement states and actions
3. Visual demonstration of elevator movement
4. Time delays to simulate floor-to-floor travel

### Building and Running

```bash
cd src
gcc -o elevator elevator.c
./elevator
```

The program will demonstrate the elevator moving from ground floor to top floor and back, showing its position and state at each step.
