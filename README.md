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
