# Traffic Light Controller TLA+ Specification

This project contains a formal specification of a traffic light controller system written in TLA+. The specification models a traffic light system at an intersection controlling North-South and East-West traffic flows.

## Quick Start

1. Follow the instructions in [SETUP.md](SETUP.md) to install required tools
2. Open the project in VSCode with TLA+ extension
3. Open `tla/TrafficLight.tla`
4. Use the TLA+ extension to check the model

## Project Structure

```
traffic_light/
├── README.md        # This file
├── SETUP.md         # Setup instructions
├── .gitignore      # Git ignore rules
└── tla/            # TLA+ specification files
    ├── TrafficLight.tla  # Main specification
    └── TrafficLight.cfg  # Model checker config
```

## Specification Details

The traffic light controller manages an intersection with:
- North-South traffic lights
- East-West traffic lights
- Timer for light changes
- Turn management for fair scheduling

### Variables
- `ns_light`: North-South traffic light state (red, yellow, green)
- `ew_light`: East-West traffic light state (red, yellow, green)
- `timer`: Counter for light duration
- `turn`: Tracks which direction gets next green light

### Properties Verified

1. **Type Safety** (`TypeOK`):
   - Light states are valid colors
   - Timer is a natural number
   - Turn variable has valid direction

2. **Safety Properties**:
   - No conflicting green lights
   - No conflicting yellow lights
   - No green-yellow conflicts

3. **Liveness Properties**:
   - Both directions eventually get green lights
   - System never deadlocks
   - Fair scheduling between directions

### Timing Parameters
- `MinGreen = 30`: Minimum duration for green light
- `YellowTime = 5`: Duration for yellow light

## Development

The specification uses:
- Strong fairness (SF) for green light changes
- Weak fairness (WF) for yellow/red transitions
- Explicit turn management for alternation
- Timer-based state transitions

## Contributing

1. Fork the repository
2. Create your feature branch
3. Make your changes
4. Run the model checker to verify properties
5. Submit a pull request

## License

This project is open source and available under the MIT License.
