#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdbool.h>
#include <string.h>

// Constants
#define MIN_GREEN_TIME 30
#define YELLOW_TIME 5

// Light states
typedef enum {
    RED,
    YELLOW,
    GREEN
} LightState;

// Traffic light structure
typedef struct {
    LightState ns_light;  // North-South light
    LightState ew_light;  // East-West light
    int timer;            // Timer for state changes
} TrafficSystem;

// Convert light state to string
const char* light_to_string(LightState state) {
    switch (state) {
        case RED:    return "red";
        case YELLOW: return "yellow";
        case GREEN:  return "green";
        default:     return "unknown";
    }
}

// Initialize traffic system
void init_system(TrafficSystem* sys) {
    sys->ns_light = RED;
    sys->ew_light = GREEN;
    sys->timer = MIN_GREEN_TIME;
}

// Check safety properties
bool check_safety(TrafficSystem* sys) {
    // Lights cannot both be green or yellow at the same time
    if ((sys->ns_light == GREEN && sys->ew_light == GREEN) ||
        (sys->ns_light == YELLOW && sys->ew_light == YELLOW) ||
        (sys->ns_light == GREEN && sys->ew_light == YELLOW) ||
        (sys->ns_light == YELLOW && sys->ew_light == GREEN)) {
        return false;
    }
    return true;
}

// Update system state
void update_system(TrafficSystem* sys) {
    // Decrease timer
    if (sys->timer > 0) {
        sys->timer--;
        return;
    }

    // State transitions
    if (sys->ns_light == RED && sys->ew_light == RED) {
        // Start NS green cycle
        sys->ns_light = GREEN;
        sys->timer = MIN_GREEN_TIME;
    }
    else if (sys->ns_light == GREEN && sys->timer == 0) {
        // NS green to yellow
        sys->ns_light = YELLOW;
        sys->timer = YELLOW_TIME;
    }
    else if (sys->ns_light == YELLOW && sys->timer == 0) {
        // NS yellow to red
        sys->ns_light = RED;
        sys->timer = 0;
    }
    else if (sys->ew_light == GREEN && sys->timer == 0) {
        // EW green to yellow
        sys->ew_light = YELLOW;
        sys->timer = YELLOW_TIME;
    }
    else if (sys->ew_light == YELLOW && sys->timer == 0) {
        // EW yellow to red
        sys->ew_light = RED;
        sys->timer = 0;
    }
    else if (sys->ew_light == RED && sys->ns_light == RED) {
        // Start EW green cycle
        sys->ew_light = GREEN;
        sys->timer = MIN_GREEN_TIME;
    }
}

// Display current state
void display_state(TrafficSystem* sys) {
    printf("North-South: %-6s  East-West: %-6s  Timer: %d\n",
           light_to_string(sys->ns_light),
           light_to_string(sys->ew_light),
           sys->timer);
}

int main() {
    TrafficSystem sys;
    init_system(&sys);
    
    printf("Traffic Light Controller Simulation\n");
    printf("----------------------------------\n");
    
    // Run simulation for a few cycles
    for (int i = 0; i < 200; i++) {
        display_state(&sys);
        
        if (!check_safety(&sys)) {
            printf("ERROR: Safety violation detected!\n");
            return 1;
        }
        
        update_system(&sys);
        sleep(1);  // Wait for 1 second between updates
    }
    
    return 0;
}
