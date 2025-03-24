#include <stdio.h>
#include <stdbool.h>
#include <unistd.h>

#define MAX_FLOORS 5
#define BETWEEN_FLOOR_TIME 2  // seconds to move between floors

typedef enum {
    ASCENDING = 1,
    DESCENDING = -1
} Direction;

typedef struct {
    int position;     // odd numbers for floors (2f-1), even for between floors
    Direction dir;    // current direction
} Elevator;

// Helper functions matching TLA+ spec
bool at_floor(int position, int floor) {
    return position == (2 * floor - 1);
}

bool in_transit(int position) {
    return position % 2 == 0;
}

int current_floor(int position) {
    if (in_transit(position)) {
        printf("Currently between floors\n");
        return -1;
    }
    return (position + 1) / 2;
}

void print_status(Elevator *e) {
    int floor = current_floor(e->position);
    printf("Position: %d, ", e->position);
    if (floor != -1) {
        printf("Floor: %d, ", floor);
    }
    printf("Direction: %s\n", e->dir == ASCENDING ? "Up" : "Down");
}

// Movement actions matching TLA+ spec
bool start_ascending(Elevator *e) {
    int floor = current_floor(e->position);
    if (floor != -1 && floor < MAX_FLOORS) {
        e->position++;
        e->dir = ASCENDING;
        return true;
    }
    return false;
}

bool continue_ascending(Elevator *e) {
    if (in_transit(e->position) && e->dir == ASCENDING) {
        e->position++;
        return true;
    }
    return false;
}

bool start_descending(Elevator *e) {
    int floor = current_floor(e->position);
    if (floor != -1 && floor > 1) {
        e->position--;
        e->dir = DESCENDING;
        return true;
    }
    return false;
}

bool continue_descending(Elevator *e) {
    if (in_transit(e->position) && e->dir == DESCENDING) {
        e->position--;
        return true;
    }
    return false;
}

int main() {
    Elevator e = {.position = 1, .dir = ASCENDING};  // Start at ground floor
    
    printf("Elevator Demo - Moving through all floors\n");
    printf("Initial state:\n");
    print_status(&e);
    
    // Demo: Move up to top floor
    while (current_floor(e.position) != MAX_FLOORS) {
        if (start_ascending(&e)) {
            printf("Starting to move up:\n");
            print_status(&e);
            sleep(BETWEEN_FLOOR_TIME);
        }
        if (continue_ascending(&e)) {
            printf("Continuing up:\n");
            print_status(&e);
            sleep(BETWEEN_FLOOR_TIME);
        }
    }
    
    printf("\nReached top floor, now descending\n");
    
    // Demo: Move down to ground floor
    while (current_floor(e.position) != 1) {
        if (start_descending(&e)) {
            printf("Starting to move down:\n");
            print_status(&e);
            sleep(BETWEEN_FLOOR_TIME);
        }
        if (continue_descending(&e)) {
            printf("Continuing down:\n");
            print_status(&e);
            sleep(BETWEEN_FLOOR_TIME);
        }
    }
    
    printf("\nDemo complete!\n");
    return 0;
}
