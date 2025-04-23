package main



const (
	NumFloors = 5
)

type Direction int

const (
	Idle Direction = iota
	Up
	Down
)

func (d Direction) String() string {
	switch d {
	case Idle:
		return "Idle"
	case Up:
		return "Up"
	case Down:
		return "Down"
	}
	return "Unknown"
}

type Elevator struct {
	currentFloor int
	doorOpen     bool
	direction    Direction
	requests     [NumFloors]bool // true if there is a pending request at that floor
}

func (e *Elevator) requestFloor(floor int) {
	if floor >= 0 && floor < NumFloors {
		e.requests[floor] = true
	}
}

func (e *Elevator) openDoor() {
	if !e.doorOpen {
			e.doorOpen = true
	}
}

func (e *Elevator) closeDoor() {
	if e.doorOpen {
			e.doorOpen = false
	}
}

func (e *Elevator) move() {
	if e.doorOpen {
			return
	}
	if e.direction == Up && e.currentFloor < NumFloors-1 {
		e.currentFloor++
		} else if e.direction == Down && e.currentFloor > 0 {
		e.currentFloor--
		} else {
		e.direction = Idle
	}
}

func (e *Elevator) step() {
	// Serve request at current floor
	if e.requests[e.currentFloor] {
		e.openDoor()
			e.requests[e.currentFloor] = false
		return
	}
	// If door is open and no request, close it
	if e.doorOpen {
		e.closeDoor()
		return
	}
	// Find next request
	next := -1
	for i := 0; i < NumFloors; i++ {
		if e.requests[i] {
			next = i
			break
		}
	}
	if next == -1 {
		e.direction = Idle
		return // No requests
	}
	// Decide direction
	if next > e.currentFloor {
		e.direction = Up
	} else if next < e.currentFloor {
		e.direction = Down
	} else {
		e.direction = Idle
	}
	// Move if needed
	if e.direction != Idle {
		e.move()
	}
}

func main() {
	e := Elevator{currentFloor: 0, doorOpen: false, direction: Idle}
	// Sample requests
	e.requestFloor(2)
	e.requestFloor(4)
	e.requestFloor(1)
	steps := 0
	for steps < 20 {
			e.step()
		steps++
	}
}
