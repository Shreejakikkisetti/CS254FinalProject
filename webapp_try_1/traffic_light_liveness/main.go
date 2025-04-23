package main

type State int

const (
	Red State = iota
	Yellow
)

type TrafficLight struct {
	state State
}

func (tl *TrafficLight) Transition() {
	switch tl.state {
	case Red:
		tl.state = Yellow
	case Yellow:
		tl.state = Red
	}
}

func main() {
	tl := &TrafficLight{state: Red}
	
	for {
		tl.Transition()
	}
}
