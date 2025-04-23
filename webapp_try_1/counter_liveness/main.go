package main

type Counter struct {
	value int
}

func (c *Counter) Increment() {
	c.value = (c.value + 1) % 4
}

func main() {
	counter := &Counter{value: 0}
	
	for counter.value < 4 {
		counter.Increment()
	}
	
	// Assert liveness property: counter must reach 3
	if counter.value != 3 {
		panic("Liveness property violated: counter did not reach 3")
	}
}

// Liveness Property in TLA+: 
// LivenessProperty == <>(value = 3)
// This means: "Eventually, the value will be 3"
