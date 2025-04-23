package main

type Counter struct {
	value int
}

func (c *Counter) Increment() {
	// Only increment if value is less than 5
	if c.value < 5 {
		c.value++
	}
}

func (c *Counter) CheckSafetyProperty() bool {
	// Safety property: counter should never exceed 5
	return c.value < 5
}

func main() {
	counter := &Counter{value: 0}
	
	// Increment while maintaining safety property
	for counter.value < 5 {
		counter.Increment()
		
		// Check safety property (equivalent to PlusCal's assert)
		if !counter.CheckSafetyProperty() {
			panic("Safety property violated: counter exceeded 5")
		}
	}

	// Final safety assertion
	if counter.value >= 5 {
		panic("Final safety assertion failed: counter should not reach 5")
	}
}

// Safety Property: 
// The counter must never exceed the value of 5
// This demonstrates a simple safety property that gets violated

// Specific Safety Property to Verify:
// Safety Property: value < 3
// This property will fail during verification
// Represents a "bad thing" happening when value reaches or exceeds 3
