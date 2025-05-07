package main

// Message types for Paxos protocol
type MsgType int

const (
	Prepare MsgType = iota + 1
	Promise
	Propose
	Accept
)

// Message structure for communication
type Message struct {
	From   int
	To     int
	Type   MsgType
	Seq    int
	Val    string
}

// Proposer component
type Proposer struct {
	ID         int
	Seq        int
	ProposeNum int
	ProposeVal string
	Acceptors  map[int]bool
	Promises   map[int]bool
}

// Main proposer logic
func (p *Proposer) Run() {
	// Phase 1: Prepare
	for !p.MajorityReached() {
		p.Seq++
		p.ProposeNum = p.Seq<<4 | p.ID
		
		// Send prepare messages to acceptors
		for acceptorID := range p.Acceptors {
			// In a real system, would send message to acceptor
			p.SendPrepare(acceptorID)
		}
		
		// Simulate receiving promises
		for acceptorID := range p.Acceptors {
			if p.ReceivePromise(acceptorID) {
				p.Promises[acceptorID] = true
			}
		}
	}
	
	// Phase 2: Propose
	for acceptorID := range p.Promises {
		if p.Promises[acceptorID] {
			// In a real system, would send propose message
			p.SendPropose(acceptorID)
		}
	}
}

// Send prepare message to an acceptor
func (p *Proposer) SendPrepare(acceptorID int) bool {
	// Simplified: just return true to simulate message sent
	return true
}

// Receive promise from an acceptor
func (p *Proposer) ReceivePromise(acceptorID int) bool {
	// Simplified: just return true to simulate promise received
	return true
}

// Send propose message to an acceptor
func (p *Proposer) SendPropose(acceptorID int) bool {
	// Simplified: just return true to simulate message sent
	return true
}

// Check if majority of promises received
func (p *Proposer) MajorityReached() bool {
	count := 0
	for _, promised := range p.Promises {
		if promised {
			count++
		}
	}
	return count > len(p.Acceptors)/2
}

// Acceptor component
type Acceptor struct {
	ID         int
	PromiseSeq int
	AcceptSeq  int
	AcceptVal  string
}

// Process prepare message
func (a *Acceptor) ProcessPrepare(prepareSeq int) bool {
	if prepareSeq > a.PromiseSeq {
		a.PromiseSeq = prepareSeq
		return true
	}
	return false
}

// Process propose message
func (a *Acceptor) ProcessPropose(proposeSeq int, proposeVal string) bool {
	if proposeSeq >= a.PromiseSeq {
		a.AcceptSeq = proposeSeq
		a.AcceptVal = proposeVal
		return true
	}
	return false
}

// Learner component
type Learner struct {
	AcceptedVals map[string]int
	Acceptors    map[int]string
}

// Process accept message
func (l *Learner) ProcessAccept(acceptorID int, val string) string {
	l.Acceptors[acceptorID] = val
	
	// Count values
	counts := make(map[string]int)
	for _, v := range l.Acceptors {
		counts[v]++
	}
	
	// Check if any value has majority
	majority := len(l.Acceptors)/2 + 1
	for val, count := range counts {
		if count >= majority {
			return val
		}
	}
	
	return ""
}

func main() {
	// Example setup
	proposer := &Proposer{
		ID:         1,
		ProposeVal: "consensus-value",
		Acceptors:  make(map[int]bool),
		Promises:   make(map[int]bool),
	}
	
	// Add some acceptors
	proposer.Acceptors[1] = true
	proposer.Acceptors[2] = true
	proposer.Acceptors[3] = true
	
	// Run the proposer
	proposer.Run()
}
