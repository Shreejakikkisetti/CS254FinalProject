package main

type TrafficLightColor int

const (
    Red TrafficLightColor = iota
    Yellow
    Green
    Blue
)

type TrafficLight struct {
    currentColor TrafficLightColor
}

func (tl *TrafficLight) Transition() bool {
    switch tl.currentColor {
    case Red:
        tl.currentColor = Green
    case Green:
        tl.currentColor = Yellow
    case Yellow:
        tl.currentColor = Red
    default:
        return false
    }
    return true
}

func (tl *TrafficLight) ViolateLiveness() {
    tl.currentColor = Blue
}

func main() {
    trafficLight := &TrafficLight{currentColor: Red}
    trafficLight.Transition()
    trafficLight.ViolateLiveness()
}