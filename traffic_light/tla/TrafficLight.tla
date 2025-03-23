-------------------------------- MODULE TrafficLight --------------------------------
EXTENDS Integers, Sequences

VARIABLES 
    ns_light,    \* North-South traffic light state
    ew_light,    \* East-West traffic light state
    timer,       \* Timer for light changes
    turn         \* Whose turn is it next (NS or EW)

vars == <<ns_light, ew_light, timer, turn>>

Colors == {"red", "yellow", "green"}
Directions == {"NS", "EW"}
MinGreen == 30    \* Minimum time for green light
YellowTime == 5   \* Time for yellow light

TypeOK ==
    /\ ns_light \in Colors
    /\ ew_light \in Colors
    /\ timer \in Nat
    /\ turn \in Directions

Init ==
    /\ ns_light = "red"
    /\ ew_light = "green"
    /\ timer = MinGreen
    /\ turn = "NS"    \* NS gets next turn

\* Safety: Lights cannot both be green or yellow at the same time
Safety ==
    /\ ~(ns_light = "green" /\ ew_light = "green")
    /\ ~(ns_light = "yellow" /\ ew_light = "yellow")
    /\ ~(ns_light = "green" /\ ew_light = "yellow")
    /\ ~(ns_light = "yellow" /\ ew_light = "green")

\* Helper action to decrease timer
DecreaseTimer ==
    timer' = timer - 1

\* Helper action to switch turns
SwitchTurn ==
    turn' = (IF turn = "NS" THEN "EW" ELSE "NS")

\* Change NS light from red to green (when EW is red)
NSGreen ==
    /\ ns_light = "red"
    /\ ew_light = "red"
    /\ timer = 0
    /\ turn = "NS"
    /\ ns_light' = "green"
    /\ ew_light' = ew_light
    /\ timer' = MinGreen
    /\ SwitchTurn

\* Change NS light from green to yellow
NSYellow ==
    /\ ns_light = "green"
    /\ timer = 0
    /\ ns_light' = "yellow"
    /\ ew_light' = ew_light
    /\ timer' = YellowTime
    /\ turn' = turn

\* Change NS light from yellow to red
NSRed ==
    /\ ns_light = "yellow"
    /\ timer = 0
    /\ ns_light' = "red"
    /\ ew_light' = ew_light
    /\ timer' = 0
    /\ turn' = turn

\* Change EW light from red to green (when NS is red)
EWGreen ==
    /\ ew_light = "red"
    /\ ns_light = "red"
    /\ timer = 0
    /\ turn = "EW"
    /\ ew_light' = "green"
    /\ ns_light' = ns_light
    /\ timer' = MinGreen
    /\ SwitchTurn

\* Change EW light from green to yellow
EWYellow ==
    /\ ew_light = "green"
    /\ timer = 0
    /\ ew_light' = "yellow"
    /\ ns_light' = ns_light
    /\ timer' = YellowTime
    /\ turn' = turn

\* Change EW light from yellow to red
EWRed ==
    /\ ew_light = "yellow"
    /\ timer = 0
    /\ ew_light' = "red"
    /\ ns_light' = ns_light
    /\ timer' = 0
    /\ turn' = turn

\* Tick action for timer
Tick ==
    /\ timer > 0
    /\ DecreaseTimer
    /\ UNCHANGED <<ns_light, ew_light, turn>>

\* Group light change actions
NSChange == NSGreen \/ NSYellow \/ NSRed
EWChange == EWGreen \/ EWYellow \/ EWRed

Next ==
    \/ NSChange
    \/ EWChange
    \/ Tick

\* Liveness: Both directions eventually get a green light
Liveness ==
    /\ []<>(ns_light = "green")
    /\ []<>(ew_light = "green")

\* Strong fairness conditions to ensure both directions get turns
Fairness ==
    /\ SF_vars(NSGreen)
    /\ SF_vars(EWGreen)
    /\ WF_vars(NSYellow)
    /\ WF_vars(EWYellow)
    /\ WF_vars(NSRed)
    /\ WF_vars(EWRed)
    /\ WF_vars(Tick)

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness

================================================================================
