-------------------------------- MODULE TrafficLight --------------------------------
EXTENDS Integers

VARIABLES ns_light, ew_light    \* Removed line breaks and commas between variables

vars == <<ns_light, ew_light>>
Colors == {"red", "yellow", "green"}

TypeOK == 
    /\ ns_light \in Colors 
    /\ ew_light \in Colors

Init ==
    /\ ns_light = "red"
    /\ ew_light = "green"

\* Safety: Lights cannot both be green or yellow at the same time
Safety ==
    /\ ~(ns_light = "green" /\ ew_light = "green")
    /\ ~(ns_light = "yellow" /\ ew_light \in {"yellow", "green"})
    /\ ~(ns_light = "green" /\ ew_light \in {"yellow", "green"})

\* North-South light state transitions
NSNext ==
    \/ /\ ns_light = "red"
       /\ ew_light = "red"
       /\ ns_light' = "green"
       /\ UNCHANGED ew_light
    \/ /\ ns_light = "green"
       /\ ns_light' = "yellow"
       /\ UNCHANGED ew_light
    \/ /\ ns_light = "yellow"
       /\ ns_light' = "red"
       /\ UNCHANGED ew_light

\* East-West light state transitions
EWNext ==
    \/ /\ ew_light = "red"
       /\ ns_light = "red"
       /\ ew_light' = "green"
       /\ UNCHANGED ns_light
    \/ /\ ew_light = "green"
       /\ ew_light' = "yellow"
       /\ UNCHANGED ns_light
    \/ /\ ew_light = "yellow"
       /\ ew_light' = "red"
       /\ UNCHANGED ns_light

\* Group light change actions
Next == NSNext \/ EWNext

\* Liveness: Both directions eventually get a green light
Liveness ==
    /\ []<>(ns_light = "green")
    /\ []<>(ew_light = "green")

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Liveness

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness

================================================================================
