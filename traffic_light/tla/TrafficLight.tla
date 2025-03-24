-------------------------------- MODULE TrafficLight --------------------------------
EXTENDS Integers

VARIABLE light    \* Single traffic light state

vars == <<light>>
Colors == {"red", "yellow", "green"}

TypeOK == light \in Colors

Init == light = "red"

\* Simple state transitions: red -> green -> yellow -> red
Next ==
    \/ /\ light = "red"
       /\ light' = "green"
    \/ /\ light = "green"
       /\ light' = "yellow"
    \/ /\ light = "yellow"
       /\ light' = "red"

\* Safety as a state predicate (for invariant checking)
SafetyInvariant ==
    light \in Colors  \* Only valid colors are allowed

\* Safety as a temporal property (for theorem proving)
Safety ==
    [][
        /\ (light = "red" => light' \in {"red", "green"})
        /\ (light = "green" => light' \in {"green", "yellow"})
        /\ (light = "yellow" => light' \in {"yellow", "red"})
    ]_vars

\* Liveness: The light must change colors eventually
Liveness ==
    /\ []<>(light = "red")
    /\ []<>(light = "yellow")
    /\ []<>(light = "green")

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Liveness

\* Theorems
THEOREM Spec => []TypeOK
THEOREM Spec => Safety

================================================================================
