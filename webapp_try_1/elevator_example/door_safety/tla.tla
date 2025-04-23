\---- MODULE tla ----
CONSTANTS in, none
VARIABLES doorOpen, direction

vars == << doorOpen, direction >>

Init == /\ doorOpen = FALSE
        /\ direction = none

Next == /\ IF doorOpen = FALSE
              THEN /\ doorOpen' = TRUE
                   /\ direction' = in
              ELSE /\ doorOpen' = FALSE
                   /\ direction' = none

DoorSafety == (doorOpen = TRUE) => (direction = in)

Spec == Init /\ [][Next]_vars

====

\* END TRANSLATION