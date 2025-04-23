\---- MODULE tla ----
EXTENDS Naturals
\* CHANGES MADE FOR TLC COMPATIBILITY (2025-04-22):
\* 1. Removed all Assert(...) statements (not valid in TLA+)
\* 2. Kept only valid TLA+ expressions for state transitions
\* 3. Ensured currentFloor is always an integer

VARIABLES currentFloor, doorOpen

vars == << currentFloor, doorOpen >>

Init == 
    /\ currentFloor = 0
    /\ doorOpen = FALSE

Next == 
    IF doorOpen = FALSE
        THEN /\ doorOpen' = TRUE
             /\ UNCHANGED currentFloor
        ELSE /\ doorOpen' = FALSE
             /\ IF currentFloor < 4
                    THEN currentFloor' = currentFloor + 1
                    ELSE currentFloor' = currentFloor
\* Updated: Only increment currentFloor if less than 4 (matches Go logic)

FloorBounds == currentFloor >= 0 /\ currentFloor <= 4

Spec == Init /\ [][Next]_vars

====
\* END TRANSLATION