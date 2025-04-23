\* BEGIN TRANSLATION (chksum(pcal) = "e8c00948" /\ chksum(tla) = "3ec95464")
VARIABLES currentFloor, doorOpen

vars == << currentFloor, doorOpen >>

Init == (* Global variables *)
        /\ currentFloor = 0
        /\ doorOpen = FALSE

Next == IF doorOpen = FALSE
           THEN /\ doorOpen' = TRUE
                /\ UNCHANGED currentFloor
           ELSE /\ doorOpen' = FALSE
                /\ IF currentFloor < 4
                       THEN currentFloor' = currentFloor + 1
                       ELSE currentFloor' = currentFloor
\* Updated: Only increment currentFloor if less than 4 (matches Go logic)

Spec == Init /\ [][Next]_vars

\* END TRANSLATION