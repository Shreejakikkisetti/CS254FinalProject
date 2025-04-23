---- MODULE ValueCheck ----
EXTENDS Naturals, TLC

\* BEGIN TRANSLATION (chksum(pcal) = "8a1239d6" /\ chksum(tla) = "e939fb6")
VARIABLES pc, value

vars == << pc, value >>

Init == (* Global variables *)
        /\ value = 0
        /\ pc = "loop"

loop == /\ pc = "loop"
        /\ IF (value < 10)
              THEN /\ value' = value + 1
                   /\ Assert(value' < 5, 
                             "Safety Property Violation: value exceeded 5")
                   /\ pc' = "loop"
              ELSE /\ pc' = "Done"
                   /\ value' = value

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == loop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

(* Safety property: value must never exceed 5 *)
SafetyInvariant == value < 5

====
