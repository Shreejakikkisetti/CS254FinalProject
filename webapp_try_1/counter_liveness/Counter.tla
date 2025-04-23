---- MODULE Counter ----
EXTENDS Naturals, TLC

VARIABLES counter

(* Liveness property: eventually counter will be 3 *)
Liveness == <>(counter = 3)

Init == counter = 0

Next == counter' = (counter + 1) % 4

Spec == Init /\ [][Next]_counter

(* Specification with liveness property *)
SpecWithLiveness == 
    /\ Spec 
    /\ Liveness

=============================================================================