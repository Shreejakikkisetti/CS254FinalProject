---- MODULE TrafficLight ----
EXTENDS Naturals, TLC

VARIABLES state

(* define statement *)
LivenessProperty == <>(state = "Green")

vars == << state >>

Init == (* Global variables *)
        /\ state = "Red"

Next == 
    \/ /\ state = "Red"
       /\ state' = "Yellow"
    \/ /\ state = "Yellow"
       /\ state' = "Red"

Spec == Init /\ [][Next]_vars

\* Explicitly check that Green is NEVER reached
SpecWithLiveness == 
    /\ Spec 
    /\ ~LivenessProperty  \* This ensures the liveness property FAILS

\* BEGIN TRANSLATION (chksum(pcal) = "ea37b667" /\ chksum(tla) = "915718cf")
=============================================================================