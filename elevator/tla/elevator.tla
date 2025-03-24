---- MODULE Elevator ----
EXTENDS Naturals

CONSTANTS MaxFloors,    \* Total number of floors in building
          Ascending,    \* Upward movement state
          Descending    \* Downward movement state

ASSUME MaxFloors \in Nat  \* Must be a natural number

VARIABLES position,    \* Current position (odd = at floor, even = between floors)
          movement     \* Current movement state (Ascending or Descending)

\* Helper function to determine if elevator is stopped at a specific floor
AtFloor(floor) == position = 2 * floor - 1

\* Helper function to determine if elevator is between floors
InTransit == position % 2 = 0

\* Initial state - start at ground floor
Init == /\ position = 1
        /\ movement \in {Ascending, Descending}

\* Start ascending from a floor
StartAscending == 
    /\ \E f \in 1..MaxFloors-1 : AtFloor(f)  \* At any floor except top
    /\ position' = position + 1  \* Move to in-between state
    /\ movement' = Ascending

\* Continue ascending between floors
ContinueAscending == 
    /\ InTransit  \* Must be between floors
    /\ movement = Ascending
    /\ position' = position + 1
    /\ UNCHANGED movement

\* Start descending from a floor
StartDescending == 
    /\ \E f \in 2..MaxFloors : AtFloor(f)  \* At any floor except bottom
    /\ position' = position - 1
    /\ movement' = Descending

\* Continue descending between floors
ContinueDescending == 
    /\ InTransit
    /\ movement = Descending
    /\ position' = position - 1
    /\ UNCHANGED movement

\* All possible next states
Next == \/ StartAscending
        \/ ContinueAscending
        \/ StartDescending
        \/ ContinueDescending

\* Variables for fairness conditions
vars == <<position, movement>>

\* Fairness conditions to ensure progress
Fairness == 
    /\ WF_vars(ContinueAscending)  \* Must complete in-progress movements
    /\ WF_vars(ContinueDescending)
    /\ WF_vars(StartAscending /\ AtFloor(1))  \* Must move from terminal floors
    /\ WF_vars(StartDescending /\ AtFloor(MaxFloors))
    /\ \A f \in 2..MaxFloors-1 :  \* Must eventually move from middle floors
        /\ SF_vars(StartAscending /\ AtFloor(f))
        /\ SF_vars(StartDescending /\ AtFloor(f))

\* Complete system specification
Spec == Init /\ [][Next]_vars /\ Fairness

====