---- MODULE ElevatorCheck ----
EXTENDS elevator

\* State display for better debugging
StateView == [
    pos |-> position,
    currentFloor |-> IF InTransit THEN "between" ELSE (position + 1) \div 2,
    dir |-> movement
]

\* Safety: Position stays within valid bounds
ValidBounds == /\ position >= 0
               /\ position <= 2*MaxFloors-1

\* Liveness: Elevator doesn't get permanently stuck between floors
StuckInTransit == <>[](InTransit)
NoStuck == ~StuckInTransit

\* Liveness: Elevator can reach every floor
ReachesAllFloors == [] \A f \in 1..MaxFloors : <>(AtFloor(f))

====
