--------------------------- MODULE Mutex ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N \* Number of processes

VARIABLES 
    pc,     \* Program counter for each process (noncritical, trying, critical)
    lock,   \* Lock state (FREE or process id that holds it)
    queue   \* Sequence of processes waiting for the lock

vars == <<pc, lock, queue>>

States == {"noncritical", "trying", "critical"}
Procs == 1..N

\* Helper operator to check if a process is in the queue
InQueue(p) == \E i \in 1..Len(queue) : queue[i] = p

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ lock \in {0} \union Procs  \* 0 means FREE
    /\ queue \in Seq(Procs)      \* Queue is a sequence of process IDs

Init ==
    /\ pc = [p \in Procs |-> "noncritical"]
    /\ lock = 0
    /\ queue = <<>>  \* Empty sequence

\* Try to acquire lock
Try(p) ==
    /\ pc[p] = "noncritical"
    /\ ~InQueue(p)  \* Not already in queue
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ queue' = Append(queue, p)  \* Add to end of queue
    /\ UNCHANGED lock

\* Enter critical section if lock is free and first in queue
Enter(p) ==
    /\ pc[p] = "trying"
    /\ lock = 0
    /\ Len(queue) > 0  \* Queue not empty
    /\ Head(queue) = p  \* Must be first in queue
    /\ lock' = p
    /\ queue' = Tail(queue)  \* Remove from front of queue
    /\ pc' = [pc EXCEPT ![p] = "critical"]

\* Exit critical section
Exit(p) ==
    /\ pc[p] = "critical"
    /\ lock = p
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "noncritical"]
    /\ UNCHANGED queue

\* System transitions
Next == \E p \in Procs : Try(p) \/ Enter(p) \/ Exit(p)

\* Fairness conditions
Fairness == \A p \in Procs :
    /\ WF_vars(Try(p))
    /\ WF_vars(Enter(p))
    /\ WF_vars(Exit(p))

\* Safety: mutual exclusion
MutualExclusion ==
    \A p1, p2 \in Procs :
        (p1 # p2) => ~(pc[p1] = "critical" /\ pc[p2] = "critical")

\* Liveness: if a process is trying, it eventually enters
Liveness ==
    \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "critical")

\* No starvation: if a process is in the queue, it eventually enters
NoStarvation ==
    \A p \in Procs : InQueue(p) ~> (pc[p] = "critical")

\* Complete spec
Spec == Init /\ [][Next]_vars /\ Fairness

THEOREM Spec => []TypeOK
=============================================================================
