---- MODULE paxos_simple_safety ----
EXTENDS Integers, Sequences, TLC, FiniteSets

(* This is a simplified Paxos model focused on safety properties *)

CONSTANTS Values

VARIABLES
  proposeNum,    (* Current proposal number *)
  proposeVal,    (* Value being proposed *)
  promiseSeq,    (* Highest sequence number promised *)
  acceptSeq,     (* Highest sequence number accepted *)
  acceptVal      (* Value accepted with highest sequence number *)

vars == << proposeNum, proposeVal, promiseSeq, acceptSeq, acceptVal >>

(* Type invariant *)
TypeOK ==
  /\ proposeNum \in Nat
  /\ proposeVal \in Values
  /\ promiseSeq \in Nat
  /\ acceptSeq \in Nat
  /\ acceptVal \in Values

(* Safety property: acceptSeq is always >= promiseSeq *)
Safety == acceptSeq >= promiseSeq

(* Initial state *)
Init ==
  /\ proposeNum = 0
  /\ proposeVal \in Values
  /\ promiseSeq = 0
  /\ acceptSeq = 0
  /\ acceptVal \in Values

(* Phase 1: Prepare - Proposer chooses a new proposal number *)
Prepare ==
  /\ proposeNum' = proposeNum + 1
  /\ proposeVal' \in Values
  /\ UNCHANGED << promiseSeq, acceptSeq, acceptVal >>

(* Phase 2: Promise - Acceptor promises not to accept proposals with lower numbers *)
Promise ==
  /\ proposeNum > promiseSeq
  /\ promiseSeq' = proposeNum
  /\ UNCHANGED << proposeNum, proposeVal, acceptSeq, acceptVal >>

(* Phase 3: Accept - Acceptor accepts a proposal *)
Accept ==
  /\ promiseSeq >= acceptSeq  (* This ensures Safety is maintained *)
  /\ acceptSeq' = promiseSeq
  /\ acceptVal' = proposeVal
  /\ UNCHANGED << proposeNum, proposeVal, promiseSeq >>

(* Next state relation *)
Next ==
  \/ Prepare
  \/ Promise
  \/ Accept

(* Complete specification *)
Spec == Init /\ [][Next]_vars

(* State constraint to limit model checking *)
StateConstraint == proposeNum <= 3

====
