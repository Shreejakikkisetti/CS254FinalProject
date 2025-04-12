---- MODULE Test ----
EXTENDS Integers, TLC

(*
--algorithm test
variables x = 0;
begin
  a1: x := 1;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e30a4e0b" /\ chksum(tla) = "71e5dd47")
VARIABLES pc, x

vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "a1"

a1 == /\ pc = "a1"
      /\ x' = 1
      /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
