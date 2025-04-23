---- MODULE GoState ----
EXTENDS Naturals, TLC

(*--algorithm TrafficLightAlgorithm
variables state = "Red";

begin
  main:
    while TRUE do
      if state = "Red" then
        state := "Green"
      elsif state = "Green" then
        state := "Yellow"
      elsif state = "Yellow" then
        state := "Red"
      end if;
      
      assert state \in {"Red", "Yellow", "Green"};
    end while;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "12cf62f3" /\ chksum(tla) = "42b2fbe3")
VARIABLE state

vars == << state >>

Init == (* Global variables *)
        /\ state = "Red"

Next == /\ IF state = "Red"
              THEN /\ state' = "Green"
              ELSE /\ IF state = "Green"
                         THEN /\ state' = "Yellow"
                         ELSE /\ IF state = "Yellow"
                                    THEN /\ state' = "Red"
                                    ELSE /\ TRUE
                                         /\ state' = state
        /\ Assert(state' \in {"Red", "Yellow", "Green"}, 
                  "Failure of assertion at line 19, column 7.")

Spec == Init /\ [][Next]_vars

\* Safety Property: state is always Red, Yellow, or Green
SafetyProperty == state \in {"Red", "Yellow", "Green"}

\* END TRANSLATION
====