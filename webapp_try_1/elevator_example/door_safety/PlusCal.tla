---- MODULE DoorControl ----
EXTENDS Naturals, TLC

CONSTANTS in, none

(* --algorithm DoorControlAlgorithm
variables
  doorOpen = FALSE;
  direction = none;

begin
  main:
    while TRUE do
      if doorOpen = FALSE then
        doorOpen := TRUE;
        direction := in;
      else
        doorOpen := FALSE;
        direction := none;
      end if;
      assert (doorOpen = TRUE) => (direction = in);
      assert (doorOpen = FALSE) => (direction = none);
    end while;
end algorithm; *)
====