---- MODULE ThreeFlags ----
EXTENDS TLC, Integers
(* --algorithm flags
variables flags \in [1..3 -> BOOLEAN]
        , next = TRUE;
begin
  while next do
    with f \in DOMAIN flags
       , n \in BOOLEAN
    do
      flags[f] := ~flags[f];
      next := n;
    end with;
  end while;
end algorithm; *)
(* initial implementation of algorithm flags
variables f1 \in BOOLEAN, f2 \in BOOLEAN, f3 \in BOOLEAN;
begin
  while TRUE do
    with f \in {f1, f2, f3} do
      either
        f := TRUE;
      or
        f := FALSE;
      end either;
    end with;
  end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES flags, next, pc

vars == << flags, next, pc >>

Init == (* Global variables *)
        /\ flags \in [1..3 -> BOOLEAN]
        /\ next = TRUE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF next
               THEN /\ \E f \in DOMAIN flags:
                         \E n \in BOOLEAN:
                           /\ flags' = [flags EXCEPT ![f] = ~flags[f]]
                           /\ next' = n
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << flags, next >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
AlwaysBoolean == flags[1] \in BOOLEAN /\ flags[2] \in BOOLEAN /\ flags[3] \in BOOLEAN
AtLeastOneTrue == flags[1] \/ flags[2] \/ flags[3]
====
