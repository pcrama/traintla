---- MODULE hanoi_set ----
\* Implement the towers of Hanoi using sets instead of tuples

EXTENDS TLC, Sequences, Integers

min_set(s) == CHOOSE x \in s : (\A y \in s : x <= y)

(* --algorithm hanoi
variables tower = << { 1, 2, 3, 4, 5 }, {}, {} >>
define
  D == DOMAIN tower
end define
begin
while TRUE do
  assert tower[3] /= {1, 2, 3, 4, 5};
  with from \in { x \in D : tower[x] /= {} }
     , to \in { x \in D :
                   \/ tower[x] = {}
                   \/ min_set(tower[from]) < min_set(tower[x]) }
  do
    tower[to] := { min_set(tower[from]) } \union tower[to]
    || tower[from] := tower[from] \ { min_set(tower[from]) };
  end with;
end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLE tower

(* define statement *)
D == DOMAIN tower


vars == << tower >>

Init == (* Global variables *)
        /\ tower = << { 1, 2, 3, 4, 5 }, {}, {} >>

Next == /\ Assert(tower[3] /= {1, 2, 3, 4, 5}, 
                  "Failure of assertion at line 15, column 3.")
        /\ \E from \in { x \in D : tower[x] /= {} }:
             \E to \in { x \in D :
                            \/ tower[x] = {}
                            \/ min_set(tower[from]) < min_set(tower[x]) }:
               tower' = [tower EXCEPT ![to] = { min_set(tower[from]) } \union tower[to],
                                      ![from] = tower[from] \ { min_set(tower[from]) }]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
====
