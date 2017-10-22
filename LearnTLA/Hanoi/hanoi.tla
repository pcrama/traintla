---- MODULE hanoi ----
EXTENDS TLC, Sequences, Integers

(* --algorithm hanoi
variables tower = << << 1, 2, 3, 4, 5 >>, <<>>, <<>> >>
define
  D == DOMAIN tower
end define
begin
while TRUE do
  assert tower[3] /= << 1, 2, 3, 4, 5 >>;
  with from \in { x \in D : tower[x] /= <<>> }
     , to \in { x \in D :
                   \/ tower[x] = <<>>
                   \/ Head(tower[from]) < Head(tower[x]) }
  do
    tower[to] := << Head(tower[from]) >> \o tower[to]
    || tower[from] := Tail(tower[from]);
  end with;
end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLE tower

(* define statement *)
D == DOMAIN tower


vars == << tower >>

Init == (* Global variables *)
        /\ tower = << << 1, 2, 3, 4, 5 >>, <<>>, <<>> >>

Next == /\ Assert(tower[3] /= << 1, 2, 3, 4, 5 >>, 
                  "Failure of assertion at line 11, column 3.")
        /\ \E from \in { x \in D : tower[x] /= <<>> }:
             \E to \in { x \in D :
                            \/ tower[x] = <<>>
                            \/ Head(tower[from]) < Head(tower[x]) }:
               tower' = [tower EXCEPT ![to] = << Head(tower[from]) >> \o tower[to],
                                      ![from] = Tail(tower[from])]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
====
