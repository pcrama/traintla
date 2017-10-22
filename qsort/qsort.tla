----- MODULE qsort -----
EXTENDS Naturals, Sequences

qsort(x) == LET totLen = Len(x),
                pivot = p \in x : /\ Len({z \in x : z <= p}) * 2 >= totLen
                                  /\ Len({z \in x : z >= p}) * 2 >= totLen
            IN qsort({s \in x: s < pivot}) \o < pivot > \o qsort({b \in x: b > pivot})
