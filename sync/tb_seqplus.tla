----------------------------- MODULE tb_seqplus -----------------------------
EXTENDS TLC, seqplus

Seq1s == { << 0 >>, << 1 >>, << 2 >> }
Seq2s == { << 3, 4 >>, << 5, 6 >>, << 7, 8 >>, << 9, 10 >> }

_add(x, y) == x + y

SpecButLast == \A x \in Seq1s: \A y \in Seq2s: y = ButLast(y \o x)

SpecReduce == \A n \in 1..10: (n * (n + 1)) = 2 * Reduce(_add, 0, [ i \in 1..n |-> i ])

SpecZipWith == /\ ZipWith(_add, 101, <<>>, << 1 >>) = 101
               /\ ZipWith(_add, 101, << 1 >>, << 2 >>) = << 3 >>
               /\ ZipWith(_add, 101, << 1, 3 >>, << 2, 4 >>) = << 3, 7 >>
	       /\ ZipWith(_add, 101, << 1, 3, 6 >>, << 2, 4, 9 >>) = << 3, 7, 15 >>

SpecZip == /\ Zip(101, <<>>, << 1 >>) = 101
           /\ Zip(101, << 2, 3 >>, << 1 >>) = 101

Spec == /\ SpecReduce
	/\ SpecZipWith
	/\ SpecZip
	        \* /\ SpecButLast

=============================================================================