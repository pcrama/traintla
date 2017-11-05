------------------------------ MODULE seqplus ------------------------------
EXTENDS Sequences, Naturals

ButLast(s) == IF Len(s) > 1
                 THEN [ i \in 1..Len(s) - 1 |-> s[i] ]
                 ELSE <<>>

Reverse(s) == LET N == Len(s) IN [ i \in 1..N |-> s[N - i + 1] ]

RECURSIVE Filter(_, _), _reduce(_, _, _, _, _)

_reduce(Op(_, _), def, seq, idx, len) ==
  IF idx > len
     THEN def
     ELSE Op(seq[idx], _reduce(Op, def, seq, idx + 1, len))

Reduce(Op(_, _), def, seq) == _reduce(Op, def, seq, 1, Len(seq))

ZipWith(Op(_, _), err, left, right) ==
    LET lf_len == Len(left)
        rg_len == Len(right)
    IN IF lf_len = rg_len
          THEN [ i \in 1..lf_len |-> Op(left[i], right[i]) ]
          ELSE err

_cons(x, y) == <<x, y>>

Zip(err, left, right) == ZipWith(_cons, err, left, right)

Filter(Pred(_), s) ==
    IF s = <<>>
       THEN <<>>
       ELSE LET hd == Head(s)
                tl == Filter(Pred, Tail(s))
            IN IF Pred(hd)
                  THEN << hd >> \o tl
                  ELSE tl

============================================================================