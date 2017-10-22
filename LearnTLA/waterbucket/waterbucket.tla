---- MODULE waterbucket ----
EXTENDS TLC, Naturals, Sequences

VOLUMES == << 4, 17, 18, 32 >>
MAX_WATER == 4 + 3 * 18 + 7
TARGET == 5
D == DOMAIN VOLUMES

Min(x, y) == IF x <= y THEN x ELSE y

RECURSIVE Sum(_)
Sum(x) == IF x = << >>
          THEN 0
          ELSE x[1] + Sum(Tail(x))

(* --algorithm buckets
variables volumes = << 0, 0, 0, 0 >>
        , consumed = 0
        , thrown_away = 0
        , xfer = 0;
begin
  while TRUE do
    assert { x \in D : volumes[x] = TARGET } = {};
    either
      \* Empty a bucket
      with x \in { x \in D : volumes[x] > 0 } do
        thrown_away := thrown_away + volumes[x];
        volumes[x] := 0;
      end with;
    or
      \* Fill a bucket
      with filled \in { x \in D : /\ volumes[x] < VOLUMES[x]
                                  /\ VOLUMES[x] - volumes[x] + consumed <= MAX_WATER } do
        xfer := VOLUMES[filled] - volumes[filled];
        volumes[filled] := VOLUMES[filled];
        consumed := consumed + xfer;
      end with;
    or
      \* Pour bucket `from' into `to'
      with from \in { x \in D : volumes[x] > 0 }
         , to \in { x \in D \ { from } : volumes[x] < VOLUMES[x] }
      do
        xfer := Min(VOLUMES[to] - volumes[to], volumes[from]);
        volumes[to] := volumes[to] + xfer || volumes[from] := volumes[from] - xfer;
      end with;
    end either
  end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES volumes, consumed, thrown_away, xfer

vars == << volumes, consumed, thrown_away, xfer >>

Init == (* Global variables *)
        /\ volumes = << 0, 0, 0, 0 >>
        /\ consumed = 0
        /\ thrown_away = 0
        /\ xfer = 0

Next == /\ Assert({ x \in D : volumes[x] = TARGET } = {}, 
                  "Failure of assertion at line 23, column 5.")
        /\ \/ /\ \E x \in { x \in D : volumes[x] > 0 }:
                   /\ thrown_away' = thrown_away + volumes[x]
                   /\ volumes' = [volumes EXCEPT ![x] = 0]
              /\ UNCHANGED <<consumed, xfer>>
           \/ /\ \E filled \in { x \in D : /\ volumes[x] < VOLUMES[x]
                                           /\ VOLUMES[x] - volumes[x] + consumed <= MAX_WATER }:
                   /\ xfer' = VOLUMES[filled] - volumes[filled]
                   /\ volumes' = [volumes EXCEPT ![filled] = VOLUMES[filled]]
                   /\ consumed' = consumed + xfer'
              /\ UNCHANGED thrown_away
           \/ /\ \E from \in { x \in D : volumes[x] > 0 }:
                   \E to \in { x \in D \ { from } : volumes[x] < VOLUMES[x] }:
                     /\ xfer' = Min(VOLUMES[to] - volumes[to], volumes[from])
                     /\ volumes' = [volumes EXCEPT ![to] = volumes[to] + xfer',
                                                   ![from] = volumes[from] - xfer']
              /\ UNCHANGED <<consumed, thrown_away>>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

NotTriviallyImpossible == ~(\/ MAX_WATER < TARGET
                            \/ { x \in D : VOLUMES[x] >= TARGET } = {})

LimitedSupply == consumed <= MAX_WATER

ClosedSystem == consumed = thrown_away + Sum(volumes)

TypesOK == /\ D = DOMAIN volumes
           /\ { x \in D : ~(/\ 0 <= volumes[x]
                            /\ volumes[x] <= VOLUMES[x]) } = {}
====
