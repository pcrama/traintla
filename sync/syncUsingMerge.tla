------------------- MODULE syncUsingMerge ------------------
EXTENDS TLC, Sequences, Naturals, singleFileModel

CONSTANT MAX_STEPS, MAX_HOSTS
ASSUME /\ MAX_STEPS \in Nat \ {0, 1}
       /\ MAX_HOSTS \in Nat \ {0, 1}

(* Synchronize from a to b: if a is newer, overwrite b *)
SyncByMerge(a, b, timestamp, host_a, host_b) ==
    IF FileExists(a)
       THEN IF FileExists(b)
               THEN Merge(b, timestamp, host_b, a, host_a)
               ELSE a
       ELSE b

(* --algorithm modifyAndSync
variables files = [ i \in 1..MAX_HOSTS |-> Create(<<>>, 1, i) ]
        , ref = Create(<<>>, 1, MAX_HOSTS + 1)
        , t = 1
        , syncLeft = Len(files)
        , syncRight = 1
        , story = <<>>;
begin
  modifyAndPartialSync:
    while t <= MAX_STEPS do
      t := t + 1;
      with host \in DOMAIN files do
        either
          \* Synchronize from any other host to current host
          with otherHost \in DOMAIN files \ { host } do
            files[host] := SyncByMerge(
                files[otherHost], files[host], t, otherHost, host);
            story := Append(story, << otherHost, "->", host >>);
          end with;
        or
          \* Edit/Delete/Create file
          if FileExists(files[host]) then
            \* either
              files[host] := Edit(files[host], t, t);
              ref := Edit(ref, t, t);
              story := Append(story, << "edit", host, t >>);
            \* or
            (*  files[host] := Delete(files[host], t, host);
              story := story \o << "del", host, t >>;
              ref := Delete(ref, t, host) *)
            \* end either;
          else
            files[host] := Create(files[host], t, host);
            story := story \o << "create", host, t >>;
          end if;
        or
          skip;
        end either;
      end with;
    end while;
  fullSyncLeft:
    while syncLeft > 1 do
      t := t + 1;
      files[syncLeft - 1] := SyncByMerge(
          files[syncLeft], files[syncLeft - 1], t, syncLeft, syncLeft - 1);
      syncLeft := syncLeft - 1;
    end while;
  fullSyncRight:
    while syncRight < Len(files) do
      t := t + 1;
      files[syncRight + 1] := SyncByMerge(
          files[syncRight], files[syncRight + 1], t, syncRight, syncRight + 1);
      syncRight := syncRight + 1;
    end while;
  assert \A i \in DOMAIN files \ {1}: SameFile(files[1], files[i])
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES files, ref, t, syncLeft, syncRight, story, pc

vars == << files, ref, t, syncLeft, syncRight, story, pc >>

Init == (* Global variables *)
        /\ files = [ i \in 1..MAX_HOSTS |-> Create(<<>>, 1, i) ]
        /\ ref = Create(<<>>, 1, MAX_HOSTS + 1)
        /\ t = 1
        /\ syncLeft = Len(files)
        /\ syncRight = 1
        /\ story = <<>>
        /\ pc = "modifyAndPartialSync"

modifyAndPartialSync == /\ pc = "modifyAndPartialSync"
                        /\ IF t <= MAX_STEPS
                              THEN /\ t' = t + 1
                                   /\ \E host \in DOMAIN files:
                                        \/ /\ \E otherHost \in DOMAIN files \ { host }:
                                                /\ files' = [files EXCEPT ![host] =            SyncByMerge(
                                                                                    files[otherHost], files[host], t', otherHost, host)]
                                                /\ story' = Append(story, << otherHost, "->", host >>)
                                           /\ ref' = ref
                                        \/ /\ IF FileExists(files[host])
                                                 THEN /\ files' = [files EXCEPT ![host] = Edit(files[host], t', t')]
                                                      /\ ref' = Edit(ref, t', t')
                                                      /\ story' = Append(story, << "edit", host, t' >>)
                                                 ELSE /\ files' = [files EXCEPT ![host] = Create(files[host], t', host)]
                                                      /\ story' = story \o << "create", host, t' >>
                                                      /\ ref' = ref
                                        \/ /\ TRUE
                                           /\ UNCHANGED <<files, ref, story>>
                                   /\ pc' = "modifyAndPartialSync"
                              ELSE /\ pc' = "fullSyncLeft"
                                   /\ UNCHANGED << files, ref, t, story >>
                        /\ UNCHANGED << syncLeft, syncRight >>

fullSyncLeft == /\ pc = "fullSyncLeft"
                /\ IF syncLeft > 1
                      THEN /\ t' = t + 1
                           /\ files' = [files EXCEPT ![syncLeft - 1] =                    SyncByMerge(
                                                                       files[syncLeft], files[syncLeft - 1], t', syncLeft, syncLeft - 1)]
                           /\ syncLeft' = syncLeft - 1
                           /\ pc' = "fullSyncLeft"
                      ELSE /\ pc' = "fullSyncRight"
                           /\ UNCHANGED << files, t, syncLeft >>
                /\ UNCHANGED << ref, syncRight, story >>

fullSyncRight == /\ pc = "fullSyncRight"
                 /\ IF syncRight < Len(files)
                       THEN /\ t' = t + 1
                            /\ files' = [files EXCEPT ![syncRight + 1] =                     SyncByMerge(
                                                                         files[syncRight], files[syncRight + 1], t', syncRight, syncRight + 1)]
                            /\ syncRight' = syncRight + 1
                            /\ pc' = "fullSyncRight"
                       ELSE /\ Assert(\A i \in DOMAIN files \ {1}: SameFile(files[1], files[i]), 
                                      "Failure of assertion at line 70, column 3.")
                            /\ pc' = "Done"
                            /\ UNCHANGED << files, t, syncRight >>
                 /\ UNCHANGED << ref, syncLeft, story >>

Next == modifyAndPartialSync \/ fullSyncLeft \/ fullSyncRight
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeInvariants == /\ \A f \in DOMAIN files: IsFile(files[f])
                  /\ IsFile(ref)

syncToLeft(Op(_, _), s) ==
  IF Len(s) = 1
     THEN s[1]
     ELSE IF Len(s) = 2
             THEN << Op(s[2], s[1]), s[2] >>
             ELSE Assert(FALSE, "syncToLeft not implemented fully") \* Op(syncToLeft(Op, Tail(s)), s[1])

syncToRight(Op(_, _), s) ==
  IF Len(s) = 1
     THEN s[1]
     ELSE IF Len(s) = 2
             THEN << s[1], Op(s[1], s[2]) >>
             ELSE Assert(FALSE, "syncToRight not implemented fully") \* Op(syncToLeft(Op, Tail(s)), s[1])

currySync(a, b) == SyncByMerge(a, b, t, 1, 2)

NoUpdateLost == LET synced == syncToLeft(currySync, syncToRight(currySync, files))
                IN \/ \A i \in DOMAIN files : SameFile(synced[i], ref)
                   \/ Trace2(story, FALSE)
============================================================
