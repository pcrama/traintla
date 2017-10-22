----------------- MODULE singleFileModel -----------------
EXTENDS Naturals, Sequences, TLC

(* Operations on files *)
Create(timestamp) == IF Assert(timestamp > 0, "Only strictly positive timestamps, please")
                     THEN << <<>>, timestamp, "alive" >>
                     ELSE <<>>

FileExists(file) == file[3] = "alive"

Edit(file, content, timestamp) ==
    LET orig == IF FileExists(file) THEN file ELSE Create(timestamp)
    IN << orig[1] \o << content >>, timestamp, orig[3] >>

Delete(file) == << file[1], file[2], "deleted" >>

\* Type assertion for type invariants
IsFile(f) == DOMAIN f = 1..3 /\ f[2] >= 0 /\ f[3] \in { "deleted", "alive" }
==========================================================
