----------------- MODULE singleFileModel -----------------
EXTENDS Naturals, Sequences, TLC

(* A file is represented as
 *
 * 1. Sequence of updates (see description below)
 * 2. Status (alive or deleted)
 *
 * An update is a sequence of
 *
 * 1. Timestamp (increasing, \in Nat)
 * 2. Host on which the update was initially made (\in Nat)
 * 3. Kind of update (create, edit, delete, merge)
 *)

(* Predicates *)

\* Type assertion for type invariants
IsFile(f) == /\ DOMAIN f = 1..2
             /\ f[2] \in { "deleted", "alive" }
             /\ LET updates == f[1]
                IN /\ \A idx \in DOMAIN updates: (
                          \A oth \in {x \in DOMAIN updates: x > idx}: (
                              \/ updates[oth][1] > updates[idx][1]
                              \/ /\ updates[oth][1] = updates[idx][1]
                                 /\ updates[oth][2] = updates[idx][2]))

\* Internal use
_AssertParams(file, timestamp, host) == 
    /\ Assert(/\ timestamp \in Nat \ {0}
             , "Only strictly positive timestamps, please")
    /\ Assert(/\ host \in Nat
             , "host must be a Nat")
    /\ Assert(DOMAIN file = {1, 2} => IsFile(file)
             , "file must be either <<>> (ignored) or an already existing file")

\* File isn't deleted?
FileExists(file) == file[2] = "alive"

(* Internal functions
 *
 * Put first to avoid having RECURSIVE statements, skip to next section... *)

RECURSIVE _merge_sequences_internal(_, _, _, _, _, _)

_end_of_seq(seq, from, len) ==
    IF from > len
       THEN <<>>
       ELSE [ i \in (1..(len - from + 1)) |-> seq[i + from - 1] ]

_first_of_first_and_recurse(hd_tl, other, ht_idx, ht_len, ot_idx, ot_len) ==
    << hd_tl[ht_idx] >>
    \o _merge_sequences_internal(hd_tl, other, ht_idx + 1, ht_len, ot_idx, ot_len)

_timestamp(x) == x[1]

_host(x) == x[2]

_merge_sequences_internal(left, right, lf_idx, lf_len, rg_idx, rg_len) ==
    IF lf_idx <= lf_len /\ rg_idx <= rg_len
       \* Neither sequences are exhausted continue merging
       THEN LET lf_elt == left[lf_idx]
                rg_elt == right[rg_idx]
                lf_time == _timestamp(lf_elt)
                rg_time == _timestamp(rg_elt)
                \* Try ordering by timestamp first
            IN IF lf_time < rg_time
                  THEN _first_of_first_and_recurse(
                           left, right, lf_idx, lf_len, rg_idx, rg_len)
                  ELSE IF lf_time > rg_time
                       THEN _first_of_first_and_recurse(
                                right, left, rg_idx, rg_len, lf_idx, lf_len)
                       ELSE LET lf_host == _host(lf_elt)
                                rg_host == _host(rg_elt)
                                \* Same timestamps, now try ordering by host
                            IN IF lf_host < rg_host
                               THEN _first_of_first_and_recurse(
                                        left, right, lf_idx, lf_len, rg_idx, rg_len)
                               ELSE IF lf_host > rg_host
                                    THEN _first_of_first_and_recurse(
                                             right, left, rg_idx, rg_len, lf_idx, lf_len)
                                    ELSE IF Assert(lf_elt = rg_elt,
                                                   "Entries should have been equal")
                                            THEN << lf_elt >>
                                                 \o _merge_sequences_internal(
                                                     left, right,
                                                     lf_idx + 1, lf_len,
                                                     rg_idx + 1, rg_len)
                                            ELSE << "NOTREACHED" >>
        \* At least one sequence is exhausted, return rest of other sequence
        ELSE IF lf_idx > lf_len
                THEN _end_of_seq(right, rg_idx, rg_len)
                ELSE _end_of_seq(left, lf_idx, lf_len)

\* Merge two sorted lists
_merge_sequences(left, right) ==
    _merge_sequences_internal(left, right, 1, Len(left), 1, Len(right))

RECURSIVE _sameContent(_, _, _, _, _, _)
_sameContent(a, b, a_idx, a_len, b_idx, b_len) ==
    \/ (a_idx > a_len \/ b_idx > b_len)
    \/ a[a_idx] = b[b_idx]
    \/ (a[a_idx][3] /= "edit" /\ _sameContent(a, b, a_idx + 1, a_len, b_idx, b_len))
    \/ (b[b_idx][3] /= "edit" /\ _sameContent(a, b, a_idx, a_len, b_idx + 1, b_len))

(* Operations on files *)

SameFile(a, b) ==
    \/ a[2] = "deleted" /\ a[2] = b[2] \* Avoid writing literal constant twice
    \/ /\ a[2] = "alive" /\ a[2] = b[2] \* Avoid writing literal constant twice
       /\ _sameContent(a[1], b[1], 1, Len(a[1]), 1, Len(b[1]))

Create(file, timestamp, host) ==
    IF _AssertParams(file, timestamp, host)
       THEN LET orig_content == IF IsFile(file) THEN file[1] ELSE <<>>
            IN << Append(orig_content, << timestamp, host, "create" >>), "alive" >>
       ELSE <<>>

Edit(file, timestamp, host) ==
    IF /\ _AssertParams(file, timestamp, host)
       /\ Assert(FileExists(file), "You must Create(file, ...) first")
       THEN LET orig == IF FileExists(file) THEN file ELSE Create(file, timestamp, host)
            IN << Append(orig[1], <<timestamp, host, "edit">>), orig[2] >>
       ELSE <<>>

Delete(file, timestamp, host) ==
    IF /\ _AssertParams(file, timestamp, host)
       /\ Assert(FileExists(file), "file is already deleted")
       THEN << Append(file[1], << timestamp, host, "delete" >>), "deleted" >>
       ELSE <<>>

Merge(file, timestamp, host, other_file, other_host) ==
    IF /\ _AssertParams(file, timestamp, host)
       /\ Assert(FileExists(file), "file is deleted")
       /\ Assert(FileExists(other_file), "other_file is deleted")
       THEN << _merge_sequences(file[1], other_file[1])
               \o << << timestamp, host, "merge", other_host >> >>
             , file[2] >>
       ELSE <<>>

ModificationTime(file) == IF /\ Assert(IsFile(file), "Needs a file")
                             /\ Assert(FileExists(file),
                                       "File doesn't exist -> no modification time")
                             THEN LET content == file[1]
                                      len == Len(content)
                                  IN content[len][1]
                             ELSE 0 \* NOTREACHED
==========================================================
