---- MODULE multi_transfer ----
EXTENDS Naturals, TLC
(* --algorithm multi_transfer
variables alice_account = 10
        , bob_account = 9
        , total_accounts = alice_account + bob_account;
process Transfer \in 1..2
  variable money \in 1..20
begin
  T1: if alice_account >= money then
       alice_account := alice_account - money;
       bob_account := bob_account + money;
  end if;
end process
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, total_accounts, pc, money

vars == << alice_account, bob_account, total_accounts, pc, money >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 9
        /\ total_accounts = alice_account + bob_account
        (* Process Transfer *)
        /\ money \in [1..2 -> 1..20]
        /\ pc = [self \in ProcSet |-> "T1"]

T1(self) == /\ pc[self] = "T1"
            /\ IF alice_account >= money[self]
                  THEN /\ alice_account' = alice_account - money[self]
                       /\ bob_account' = bob_account + money[self]
                  ELSE /\ TRUE
                       /\ UNCHANGED << alice_account, bob_account >>
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << total_accounts, money >>

Transfer(self) == T1(self)

Next == (\E self \in 1..2: Transfer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
AccountsNotNegative == alice_account >= 0 /\ bob_account >= 0
\* MoneyNotNegative == money >= 0
MoneyTotalInvariant == alice_account + bob_account = total_accounts
====
