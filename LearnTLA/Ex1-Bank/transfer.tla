---- MODULE transfer ----
EXTENDS Naturals, TLC
(* --algorithm transfer
variables alice_account = 10
        , bob_account = 9
        , money \in 1..20
        , total_accounts = alice_account + bob_account;
begin
Transfer: if alice_account >= money then
    A: alice_account := alice_account - money;
       bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;
   assert bob_account >= 0;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, total_accounts, pc

vars == << alice_account, bob_account, money, total_accounts, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 9
        /\ money \in 1..20
        /\ total_accounts = alice_account + bob_account
        /\ pc = "Transfer"

Transfer == /\ pc = "Transfer"
            /\ IF alice_account >= money
                  THEN /\ pc' = "A"
                  ELSE /\ pc' = "C"
            /\ UNCHANGED << alice_account, bob_account, money, total_accounts >>

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << money, total_accounts >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 13, column 4.")
     /\ Assert(bob_account >= 0, 
               "Failure of assertion at line 14, column 4.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money, total_accounts >>

Next == Transfer \/ A \/ C
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
MoneyNotNegative == money >= 0
MoneyTotalInvariant == alice_account + bob_account = total_accounts
====
