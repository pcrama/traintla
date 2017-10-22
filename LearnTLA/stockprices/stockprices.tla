---- MODULE stockprices ----
EXTENDS TLC, Integers, Sequences

CONSTANTS INITIAL_CAPITAL, FEE

(* --algorithm trading
variables price_hist = << << 10,  9 >>,
                          << 11, 10 >>,
                          << 15, 10 >>,
                          << 14, 11 >>,
                          << 13, 12 >>,
                          <<  9,  8 >>,
                          << 11,  9 >>,
                          << 14, 13 >> >>,
          capital = INITIAL_CAPITAL,
          market = 0,
          stocks = 0,
          temp = 0,
          buy_price = 0, \* From trader's perspective
          sell_price = 0; \* From trader's perspective
begin
    while price_hist /= <<>> do
      buy_price := Head(price_hist)[1];
      sell_price := Head(price_hist)[2];
      price_hist := Tail(price_hist);
      either
        skip;
      or
        if capital >= buy_price then
          with quantity \in { q \in 1..(capital - FEE) : q * buy_price + FEE <= capital } do
            market := market + quantity * buy_price + FEE;
            capital := capital - quantity * buy_price - FEE;
            stocks := stocks + quantity;
          end with;
        end if;
      or
        if stocks > 0 then
          market := market - stocks * sell_price + FEE;
          capital := capital + stocks * sell_price - FEE;
          stocks := 0;
        end if;
      end either;
    end while;
    assert capital <= INITIAL_CAPITAL;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES price_hist, capital, market, stocks, temp, buy_price, sell_price, 
          pc

vars == << price_hist, capital, market, stocks, temp, buy_price, sell_price, 
           pc >>

Init == (* Global variables *)
        /\ price_hist = << << 10,  9 >>,
                           << 11, 10 >>,
                           << 15, 10 >>,
                           << 14, 11 >>,
                           << 13, 12 >>,
                           <<  9,  8 >>,
                           << 11,  9 >>,
                           << 14, 13 >> >>
        /\ capital = INITIAL_CAPITAL
        /\ market = 0
        /\ stocks = 0
        /\ temp = 0
        /\ buy_price = 0
        /\ sell_price = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF price_hist /= <<>>
               THEN /\ buy_price' = Head(price_hist)[1]
                    /\ sell_price' = Head(price_hist)[2]
                    /\ price_hist' = Tail(price_hist)
                    /\ \/ /\ TRUE
                          /\ UNCHANGED <<capital, market, stocks>>
                       \/ /\ IF capital >= buy_price'
                                THEN /\ \E quantity \in { q \in 1..(capital - FEE) : q * buy_price' + FEE <= capital }:
                                          /\ market' = market + quantity * buy_price' + FEE
                                          /\ capital' = capital - quantity * buy_price' - FEE
                                          /\ stocks' = stocks + quantity
                                ELSE /\ TRUE
                                     /\ UNCHANGED << capital, market, stocks >>
                       \/ /\ IF stocks > 0
                                THEN /\ market' = market - stocks * sell_price' + FEE
                                     /\ capital' = capital + stocks * sell_price' - FEE
                                     /\ stocks' = 0
                                ELSE /\ TRUE
                                     /\ UNCHANGED << capital, market, stocks >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capital <= INITIAL_CAPITAL, 
                              "Failure of assertion at line 44, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << price_hist, capital, market, stocks, 
                                    buy_price, sell_price >>
         /\ temp' = temp

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

ClosedSystem == market + capital = INITIAL_CAPITAL
NoLoans == capital >= 0
====
