---- MODULE besttrade ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANT capital, fee

price_history == << << 17, 19 >>, << 9, 11 >>, << 16, 12 >>, << 15, 15 >>, << 16, 15 >> >>

MaxBy(Op(_), s) == { x \in s : LET OpX == Op(x) IN \A y \in s \ { x } : OpX >= Op(y) }

TradeBenefit(q, buy, sell) == q * (sell - buy) - 2 * fee

TradeOpportunities == {
    <<buy_at, sell_at>> \in (DOMAIN price_history) \X (DOMAIN price_history) :
    sell_at > buy_at }

CanBuy(price) ==
     CHOOSE x \in 0..(capital - 2 * fee) : /\ x * price <= (capital - 2 * fee)
                                           /\ (x + 1) * price > (capital - 2 * fee)

Trades == { LET price == price_history[buy_at][1] IN
            << CanBuy(price),
               price,
               buy_at,
               price_history[sell_at][2],
               sell_at >> :
            << buy_at, sell_at >> \in { << buy_at, sell_at >> \in TradeOpportunities :
                                        LET price == price_history[buy_at][1] IN
                                        TradeBenefit(CanBuy(price),
                                                     price,
                                                     price_history[sell_at][2]) > 0 }
          }

JudgeTrade(q) == TradeBenefit(q[1], q[2], q[4])

Spec == IF Trades = {}
        THEN PrintT("No trades at all")
        ELSE PrintT(MaxBy(JudgeTrade, Trades))

====
