--------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, tx, rx, buffer_rx, tx_ack

vars == <<network, tx, rx, buffer_rx, tx_ack>>

N == 8
WINDOW == 3

ASSUME WINDOW * 2 < N

Init ==
    /\ network = {}
    /\ tx = 0
    /\ tx_ack = 0
    /\ rx = 0
    /\ buffer_rx = {} 

Send == 
    /\ tx = tx_ack
    /\ tx' = (tx + 1) % N 
    /\ network' = network \cup {[dst |-> "client", seq |-> tx']}
    /\ UNCHANGED <<rx, buffer_rx, tx_ack>>

MinS(s) == 
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) == 
    CHOOSE x \in s: \A y \in s: x >= y

ClientRx(pp) == 
    LET 
        p == pp.seq 
        dst == pp.dst
        combined == buffer_rx \cup {p}
        upper == {x \in combined : x > N - WINDOW}
        lower == {x \in combined : x < WINDOW - 1}
        maxv == MinS(combined) 
        minv == MaxS(combined)
        range == IF upper # {} /\ lower # {} 
                 THEN 
                    N - MinS(upper) + MaxS(lower)
                 ELSE 
                    maxv - minv + 1
        ready == range = Cardinality(combined)
        maxv2 == IF upper # {} /\ lower # {} 
                 THEN
                    MaxS(lower)
                 ELSE 
                    maxv
    IN 
        \/ /\ ready = TRUE
           /\ buffer_rx' = {}
           /\ rx' = maxv2
           /\ network' = (network \{pp}) \cup {[dst |-> "server", ack |-> maxv2]} 
           /\ UNCHANGED <<tx, tx_ack>>
        \/ /\ ready = FALSE
        \*    /\ Assert(0,"")
           /\ buffer_rx' = combined
           /\ network' = network \ {pp}
           /\ UNCHANGED <<tx, rx, tx_ack>>

ServerRx(pp) == 
    /\ tx_ack' = pp.ack
    /\ network' = network \ {pp}
    /\ UNCHANGED <<tx, rx, buffer_rx>>

Receive(pp) ==
    \/ /\ pp.dst = "client"
       /\ ClientRx(pp)
    \/ /\ pp.dst = "server"
       /\ ServerRx(pp)

Next == 
    \/ Send 
    \/ \E p \in network : 
        Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================