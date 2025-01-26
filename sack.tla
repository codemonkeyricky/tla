--------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, seq_tx, seq_rx, buffer_rx, ack_tx

vars == <<network, seq_tx, seq_rx, buffer_rx, ack_tx>>

N == 8
WINDOW == 3

ASSUME WINDOW * 2 < N

Init ==
    /\ network = {}
    /\ seq_tx = 0
    /\ ack_tx = 0
    /\ seq_rx = 0
    /\ buffer_rx = {} 

Send == 
    /\ seq_tx = ack_tx
    /\ seq_tx' = (seq_tx + 1) % N 
    /\ network' = network \cup {[dst |-> "client", seq |-> seq_tx]}
    /\ UNCHANGED <<seq_rx, buffer_rx, ack_tx>>

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
           /\ seq_rx' = maxv2
           /\ network' = (network \{pp}) \cup {[dst |-> "server", ack |-> maxv2]} 
           /\ UNCHANGED <<seq_tx, ack_tx>>
        \/ /\ ready = FALSE
        \*    /\ Assert(0,"")
           /\ buffer_rx' = combined
           /\ network' = network \ {pp}
           /\ UNCHANGED <<seq_tx, seq_rx, ack_tx>>

ServerRx(pp) == 
    /\ ack_tx' = pp.ack
    /\ network' = network \ {pp}
    /\ UNCHANGED <<seq_tx, seq_rx, buffer_rx, ack_tx>>

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