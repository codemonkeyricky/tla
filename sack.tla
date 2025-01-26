--------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, tx, rx, buffer_rx, tx_ack, tx_limit

vars == <<network, tx, tx_limit, rx, buffer_rx, tx_ack>>

N == 8
WINDOW == 2

ASSUME WINDOW * 2 < N

Init ==
    /\ network = {}
    /\ tx = 0
    /\ tx_limit = WINDOW
    /\ tx_ack = 0
    /\ rx = 0
    /\ buffer_rx = {} 

Send == 
    /\ tx # tx_limit
    /\ tx' = tx + 1
    /\ network' = network \cup {[dst |-> "client", seq |-> tx']}
    /\ UNCHANGED <<rx, buffer_rx, tx_ack, tx_limit>>

MinS(s) == 
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) == 
    CHOOSE x \in s: \A y \in s: x >= y

RemoveMessage(m, msgs) == 
    msgs \ {m}

AddMessage(m, msgs) == 
    msgs \cup {m}

ClientRx(pp) == 
    LET 
        p == pp.seq 
        dst == pp.dst
        combined == buffer_rx \cup {p}
        minv == MinS(combined) 
        maxv == MaxS(combined)
        range == maxv - minv + 1
        ready == 
            /\ rx + 1 = minv 
            /\ range = Cardinality(combined)
        network_wo_msg == network \ {pp}
    IN 
        \/ /\ ready = TRUE
           /\ buffer_rx' = {}
           /\ rx' = maxv
           /\ network' = AddMessage([dst |-> "server", 
                                     ack |-> maxv], 
                                        RemoveMessage(pp, network))
           /\ UNCHANGED <<tx, tx_ack, tx_limit>>
        \/ /\ ready = FALSE
           /\ buffer_rx' = combined
           /\ network' = network \ {pp}
           /\ UNCHANGED <<tx, rx, tx_ack, tx_limit>>

ServerRx(pp) == 
    \/  /\ pp.ack > tx_ack
        /\ tx_ack' = pp.ack
        /\ tx_limit' = (pp.ack + WINDOW) % N
        /\ network' = network \ {pp}
        /\ UNCHANGED <<tx, rx, buffer_rx>>
    \/  /\ pp.ack <= tx_ack
        /\ network' = network \ {pp}
        /\ UNCHANGED <<tx, rx, buffer_rx, tx_ack, tx_limit>>

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