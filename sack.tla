x-------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, tx, client_rx, client_buffer, tx_ack, tx_limit

vars == <<network, tx, tx_limit, client_rx, client_buffer, tx_ack>>

N == 8
WINDOW == 3

ASSUME WINDOW * 2 < N

Init ==
    /\ network = {}
    /\ tx = 0
    /\ tx_limit = WINDOW
    /\ tx_ack = 0
    /\ client_rx = 0
    /\ client_buffer = {} 

Send == 
    /\ tx # tx_limit
    /\ tx' = (tx + 1) % N
    /\ network' = network \cup {[dst |-> "client", seq |-> tx']}
    /\ UNCHANGED <<client_rx, client_buffer, tx_ack, tx_limit>>

Liveness == 
    tx = 0 ~> tx = N-1

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
        combined == client_buffer \cup {p}
        upper == {x \in combined : x > N - WINDOW}
        lower == {x \in combined : x < WINDOW}
        range == IF upper # {} /\ lower # {} 
                 THEN 
                    N - MinS(upper) + MaxS(lower) + 1
                 ELSE 
                    MaxS(combined) - MinS(combined) + 1
        minv == IF upper # {} /\ lower # {} 
                THEN 
                    MinS(upper)
                ELSE 
                    MinS(combined)
        maxv == IF upper # {} /\ lower # {} 
                THEN 
                    MaxS(lower)
                ELSE 
                    MaxS(combined)
        ready == 
            /\ (client_rx + 1) % N = minv       \* contiguousu with previous ack
            /\ range = Cardinality(combined)    \* combined is contiguous 
    IN 
        \/ /\ ready = TRUE
           /\ client_buffer' = {}
           /\ client_rx' = maxv
           /\ network' = AddMessage([dst |-> "server", 
                                     ack |-> maxv], 
                                        RemoveMessage(pp, network))
           /\ UNCHANGED <<tx, tx_ack, tx_limit>>
        \/ /\ ready = FALSE
           /\ client_buffer' = combined
           /\ network' = network \ {pp}
           /\ UNCHANGED <<tx, client_rx, tx_ack, tx_limit>>

RemoveStaleAck(ack, msgs) == 
    LET 
        acks == {(ack - k + N ) % N : k \in 1..WINDOW}
    IN 
        {m \in msgs : ~(m.dst = "server" /\ m.ack \in acks)}

ServerRx(pp) == 
    /\ tx_ack' = pp.ack
    /\ tx_limit' = (pp.ack + WINDOW) % N
    /\ network' = RemoveStaleAck(pp.ack, RemoveMessage(pp, network))
    /\ UNCHANGED <<tx, client_rx, client_buffer>>

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
  /\ WF_vars(Next)
=============================================================================