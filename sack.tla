x-------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, tx, client_rx, client_buffer, tx_ack, tx_limit, lost 

vars == <<network, tx, tx_limit, client_rx, client_buffer, tx_ack, lost>>

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
    /\ lost = 0

Send == 
    \/ /\ tx # tx_limit
       /\ tx' = (tx + 1) % N
       /\ network' = network \cup {[dst |-> "client", seq |-> tx']}
       /\ UNCHANGED <<client_rx, client_buffer, tx_ack, tx_limit, lost>>
    \* \/ /\ lost = 0
    \*    /\ tx # tx_limit
    \*    /\ tx' = (tx + 1) % N
    \*    /\ lost' = 1
    \*    /\ UNCHANGED <<network, client_rx, client_buffer, tx_ack, tx_limit>>

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
    /\ network' = RemoveMessage(pp, network)
    /\ client_buffer' = client_buffer \cup {pp.seq}
    /\ UNCHANGED <<tx, client_rx, tx_ack, tx_limit, lost>>

Client == 
    LET 
        combined == client_buffer 
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
           /\ client_buffer # {}
           /\ ready = TRUE
           /\ client_buffer' = {}
           /\ client_rx' = maxv
           /\ network' = AddMessage([dst |-> "server", type |-> "ack", ack |-> maxv], network)
           /\ UNCHANGED <<tx, tx_ack, tx_limit, lost>>

RemoveStaleAck(ack, msgs) == 
    LET 
        acks == {(ack - k + N ) % N : k \in 1..WINDOW}
    IN 
        {m \in msgs : ~(m.dst = "server" /\ m.type = "ack" /\ m.ack \in acks)}

ServerRx(pp) == 
    \/ /\ pp.type = "ack"
       /\ tx_ack' = pp.ack
       /\ tx_limit' = (pp.ack + WINDOW) % N
       /\ network' = RemoveStaleAck(pp.ack, RemoveMessage(pp, network))
       /\ UNCHANGED <<tx, client_rx, client_buffer, lost>>
    \/ /\ pp.type = "retransmit"
       /\ network' = AddMessage([dst |-> "client", seq |-> pp.seq], 
                                RemoveMessage(pp, network))
       /\ lost' = 0
       /\ UNCHANGED <<tx, tx_limit, client_rx, client_buffer, tx_ack>>

Receive(pp) ==
    \/ /\ pp.dst = "client"
       /\ ClientRx(pp)
    \/ /\ pp.dst = "server"
       /\ ServerRx(pp)
    
Drop(p) == 
    /\ network' = RemoveMessage(p, network)
    /\ UNCHANGED <<tx, client_rx, client_buffer, tx_ack, tx_limit>>

ClientRetranReq == 
    LET 
        combined == client_buffer
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
        FullRange == 
            IF upper # {} /\ lower # {} 
            THEN 
                {x \in 0..maxv : TRUE} \cup {x \in client_rx + 1..N-1 : TRUE}
            ELSE 
                {x \in client_rx+1 ..maxv : TRUE}
        all_client_msgs == {m \in network: m.dst = "client"}
        all_client_seqs == {m.seq : m \in all_client_msgs}
        client_missing == FullRange \ combined
        network_missing == FullRange \ all_client_seqs
        to_request == network_missing \intersect client_missing
    IN 
        /\ client_buffer # {}
        /\ to_request # {}
        /\ network' = AddMessage([dst |-> "server", 
                                     type |-> "retransmit",
                                     seq |-> CHOOSE x \in to_request : TRUE],
                                       network)
        /\ UNCHANGED <<tx, tx_limit, client_rx, client_buffer, tx_ack, lost>>

Reset == 
    /\ network' = {}
    /\ tx' = 0
    /\ tx_limit' = WINDOW
    /\ tx_ack' = 0
    /\ client_rx' = 0
    /\ client_buffer' = {} 

Next == 
    \/ Send 
    \/ \E p \in network : 
        Receive(p)
    \/ ClientRetranReq
    \/ Client
    \* \/ \E p \in network : 
    \*     /\ p.dst = "client" 
    \*     /\ Drop(p)
    \* \/ /\ network = {} 
    \*    /\ Reset 

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================