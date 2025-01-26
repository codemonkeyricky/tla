x-------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, server_tx, client_rx, client_buffer, server_tx_ack, server_tx_limit, lost 

vars == <<network, server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack, lost>>

N == 8
WINDOW == 3

ASSUME WINDOW * 2 < N

Init ==
    /\ network = {}
    /\ server_tx = 0
    /\ server_tx_limit = WINDOW
    /\ server_tx_ack = 0
    /\ client_rx = 0
    /\ client_buffer = {} 
    /\ lost = 0

Send == 
    \/ /\ server_tx # server_tx_limit
       /\ server_tx' = (server_tx + 1) % N
       /\ network' = network \cup {[dst |-> "client", seq |-> server_tx']}
       /\ UNCHANGED <<client_rx, client_buffer, server_tx_ack, server_tx_limit, lost>>
    \* \/ /\ lost = 0
    \*    /\ server_tx # server_tx_limit
    \*    /\ server_tx' = (server_tx + 1) % N
    \*    /\ lost' = 1
    \*    /\ UNCHANGED <<network, client_rx, client_buffer, server_tx_ack, server_tx_limit>>

Liveness == 
    server_tx = 0 ~> server_tx = N-1

MinS(s) == 
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) == 
    CHOOSE x \in s: \A y \in s: x >= y

MaxIndex == 
    LET 
        upper == {x \in client_buffer : x > N - WINDOW}
        lower == {x \in client_buffer : x < WINDOW}
        maxv == IF upper # {} /\ lower # {} 
                THEN 
                    MaxS(lower)
                ELSE 
                    MaxS(client_buffer)
    IN 
        maxv

MinIndex == 
    LET 
        upper == {x \in client_buffer : x > N - WINDOW}
        lower == {x \in client_buffer : x < WINDOW}
        minv == IF upper # {} /\ lower # {} 
                THEN 
                    MinS(upper)
                ELSE 
                    MinS(client_buffer)
    IN 
        minv

RemoveMessage(m, msgs) == 
    msgs \ {m}

AddMessage(m, msgs) == 
    msgs \cup {m}

ClientRx(pp) == 
    /\ network' = RemoveMessage(pp, network)
    /\ client_buffer' = client_buffer \cup {pp.seq}
    /\ UNCHANGED <<server_tx, client_rx, server_tx_ack, server_tx_limit, lost>>

Range == 
    IF MaxIndex > MinIndex
    THEN
        MaxIndex - MinIndex + 1
    ELSE 
        MinIndex + 1 + N - MaxIndex

MergeReady == 
    /\ client_buffer # {}
    /\ (client_rx + 1) % N = MinIndex       \* contiguous with previous ack
    /\ Range = Cardinality(client_buffer)   \* combined is contiguous 

Client == 
    /\ client_buffer # {}
    /\ MergeReady 
    /\ client_buffer' = {}
    /\ client_rx' = MaxIndex
    /\ network' = AddMessage([dst |-> "server", type |-> "ack", ack |-> MaxIndex], network)
    /\ UNCHANGED <<server_tx, server_tx_ack, server_tx_limit, lost>>

RemoveStaleAck(ack, msgs) == 
    LET 
        acks == {(ack - k + N ) % N : k \in 1..WINDOW}
    IN 
        {m \in msgs : ~(m.dst = "server" /\ m.type = "ack" /\ m.ack \in acks)}

ServerRx(pp) == 
    \/ /\ pp.type = "ack"
       /\ server_tx_ack' = pp.ack
       /\ server_tx_limit' = (pp.ack + WINDOW) % N
       /\ network' = RemoveStaleAck(pp.ack, RemoveMessage(pp, network))
       /\ UNCHANGED <<server_tx, client_rx, client_buffer, lost>>
    \/ /\ pp.type = "retransmit"
       /\ network' = AddMessage([dst |-> "client", seq |-> pp.seq], 
                                RemoveMessage(pp, network))
       /\ lost' = 0
       /\ UNCHANGED <<server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack>>

Receive(pp) ==
    \/ /\ pp.dst = "client"
       /\ ClientRx(pp)
    \/ /\ pp.dst = "server"
       /\ ServerRx(pp)
    
Drop(p) == 
    /\ network' = RemoveMessage(p, network)
    /\ UNCHANGED <<server_tx, client_rx, client_buffer, server_tx_ack, server_tx_limit>>

Missing == 
    LET 
        full_seq == 
            IF MaxIndex < MinIndex 
            THEN 
                {x \in 0..MaxIndex : TRUE} \cup {x \in client_rx + 1..N-1 : TRUE}
            ELSE 
                {x \in client_rx+1 ..MaxIndex : TRUE}
        all_client_msgs == {m \in network: m.dst = "client"}
        all_client_seqs == {m.seq : m \in all_client_msgs}
        client_missing == full_seq \ client_buffer
        network_missing == full_seq \ all_client_seqs
        to_request == network_missing \intersect client_missing
    IN 
        to_request

ClientRetranReq == 
    \/ /\ ~MergeReady
       /\ client_buffer # {}
       /\ Missing # {}
       /\ network' = AddMessage([dst |-> "server", 
                                 type |-> "retransmit",
                                 seq |-> CHOOSE x \in Missing : TRUE],
                                   network)
       /\ UNCHANGED <<server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack, lost>>
    \* \/ /\ ~MergeReady
    \*    /\ network = {}
    \*    /\ network' = AddMessage([dst |-> "server", 
    \*                              type |-> "retransmit",
    \*                              seq |-> (client_rx + 1) % N],
    \*                                network)
    \*    /\ UNCHANGED <<server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack, lost>>

Reset == 
    /\ network' = {}
    /\ server_tx' = 0
    /\ server_tx_limit' = WINDOW
    /\ server_tx_ack' = 0
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