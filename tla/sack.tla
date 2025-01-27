x-------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, server_tx, client_rx, client_buffer, server_tx_ack, server_tx_limit, lost 

vars == <<network, server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack, lost>>

N == 16
W == 5
L == 4

ASSUME W * 2 < N
ASSUME L < W

Liveness == 
    server_tx = 0 ~> server_tx = N-1

Send == 
    \/ /\ server_tx # server_tx_limit
       /\ server_tx' = (server_tx + 1) % N
       /\ network' = network \cup {[dst |-> "client", seq |-> server_tx']}
       /\ UNCHANGED <<client_rx, client_buffer, server_tx_ack, server_tx_limit, lost>>

MinS(s) == 
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) == 
    CHOOSE x \in s: \A y \in s: x >= y

MaxIndex == 
    LET 
        upper == {x \in client_buffer : x > N - W}
        lower == {x \in client_buffer : x < W}
        maxv == IF upper # {} /\ lower # {} 
                THEN 
                    MaxS(lower)
                ELSE 
                    MaxS(client_buffer)
    IN 
        maxv

MinIndex == 
    LET 
        upper == {x \in client_buffer : x > N - W}
        lower == {x \in client_buffer : x < W}
        minv == IF upper # {} /\ lower # {} 
                THEN 
                    MinS(upper)
                ELSE 
                    MinS(client_buffer)
    IN 
        minv

Range == 
    IF MaxIndex >= MinIndex
    THEN
        MaxIndex - MinIndex + 1
    ELSE 
        MaxIndex + 1 + N - MinIndex

RemoveMessage(m, msgs) == 
    msgs \ {m}

AddMessage(m, msgs) == 
    msgs \cup {m}

ClientReceive(pp) == 
    /\ network' = RemoveMessage(pp, network)
    /\ client_buffer' = client_buffer \cup {pp.seq}
    /\ UNCHANGED <<server_tx, client_rx, server_tx_ack, server_tx_limit, lost>>

MergeReady == 
    /\ client_buffer # {}
    /\ (client_rx + 1) % N = MinIndex       \* contiguous with previous ack
    /\ Range = Cardinality(client_buffer)   \* combined is contiguous 

ClientAcknowledgement == 
    /\ client_buffer # {}
    /\ MergeReady 
    /\ client_buffer' = {}
    /\ client_rx' = MaxIndex
    /\ network' = AddMessage([dst |-> "server", type |-> "ack", ack |-> MaxIndex], network)
    /\ UNCHANGED <<server_tx, server_tx_ack, server_tx_limit, lost>>

RemoveStaleAck(ack, msgs) == 
    LET 
        acks == {(ack - k + N ) % N : k \in 1..W}
    IN 
        {m \in msgs : ~(m.dst = "server" /\ m.type = "ack" /\ m.ack \in acks)}

ServerReceive(pp) == 
    \/ /\ pp.type = "ack"
       /\ server_tx_ack' = pp.ack
       /\ server_tx_limit' = (pp.ack + W) % N
       /\ network' = RemoveStaleAck(pp.ack, RemoveMessage(pp, network))
       /\ UNCHANGED <<server_tx, client_rx, client_buffer, lost>>
    \/ /\ pp.type = "retransmit"
       /\ network' = AddMessage([dst |-> "client", seq |-> pp.seq], 
                                RemoveMessage(pp, network))
       /\ lost' = lost -1
       /\ UNCHANGED <<server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack>>

Receive(pp) ==
    \/ /\ pp.dst = "client"
       /\ ClientReceive(pp)
    \/ /\ pp.dst = "server"
       /\ ServerReceive(pp)
    
Drop(p) == 
    /\ lost # L
    /\ network' = RemoveMessage(p, network)
    /\ lost' = lost + 1
    /\ UNCHANGED <<server_tx, client_rx, client_buffer, server_tx_ack, server_tx_limit>>

Missing == 
    LET 
        full_seq == 
            IF MaxIndex >= client_rx+1 
            THEN 
                {x \in client_rx+1 .. MaxIndex : TRUE}
            ELSE 
                {x \in 0..MaxIndex : TRUE} \cup {x \in client_rx + 1..N-1 : TRUE}
        all_client_msgs == {m \in network: m.dst = "client"}
        all_client_seqs == {m.seq : m \in all_client_msgs}
        network_missing == full_seq \ all_client_seqs
        client_missing == full_seq \ client_buffer
        to_request == network_missing \intersect client_missing
    IN 
        to_request

ClientRetransmitRequest == 
    /\ ~MergeReady
    /\ client_buffer # {}
    /\ Missing # {}
    /\ network' = AddMessage([dst |-> "server", 
                              type |-> "retransmit",
                              seq |-> CHOOSE x \in Missing : TRUE],
                                network)
    /\ UNCHANGED <<server_tx, server_tx_limit, client_rx, client_buffer, server_tx_ack, lost>>

Init ==
    /\ network = {}
    /\ server_tx = 0
    /\ server_tx_limit = W
    /\ server_tx_ack = 0
    /\ client_rx = 0
    /\ client_buffer = {} 
    /\ lost = 0

Next == 
    \/ Send 
    \/ \E p \in network: 
        Receive(p)
    \/ ClientRetransmitRequest
    \/ ClientAcknowledgement
    \/ \E p \in network: 
        \/ /\p.dst = "client" 
           /\ Drop(p)
        \* \/ /\ p.dst = "server"
        \*    /\ p.type = "retransmit"
        \*    /\ Drop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ SF_vars(\E p \in network: p.dst = "client" /\ ClientReceive(p))
=============================================================================