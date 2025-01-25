--------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, seq_tx, seq_rx, buffer_rx

vars == <<network, seq_tx, seq_rx, buffer_rx>>

N == 8

Init ==
    /\ network = {}
    /\ seq_tx = 0
    /\ seq_rx = 0
    /\ buffer_rx = {} 

Send == 
    /\ network' = network \cup {seq_tx}
    /\ seq_tx' = (seq_tx + 1) % N 
    /\ UNCHANGED <<seq_rx, buffer_rx>>

Receive(p) ==
    LET 
        combined == buffer_rx \cup {p}
        max_v == CHOOSE x \in combined : \A y \in combined : x >= y
        min_v == CHOOSE x \in combined : \A y \in combined : x <= y
        ready == max_v - min_v = Cardinality(combined)
    IN 
        \/ /\ ready
           /\ buffer_rx' = {}
           /\ seq_rx' = max_v
           /\ network' = network \ {p}
           /\ UNCHANGED seq_tx
        \/ /\ ready = FALSE
           /\ buffer_rx' = combined
           /\ UNCHANGED <<network, seq_tx, seq_rx>>

Next == 
    \/ Send 
    \/ \E p \in network : 
        Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================