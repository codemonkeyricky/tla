--------------------------- MODULE sack ----------------------------
EXTENDS Integers, Naturals, TLC, FiniteSets
VARIABLES 
    network, seq_tx, seq_rx, buffer_rx

vars == <<network, seq_tx, seq_rx, buffer_rx>>

N == 8
WINDOW == 3

ASSUME WINDOW * 2 < N

Init ==
    /\ network = {}
    /\ seq_tx = 0
    /\ seq_rx = 0
    /\ buffer_rx = {} 

Send == 
    /\ network' = network \cup {seq_tx}
    /\ seq_tx' = (seq_tx + 1) % N 
    /\ UNCHANGED <<seq_rx, buffer_rx>>

MinS(s) == 
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) == 
    CHOOSE x \in s: \A y \in s: x >= y

Receive(p) ==
    LET 
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
           /\ network' = network \ {p}
           /\ UNCHANGED seq_tx
        \/ /\ ready = FALSE
           /\ buffer_rx' = combined
           /\ network' = network \ {p}
           /\ UNCHANGED <<seq_tx, seq_rx>>

Next == 
    \/ Send 
    \/ \E p \in network : 
        Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================