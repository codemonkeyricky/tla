--------------------------- MODULE kafka ----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets
VARIABLES topic, p_seq, p_offset, c_log, c_index
vars == <<topic, p_seq, p_offset>>

Consumers == {"c0"}
P == 2
N == 8

GetPart(p) == 
    p_seq % P

Empty == {}

Init ==
    /\ topic = [p \in 0..P-1 |-> [k \in Empty |-> 0]]
    /\ p_offset = [p \in 0..P-1 |-> p]
    /\ p_seq = 0
    /\ c_log = {}
    /\ c_index = 0

Produce == 
    /\ p_seq \notin DOMAIN topic[GetPart(p_seq)]
    /\ p_seq' = (p_seq + 1) % N
    /\ topic' = [topic EXCEPT ![GetPart(p_seq)] = topic[GetPart(p_seq)] @@ (p_seq :> p_seq)]
    /\ UNCHANGED <<p_offset, c_log, c_index>>

Consume(p) == 
    LET 
        k == p_offset[p]
        v == topic[p][k]
        remove == (k :> v)
    IN 
        /\ Cardinality(DOMAIN topic[p]) # 0
        /\ topic' = [topic EXCEPT ![p] = [i \in DOMAIN topic[p] \ DOMAIN remove |-> topic[p][i]]] 
        /\ p_offset' = [p_offset EXCEPT ![p] = (p_offset[p] + 2) % N]
        /\ c_log' = c_log \cup {v}
        /\ UNCHANGED <<p_seq, c_index>>

Flush == 
    /\ c_index \in c_log
    /\ c_log' = c_log \ {c_index}
    /\ c_index' = (c_index + 1)
    /\ UNCHANGED <<topic, p_seq, p_offset>>

Next ==
    \/ Produce
    \/ \E p \in 0..P-1: 
        Consume(p)
    \/ Flush

Spec ==
  /\ Init
  /\ [][Next]_vars
\*   /\ WF_vars(Next)
=============================================================================