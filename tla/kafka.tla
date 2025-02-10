--------------------------- MODULE kafka ----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets
VARIABLES topic, p_seq, c_offset 
vars == <<topic, p_seq, c_offset>>

Consumers == {"c0"}
P == 2
N == 8

GetPart(p) == 
    p_seq % P

Empty == {}

Init ==
    /\ topic = [p \in 0..P-1 |-> [k \in Empty |-> 0]]
    /\ c_offset = [p \in 0..P-1 |-> p]
    /\ p_seq = 0

Produce == 
    /\ p_seq \notin DOMAIN topic[GetPart(p_seq)]
    /\ p_seq' = (p_seq + 1) % N
    /\ topic' = [topic EXCEPT ![GetPart(p_seq)] = topic[GetPart(p_seq)] @@ (p_seq :> p_seq)]
    /\ UNCHANGED <<c_offset>>

Consume(p) == 
    LET 
        k == c_offset[p]
        v == topic[p][k]
        remove == (k :> v)
    IN 
        /\ Cardinality(DOMAIN topic[p]) # 0
        /\ topic' = [topic EXCEPT ![p] = [i \in DOMAIN topic[p] \ DOMAIN remove |-> topic[p][i]]] 
        /\ c_offset' = [c_offset EXCEPT ![p] = (c_offset[p] + 2) % N]
        /\ UNCHANGED <<p_seq>>

Next ==
    \/ Produce
    \/ \E p \in 0..P-1: 
        Consume(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
\*   /\ WF_vars(Next)
=============================================================================