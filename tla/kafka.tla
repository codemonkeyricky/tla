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
    /\ topic = [k \in Empty |-> 0] 
    /\ c_offset = 0 \* [p \in 0..P-1 |-> 0]
    /\ p_seq = 0

Produce == 
    /\ p_seq \notin DOMAIN topic 
    /\ p_seq' = (p_seq + 1) % N
    /\ topic' = topic @@ (p_seq :> p_seq)
    /\ UNCHANGED <<c_offset>>

Consume == 
    LET 
        k == c_offset
        v == topic[k]
        remove == (k :> v)
    IN 
        /\ Cardinality(DOMAIN topic) # 0
        /\ topic' = [i \in DOMAIN topic \ DOMAIN remove |-> topic[i]] 
        /\ c_offset' = (c_offset + 1) % N
        /\ UNCHANGED <<p_seq>>

\* Consume(p) == 
    \* LET 
        \* map == topic[p]
        \* size == Cardinality(map)
        \* v == map[c_offset[p]]
        \* remove == [c_offset[p] |-> v]
    \* IN 
        \* /\ map # {}
        \* /\ c_offset' = [c_offset EXCEPT ![p] = (c_offset[p] + 1) % N]
        \* /\ topic' = [topic EXCEPT ![p] = {}]
        \* /\ UNCHANGED <<p_seq>>
\* 
Next ==
    \/ Produce
    \/ Consume
    \* \/ \E p \in 0..P-1: 
    \*     Consume(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
\*   /\ WF_vars(Next)
=============================================================================