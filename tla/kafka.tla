--------------------------- MODULE kafka ----------------------------
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES topic, p_seq, c_offset 
vars == <<topic, p_seq, c_offset>>

Consumers == {"c0"}
P == 2
N == 8

GetPart(p) == 
    p_seq % P

Init ==
    /\ topic = [p \in 0..P-1 |-> <<>>]   \* topic split into two partitions
    /\ c_offset = [p \in 0..P-1 |-> 0]
    /\ p_seq = 0

Produce == 
    /\ Len(topic[c_offset[GetPart(p_seq)]]) < 4
    /\ p_seq' = (p_seq + 1) % N
    /\ topic' = [topic EXCEPT ![p_seq % 2] = Append(topic[p_seq % 2], p_seq)]
    /\ UNCHANGED <<c_offset>>

Consume(p) == 
    /\ Len(topic[p]) # 0
    /\ c_offset' = [c_offset EXCEPT ![p] = (c_offset[p] + 1) % N]
    /\ topic' = [topic EXCEPT ![p] = Tail(topic[c_offset[p]])]
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