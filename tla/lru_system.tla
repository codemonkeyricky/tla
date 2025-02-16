--------------------------- MODULE lru_system ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLE kv, recency
vars == <<kv>>

LRU == INSTANCE lru

DataSet == 
    {"a", "b", "c", "d", "e", "f", "g", "h"}

\* vars == <<kv>>

\* \* N == 4
\* \* KV == {"a", "b", "c", "d", "e", "f"}

Init ==
    /\ LRU!Init 

Next ==
    \E d \in DataSet:
        LRU!Put(d, d)

Consistent == 
    \A d \in DataSet:
        LRU!Contains(d) => d = LRU!Get(d)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================