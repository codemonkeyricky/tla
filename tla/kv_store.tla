--------------------------- MODULE kv_store ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES 
    lru_recency, lru_kv, \* LRU imports
    kv, latency

vars == <<kv, latency>>

EVICT == 100
CACHED == 10

LRU == INSTANCE lru

N == 4
KV == {"a", "b", "c", "d", "e", "f"}

Put(k, v) == 
    IF LRU!Contains(k) THEN 
         /\ LRU!Put(k, v)
         /\ UNCHANGED  kv
         /\ latency = CACHED
    ELSE 
         /\ LRU!IsFull => kv' = kv @@ LRU!GetLeastRecent
         /\ LRU!Put(k, v)
         /\ latency = EVICT
\* 
Init ==
    /\ LRU!Init
    /\ kv = [k \in {} |-> 0]
    /\ latency = 0

Next ==
    \E k \in KV: 
        Put(k ,"v")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================