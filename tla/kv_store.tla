--------------------------- MODULE kv_store ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES 
    lru_recency, lru_kv, \* LRU imports
    kv, latency

vars == <<kv, latency>>

LATENCY == 100

LRU == INSTANCE lru

N == 4
KV == {"a", "b", "c", "d", "e", "f"}

Read(k) == 
    kv[k] 

Put(k, v) == 
    /\ kv' = [n \in DOMAIN kv \cup {k} |-> n]
    /\ latency' = LATENCY
    /\ LRU!Unchanged

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