--------------------------- MODULE kv_store ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES 
    lru_recency, lru_kv, lru_size,  \* LRU imports
    kv, latency                     \* local

vars == <<kv, latency>>

EVICT == 100
CACHED == 10

LRU_SIZE == 4

LRU == INSTANCE lru

\* N == 4
KV == {"a", "b", "c", "d", "e", "f"}

Read(k) == 
    IF LRU!Contains(k) THEN 
        lru_kv[k]
    ELSE 
        kv[k]

Touch(k) == 
    IF LRU!Contains(k) THEN 
        /\ LRU!Touch(k)
        /\ latency' = CACHE
    ELSE \* key not in LRU
        /\ LRU!Put(k, kv[k])
        /\ latency' = EVICT

Put(k, v) == 
    IF LRU!Contains(k) THEN 
         /\ LRU!Put(k, v)
         /\ UNCHANGED kv
         /\ latency' = CACHED
    ELSE \* LRU does not contain k
        /\ IF LRU!IsFull THEN 
                LET 
                    pair == LRU!GetLeastRecent
                    key == CHOOSE only \in DOMAIN pair: TRUE
                    value == pair[key]
                IN 
                    /\ kv' = [x \in DOMAIN kv \cup {key} |-> IF x = key THEN value ELSE kv[x]]
            ELSE 
                UNCHANGED kv 
        /\ LRU!Put(k, v)
        /\ latency' = EVICT

\* 
Init ==
    /\ LRU!Init(LRU_SIZE)
    /\ kv = <<>>
    /\ latency = 0

Next ==
    \E k \in KV: 
        Put(k ,"v")

Safety ==
    /\ LRU!Consistent

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================