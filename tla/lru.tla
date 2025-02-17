--------------------------- MODULE lru ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES lru_kv, lru_recency

vars == <<lru_kv, lru_recency>>

N == 4

KV == {"a", "b", "c", "d", "e", "f"}

Get(k) == 
    /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
    /\ UNCHANGED lru_kv

Contains(k) == 
    /\ k \in DOMAIN lru_kv 

IsFull == 
    Len(lru_recency) = N

GetLeastRecent == 
    LET 
        k == Head(lru_recency)
        v == lru_kv[k]
    IN 
        [kk \in {k} |-> v]

Put(k, v) == 
        IF k \in DOMAIN lru_kv THEN 
            /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
            /\ lru_kv' = [n \in DOMAIN lru_kv |-> IF n = k THEN v ELSE lru_kv[n]]
        ELSE 
            IF Len(lru_recency) # N THEN 
                /\ lru_recency' = Append(lru_recency, k)
                /\ lru_kv' = [n \in DOMAIN lru_kv \cup {k} |-> n]
            ELSE 
                \* remove oldest
                /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # lru_recency[1]), k)
                /\ lru_kv' = [n \in (DOMAIN lru_kv \cup {k}) \ {lru_recency[1]} |-> n]

Init ==
    /\ lru_kv = [k \in {} |-> 0]
    /\ lru_recency = <<>>

Unchanged == 
    /\ UNCHANGED <<lru_kv, lru_recency>>

Next ==
    \E k \in KV: 
        /\ Put(k ,"v")
        \* /\ PrintT(Cardinality(DOMAIN lru_recency))
        \* /\ PrintT(Cardinality(DOMAIN lru_kv))

Consistent ==
    /\ Cardinality(DOMAIN lru_recency) = Cardinality(DOMAIN lru_kv)
    \* 1 = 2

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================