--------------------------- MODULE lru ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES lru_kv, lru_recency

vars == <<lru_kv, lru_recency>>

N == 4

lru_kv == {"a", "b", "c", "d", "e", "f"}

Get(k) == 
    /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
    /\ UNCHANGED lru_kv

Contains(k) == 
    /\ k \in DOMAIN lru_kv 

Put(k, v) == 
    IF Len(lru_recency) # N THEN 
        IF k \in DOMAIN lru_kv THEN 
            /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
            /\ lru_kv' = [n \in DOMAIN kv \ {k} |-> n]
        ELSE 
            /\ lru_recency' = Append(lru_recency, k)
            /\ lru_kv' = [n \in DOMAIN kv \cup {k} |-> n]
    ELSE  \* Cardinality(lru_kv) = N 
        IF k \in DOMAIN lru_kv THEN 
            \* refresh
            /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
            /\ lru_kv' = [n \in DOMAIN kv \ {k} |-> kv[n]]
        ELSE 
            \* remove oldest
            /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # lru_recency[1]), k)
            /\ lru_kv' = [n \in (DOMAIN kv \cup {k}) \ {lru_recency[1]} |-> n]

Init ==
    /\ lru_kv = [k \in {} |-> 0]
    /\ lru_recency = <<>>

Unchanged == 
    /\ UNCHANGED <<lru_kv, lru_recency>>

Next ==
    \E k \in lru_kv: 
        Put(k ,"v")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================