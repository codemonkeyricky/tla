--------------------------- MODULE lru ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES lru_kv, lru_recency, lru_size

vars == <<lru_kv, lru_recency, lru_size>>

KV == {"a", "b", "c", "d", "e", "f"}

Touch(k) == 
    /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
    /\ UNCHANGED <<lru_kv, lru_size>>

Contains(k) == 
    /\ k \in DOMAIN lru_kv 

IsFull == 
    Len(lru_recency) = lru_size

GetLeastRecent == 
    LET 
        k == Head(lru_recency)
        v == lru_kv[k]
    IN 
        [kk \in {k} |-> v]

Put(k, v) == 
    IF k \in DOMAIN lru_kv THEN 
        \* replace
        /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # k), k)
        /\ lru_kv' = [n \in DOMAIN lru_kv |-> IF n = k THEN v ELSE lru_kv[n]]
        /\ UNCHANGED lru_size
    ELSE 
        IF Len(lru_recency) # lru_size THEN 
            \* add 
            /\ lru_recency' = Append(lru_recency, k)
            /\ lru_kv' = [n \in DOMAIN lru_kv \cup {k} |-> n]
            /\ UNCHANGED lru_size
        ELSE 
            \* replace oldest 
            /\ lru_recency' = Append(SelectSeq(lru_recency, LAMBDA x : x # lru_recency[1]), k)
            /\ lru_kv' = [n \in (DOMAIN lru_kv \cup {k}) \ {lru_recency[1]} |-> 
                            IF n # k THEN lru_kv[n] ELSE v]
            /\ UNCHANGED lru_size

Init(n) ==
    /\ lru_kv = <<>>
    /\ lru_recency = <<>>
    /\ lru_size = n

Next ==
    \E k \in KV: 
        /\ Put(k ,"v")

Consistent ==
    \* Keys tracked by lru_recency and lru_kv should match.
    /\ {lru_recency[k] : k \in DOMAIN lru_recency} = DOMAIN lru_kv
    /\ Cardinality(DOMAIN lru_kv) <= lru_size

N == 4

Spec ==
  /\ Init(N)
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================