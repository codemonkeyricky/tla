--------------------------- MODULE lru ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES kv, recency

vars == <<kv, recency>>

N == 4

KV == {"a", "b", "c", "d", "e", "f"}

Get(k) == 
    /\ recency' = Append(SelectSeq(recency, LAMBDA x : x # k), k)
    /\ UNCHANGED kv

Contains(k) == 
    /\ k \in DOMAIN kv 

Put(k, v) == 
    IF Len(recency) # N THEN 
        IF k \in DOMAIN kv THEN 
            /\ recency' = Append(SelectSeq(recency, LAMBDA x : x # k), k)
            /\ kv' = [n \in DOMAIN kv \ {k} |-> n]
        ELSE 
            /\ recency' = Append(recency, k)
            /\ kv' = [n \in DOMAIN kv \cup {k} |-> n]
    ELSE  \* Cardinality(kv) = N 
        IF k \in DOMAIN kv THEN 
            \* refresh
            /\ recency' = Append(SelectSeq(recency, LAMBDA x : x # k), k)
            /\ kv' = [n \in DOMAIN kv \ {k} |-> kv[n]]
        ELSE 
            \* remove oldest
            /\ recency' = Append(SelectSeq(recency, LAMBDA x : x # recency[1]), k)
            /\ kv' = [n \in (DOMAIN kv \cup {k}) \ {recency[1]} |-> n]

Init ==
    /\ kv = [k \in {} |-> 0]
    /\ recency = <<>>

Unchanged == 
    /\ UNCHANGED <<kv, recency>>

Next ==
    \E k \in KV: 
        Put(k ,"v")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================