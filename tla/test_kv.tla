--------------------------- MODULE test_kv ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES 
    lru_kv, lru_recency, lru_size,  \* LRU import
    kv, latency,                    \* KV store import
    written

DataSet == {"a", "b", "c", "d", "e", "f", "g"}

vars == <<lru_kv, lru_recency, lru_size>>

KV == INSTANCE kv_store

Init ==
    /\ KV!Init
    /\ written = <<>>

Next ==
    \/ \E k \in DataSet:
        /\ KV!Put(k, k)
        /\ written' = [w \in DOMAIN written \cup {k} |-> IF w = k THEN w ELSE written[w]]
        \* /\ PrintT(written')
        \* /\ Assert(0, "")
    \* \/ \E k \in DOMAIN written:
    \*     /\ Assert(KV!Get(k) = written[k], "")
    \*     /\ UNCHANGED written

Consistent == 
    \A k \in DOMAIN written: 
        KV!Read(k) = written[k]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================