--------------------------- MODULE test_kv ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

VARIABLES 
    lru_kv, lru_recency, lru_size,  \* LRU import
    kv, latency                     \* KV store import


vars == <<lru_kv, lru_recency, lru_size>>

KV == INSTANCE kv_store

Init ==
    /\ KV!Init

Next ==
    /\ TRUE

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================