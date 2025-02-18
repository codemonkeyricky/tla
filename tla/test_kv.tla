--------------------------- MODULE test_kv ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, CSV, TLC, Integers

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
    \/ \E p \in 1..10:
        /\  IF p > 2 THEN
                \* cached
                /\ \E k \in DOMAIN lru_kv:
                    /\ KV!Update(k, lru_kv[k])
                    /\ written' = [x \in DOMAIN written \ {k} |-> IF x = k THEN k ELSE written[x]]
            ELSE 
                \* cache miss
                \* /\ PrintT(p)
                /\ \E k \in DataSet \ DOMAIN lru_kv:
                    /\ KV!Update(k, k)
                    /\ written' = [x \in DOMAIN written \ {k} |-> IF x = k THEN k ELSE written[x]]

Consistent == 
    \A k \in DOMAIN written: 
        KV!Read(k) = written[k]

CSVFile ==
    "stat.csv"

Stats ==
    /\ CSVWrite("%1$s", <<latency>>, CSVFile)
    \* /\ Assert(0,"")
    \* /\ TLCSet(atoi(state), TLCGet(atoi(state)) + 1)                                                                                                               
    \* \* Update KnuthYao.svg every 100 samples.                                                                                                                     
    \* /\ TLCGet("stats").traces % 250 = 0 =>                                                                                                                        
    \*     /\ IOExec(<<"/usr/bin/env", "Rscript", "SimKnuthYao.R", CSVFile>>).exitValue = 0   

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================