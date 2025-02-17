--------------------------- MODULE test_kv ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, CSV, TLC

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