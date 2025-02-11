--------------------------- MODULE torrent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES tracker, data

vars == <<tracker, data>>

AllChunks == {1,2,3}

Client == {"c0", "c1", "c2"}
Seed == "c0"

Init ==
    /\ tracker = {Seed}
    /\ data = [k \in Client |-> IF k = Seed THEN AllChunks ELSE {}]

Join(k) == 
    /\ k \notin tracker
    /\ tracker' = tracker \cup {k}
    /\ UNCHANGED data

Progress(u) == 
    /\ u \in tracker
    /\ data[u] # AllChunks  \* u is incomplete
    /\ \E v \in tracker:
        \E k \in AllChunks:
            /\ k \notin data[u]     \* v has something u doesn't
            /\ k \in data[v] 
            /\ data' = [data EXCEPT ![u] = data[u] \cup {k}]
            /\ UNCHANGED tracker

Share == 
    \E u \in tracker: 
        Progress(u)

AllDataWithout(k) == 
    UNION {data[i] : i \in tracker \ {k}}

Leave(k) == 
    /\ k \in tracker
    /\ AllDataWithout(k) = AllChunks
    /\ tracker' = tracker \ {k}
    /\ data' = [data EXCEPT ![k] = {}] 

\* Leave == 
\*     /\ \E k \in tracker: 
\*         LeaveCluster(k) 

Next ==
    \/ \E k \in Client: 
        Join(k) 
    \/ \E k \in Client: 
        Progress(k)
    \/ \E k \in Client: 
        Leave(k)

NodeToVerify == "c0"

Safety == 
    UNION {data[k] : k \in Client} = AllChunks

Liveness == 
    \* targeted liveness condition
    data[NodeToVerify] = {} ~> data[NodeToVerify] = AllChunks

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    \* targeted fairness description
    /\ SF_vars(Join(NodeToVerify))
    /\ \A s \in SUBSET AllChunks: 
        SF_vars(data[NodeToVerify] = s /\ Progress(NodeToVerify))
=============================================================================