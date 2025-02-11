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

JoinCluster(k) == 
    /\ k \notin tracker
    /\ tracker' = tracker \cup {k}
    /\ UNCHANGED data

Join ==
    /\ \E k \in Client: 
        JoinCluster(k) 

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

LeaveCluster(k) == 
    /\ AllDataWithout(k) = AllChunks
    /\ tracker' = tracker \ {k}
    /\ data' = [data EXCEPT ![k] = {}] 

Leave == 
    /\ \E k \in tracker: 
        LeaveCluster(k) 

Next ==
    \/ Join
    \/ Share
    \/ Leave

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
    /\ SF_vars(JoinCluster(NodeToVerify))
    /\ \A s \in SUBSET AllChunks: 
        SF_vars(data[NodeToVerify] = s /\ Progress(NodeToVerify))
=============================================================================