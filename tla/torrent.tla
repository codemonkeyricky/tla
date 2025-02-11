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

Copy(u, v) == 
    /\ u \in tracker
    /\ v \in tracker
    /\ data[u] # AllChunks  \* u is incomplete
    /\ \E k \in AllChunks:
        /\ k \notin data[u]     \* v has something u doesn't
        /\ k \in data[v] 
        /\ data' = [data EXCEPT ![u] = data[u] \cup {k}]
        /\ UNCHANGED tracker

Share == 
    \E u, v \in tracker: 
        Copy(u, v)

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

Safety == 
    UNION {data[k] : k \in Client} = AllChunks

Liveness == 
    \* \A k \in Client: 
        data["c1"] = {} ~> data["c1"] = AllChunks
    \* \A k \in Client: 
    \*     data[0] = {} ~> data[k] = AllChunks

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ \A v \in Client: 
        \A s \in SUBSET AllChunks: 
            SF_vars(data["c1"] = s /\ Copy("c1", v))
    \* /\ \A u, v \in Client: 
    \*     \A k \in AllChunks:
    \*         SF_vars(Copy(u, v, k))

    \* /\ \A s \in SUBSET AllChunks: 
    \*     \A v \in Client: 
    \*         \A k \in AllChunks:
    \*             SF_vars(s # AllChunks /\ Copy("c0", v, k))

    \* /\ \A s \in SUBSET AllChunks: 
    \*     /\ SF_vars(s # AllChunks /\ data["c1"] = s /\ Download("c1"))
    \* /\ SF_vars(s # AllChunks /\ data["c1"] = s /\ Download("c1"))
    \* /\ SF_vars(s # AllChunks /\ data["c2"] = s /\ Download("c2"))
=============================================================================