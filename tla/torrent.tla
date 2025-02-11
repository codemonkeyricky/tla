--------------------------- MODULE torrent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES tracker, data

vars == <<tracker, data>>

AllChunks == {1,2,3}

Client == {"c0", "c1", "c2","c3"}
Seed == "c0"

Init ==
    /\ tracker = {Seed}
    /\ data = [k \in Client |-> IF k = Seed THEN AllChunks ELSE {}]

AddClient ==
    LET 
        potential == Client \ tracker    
        c == CHOOSE k \in potential : TRUE
    IN 
        /\ tracker # Client
        /\ potential # {}
        /\ tracker' = tracker \cup {c}
        /\ UNCHANGED data

Download(u) == 
    LET 
        \* find v that has more data
        v == CHOOSE k \in tracker : (data[k] \ data[u]) # {}
        missing == data[v] \ data[u]
        m == CHOOSE m \in missing: TRUE
    IN 
        \* /\ PrintT("download")
        \* /\ PrintT(u)
        /\ data' = [data EXCEPT ![u] = data[u] \cup {m}]
        /\ UNCHANGED tracker

Share == 
    LET 
        \* find incomplete client
        u == CHOOSE k \in tracker : data[k] # AllChunks
    IN 
        /\ \E k \in tracker : data[k] # AllChunks
        /\ Download(u)
        \* /\ UNCHANGED <<tracker>>

AllDataWithout(k) == 
    UNION {data[i] : i \in tracker \ {k}}

RemoveComplete == 
    LET 
        u == CHOOSE k \in tracker : 
            \* /\ data[k] = AllChunks
            /\ AllDataWithout(k) = AllChunks
    IN 
        /\ \E k \in tracker: 
            \* /\ data[k] = AllChunks 
            /\ AllDataWithout(k) = AllChunks
        /\ tracker' = tracker \ {u}
        /\ data' = [data EXCEPT ![u] = {}] 

Next ==
    \/ AddClient
    \/ Share
    \/ RemoveComplete

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
    /\ \A s \in SUBSET AllChunks: 
        /\ SF_vars(s # AllChunks /\ data["c1"] = s /\ Download("c1"))
    \* /\ SF_vars(s # AllChunks /\ data["c1"] = s /\ Download("c1"))
    \* /\ SF_vars(s # AllChunks /\ data["c2"] = s /\ Download("c2"))
=============================================================================