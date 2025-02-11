--------------------------- MODULE torrent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES tracker, data

vars == <<tracker, data>>

Chunks == 4
AllChunks == {1,2,3,4}

Client == {"c0", "c1", "c2", "c3"}
Seed == "c0"

Init ==
    /\ tracker = {Seed}
    /\ data = [k \in Client |-> AllChunks]

AddClient ==
    LET 
        potential == Client \ tracker    
        c == CHOOSE k \in potential : TRUE
    IN 
        /\ tracker # Client
        /\ potential # {}
        /\ tracker' = tracker \cup {c}
        /\ data' = [data EXCEPT ![c] = {}] 

Download == 
    LET 
        \* find incomplete client
        u == CHOOSE k \in tracker : data[k] # AllChunks
        \* find v that has other data
        v == CHOOSE k \in tracker : (data[k] \ data[u]) # {}
        missing == data[v] \ data[u]
        m == CHOOSE m \in missing: TRUE
    IN 
        /\ \E k \in tracker : data[k] # AllChunks
        /\ data' = [data EXCEPT ![u] = data[u] \cup {m}]
        /\ UNCHANGED <<tracker>>

AllDataWithout(k) == 
    UNION {data[i] : i \in tracker \ {k}}

RemoveClient == 
    LET 
        u == CHOOSE k \in tracker : AllDataWithout(k) = AllChunks
    IN 
        /\ \E k \in tracker : AllDataWithout(k) = AllChunks
        /\ tracker' = tracker \ {u}
        /\ UNCHANGED <<data>>

Next ==
    \/ AddClient
    \/ Download
    \/ RemoveClient

Safety == 
    UNION {data[k] : k \in Client} = AllChunks

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================