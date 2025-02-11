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

NewClient ==  
    LET 
        potential == Client \ tracker    
        c == IF potential # {} THEN CHOOSE k \in potential : TRUE ELSE "nil"
    IN 
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
    LET 
        set == tracker \ {k}
    IN 
        UNION {data[i] : i \in set}

Restart == 
    LET 
        u == CHOOSE k \in tracker : AllDataWithout(k) = AllChunks
    IN 
        /\ \E k \in tracker : AllDataWithout(k) = AllChunks
        /\ tracker' = tracker \ {u}
        /\ UNCHANGED <<data>>

\* PendingClient == 
\*     \E k \in tracker: Cardinality(data[k]) # Chunks

Next ==
    \/ /\ tracker # Client
       /\ NewClient
    \/ Download
    \/ Restart

Safety == 
    LET 
        all == UNION {data[k] : k \in Client}
    IN 
        all = AllChunks

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================