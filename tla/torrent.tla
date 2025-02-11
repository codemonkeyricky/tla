--------------------------- MODULE torrent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES tracker, data

vars == <<tracker, data>>

Chunks == 4
AllChunks == {1,2,3,4}

Client == {"c0", "c1"}
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
        u == CHOOSE k \in tracker : Cardinality(data[k]) # Chunks
        v == CHOOSE k \in tracker : Cardinality(data[k]) = Chunks
        missing == AllChunks \ data[u]
        m == CHOOSE m \in missing: TRUE
    IN 
        \* /\ PrintT(missing)
        /\ data' = [data EXCEPT ![u] = data[u] \cup {m}]
        \* /\ Assert(0, "")
        \* PrintT(data[u])
        \* /\ data' = [data EXCEPT ![u] = data[u] \cup {m}]
        /\ UNCHANGED <<tracker>>

RemoveComplete == 
    LET 
        complete == {k \in tracker: Cardinality(data[k]) = Chunks}
    IN 
        /\ Cardinality(complete) > 1
        /\ tracker' = tracker \ {CHOOSE k \in complete: TRUE}

Next ==
    \/ /\ tracker # Client
       /\ NewClient
    \/ /\ \E k \in tracker: Cardinality(data[k]) # Chunks
       /\ Download
    \/ RemoveComplete

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================