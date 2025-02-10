--------------------------- MODULE torrent ----------------------------
EXTENDS Naturals, TLC, FiniteSets
VARIABLES tracker, data

vars == <<tracker, data>>

Chunks == 4

Client == {"c0", "c1"}
Seed == "c0"

Init ==
    /\ tracker = {Seed}
    /\ data = [seed |-> {1..Chunks}]

NewClient ==  
    LET 
        potential == Client \ tracker    
        c == CHOOSE k \in potential : TRUE    
    IN 
        tracker' = tracker \cup {c}
        data' = data @@ [c :> {}]

Download == 
    LET 
        u == CHOOSE k \in tracker: Cardinality(data[k]) # Chunks
        missing == {1..Chunks} \ data[u]
        v == CHOOSE k \in tracker: missing \in data[k]
        m == CHOOSE m \in missing: TRUE
    IN 
        /\ data' = [data EXCEPT ![u] = data[u] \cup {m}]
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
    \* \/ /\ \E k \in tracker: Cardinality(data[k]) # Chunks
    \/    Download
    \/ RemoveComplete

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================