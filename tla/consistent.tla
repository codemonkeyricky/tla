--------------------------- MODULE consistent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES cluster, status, local, global, local_kv, global_kv

vars == <<cluster, local, status, global, local_kv, global_kv>>

Nodes == {"n0", "n1", "n2"}
KeySpace == {0, 1, 2, 3, 4, 5, 6, 7}

EmptyFunction == 
    [kk \in {} |-> ""]

Init ==
    /\ cluster = {}
        \* local[node][token] -> node
    /\ local = [k \in Nodes |-> EmptyFunction]
        \* global[token] -> node
    /\ global = EmptyFunction
        \* store[node][key] -> value
    /\ local_kv = [k \in Nodes |-> EmptyFunction]
        \* all values written
    /\ global_kv = {}
    /\ status = [k \in Nodes |-> "offline"]

Claimed == 
    {local[k] : k \in DOMAIN global}

Join(u) == 
    /\ \E claim \in Claimed:
        /\ global' = [global EXCEPT ![claim] = u]
        /\ local' = [local EXCEPT ![u] = global']

Gossip(u) == 
    /\ local' = [local EXCEPT ![u] = global]

Leave(u) == 
    TRUE

RECURSIVE Find(_, _)
Find(lookup, k) == 
    IF k \in DOMAIN lookup THEN
        lookup[k] 
    ELSE 
        Find(lookup, (k + 1) % Cardinality(KeySpace))

Read(u, k) == 
    \* key exists
    /\ \E key \in DOMAIN global: key = k
    /\ local_kv[Find(local[u], k)][k]

Write(u, k) == 
    LET 
        owner == Find(local[u], k)
    IN 
        /\ local_kv' = [local_kv EXCEPT ![owner] = local_kv[u] \cup {k}]
        /\ global_kv' = global_kv \cup {k}

Next ==
    \/ \E u \in Nodes: 
        Join(u) 
    \/ \E u \in Nodes:
        Leave(u)
    \/ \E u \in Nodes:
        Gossip(u)
    \/ \E u \in Nodes:
        \E k \in global_kv:
            Read(u, k)
    \/ \E u \in Nodes:
        \E k \in KeySpace:
            Write(u, k)

\* Safety == 
\*     UNION {data[k] : k \in Client} = AllChunks

\* NodeToVerify == "c0"

\* Liveness == 
\*     \* targeted liveness condition
\*     data[NodeToVerify] = {} ~> data[NodeToVerify] = AllChunks

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================