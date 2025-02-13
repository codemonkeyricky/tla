--------------------------- MODULE consistent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES cluster, local, global, local_kv, global_kv

vars == <<cluster, local, global, local_kv, global_kv>>

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
        \* store[node] = { ... keys ... }
    /\ local_kv = [k \in Nodes |-> {}]
        \* all values written
    /\ global_kv = {}
    \* /\ status = [k \in Nodes |-> "offline"]

Claimed == 
    DOMAIN global

Join(u) == 
    /\ \E claim \in KeySpace:
        \* /\ PrintT(claim)
        /\ claim \notin Claimed
        /\ global' = [x \in (DOMAIN global) \cup {claim} |->
                        IF x = claim THEN u ELSE global[x]]
        /\ local' = [local EXCEPT ![u] = global']
    /\ cluster' = cluster \cup {u}
    /\ UNCHANGED <<global_kv, local_kv>>

Gossip(u) == 
    /\ local' = [local EXCEPT ![u] = global]
    /\ UNCHANGED <<cluster, global, local_kv, global_kv>>

Leave(u) == 
    TRUE

RECURSIVE Find(_, _)
Find(lookup, k) == 
    IF k \in DOMAIN lookup THEN
        lookup[k] 
    ELSE 
        Find(lookup, (k + 1) % Cardinality(KeySpace))

Read(u, k) == 
    LET 
        owner == Find(local[u], k)
    IN 
        \* key exists
        /\ \E key \in DOMAIN global: key = k
        \* /\ PrintT(local_kv)
        \* /\ PrintT(owner)
        \* /\ PrintT(k)
        /\ k \in local_kv[owner]
        /\ UNCHANGED <<cluster, local, global, local_kv, global_kv>>

Write(u, k) == 
    LET 
        owner == Find(local[u], k)
    IN 
        \* /\ PrintT(local_kv[u])
        \* /\ PrintT(k)
        /\ local_kv' = [local_kv EXCEPT ![owner] = local_kv[owner] \cup {k}]
        /\ global_kv' = global_kv \cup {k}
        /\ UNCHANGED <<cluster, local, global>>

NotInCluster ==
    Nodes \ {cluster}

Next ==
    \/ \E u \in Nodes:
        /\ u \notin cluster
        /\ Join(u) 
    \/ \E u \in cluster:
        Gossip(u)
    \/ \E u \in cluster:
        \E k \in global_kv:
            Read(u, k)
    \/ \E u \in cluster:
        /\ \E k \in KeySpace:
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