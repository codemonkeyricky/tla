--------------------------- MODULE consistent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt
VARIABLES cluster, local_ring, global_ring, local_kv, global_kv

vars == <<cluster, local_ring, global_ring, local_kv, global_kv>>

Nodes == {"n0", "n1", "n2"}
KeySpace == {0, 1, 2, 3, 4, 5, 6, 7}
N == Cardinality(KeySpace)

EmptyFunction == 
    [kk \in {} |-> ""]

Init ==
    /\ cluster = {}
        \* local[node][token] -> node
    /\ local_ring = [k \in Nodes |-> EmptyFunction]
        \* global_ring[token] -> node
    /\ global_ring = EmptyFunction
        \* store[node] = { ... keys ... }
    /\ local_kv = [k \in Nodes |-> {}]
        \* all values written
    /\ global_kv = {}
    \* /\ status = [k \in Nodes |-> "offline"]

Claimed == 
    DOMAIN global_ring

RECURSIVE Find(_, _)
Find(lookup, k) ==
    IF k \in DOMAIN lookup THEN
        lookup[k] 
    ELSE 
        Find(lookup, (k + 1) % N) 

RECURSIVE FindPrevKey(_, _)
FindPrevKey(lookup, k) ==
    IF k \in DOMAIN lookup THEN
        k
    ELSE 
        FindPrevKey(lookup, (k - 1 + N) % N) 

Join(u) == 
    /\ \E claim \in KeySpace:
        \* /\ PrintT(claim)
        /\ claim \notin Claimed
        /\ global_ring' = [x \in (DOMAIN global_ring) \cup {claim} |->
                        IF x = claim THEN u ELSE global_ring[x]]
        /\ local_ring' = [local_ring EXCEPT ![u] = global_ring']
    /\ cluster' = cluster \cup {u}
    /\ UNCHANGED <<global_kv, local_kv>>

Gossip(u) == 
    LET 
        my_key_set == {x \in DOMAIN global_ring: IF global_ring[x] = u THEN TRUE ELSE FALSE}
        my_key == CHOOSE only \in my_key_set : TRUE
        prev_key == FindPrevKey(global_ring, my_key-1)
    IN 
        /\ Cardinality(DOMAIN global_ring) > 1
        /\ PrintT(u)
        /\ PrintT(my_key)
        /\ PrintT(prev_key)
        /\ Assert(0,"")
        /\ local_ring' = [local_ring EXCEPT ![u] = global_ring]
        /\ UNCHANGED <<cluster, global_ring, local_kv, global_kv>>

Leave(u) == 
    TRUE

Read(u, k) == 
    LET 
        owner == Find(local_ring[u], k)
    IN 
        \* key exists
        /\ \E key \in DOMAIN global_ring: key = k
        \* /\ PrintT(local_kv)
        \* /\ PrintT(owner)
        \* /\ PrintT(k)
        /\ k \in local_kv[owner]
        /\ UNCHANGED <<cluster, local_ring, global_ring, local_kv, global_kv>>

Write(u, k) == 
    LET 
        \* TODO
        \* owner == Find(local_ring[u], k)
        owner == Find(global_ring, k)
    IN 
        \* /\ PrintT(local_ring[u])
        \* /\ PrintT(k)
        \* /\ PrintT(owner)
        /\ local_kv' = [local_kv EXCEPT ![owner] = local_kv[owner] \cup {k}]
        /\ global_kv' = global_kv \cup {k}
        /\ UNCHANGED <<cluster, local_ring, global_ring>>

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
            /\ k \notin global_kv
            /\ Write(u, k)

Safety == 
    \A u, v \in cluster:
        IF u # v /\ local_kv[u] # {} /\ local_kv[v] # {} THEN 
           local_kv[u] \intersect local_kv[v] = {}
        ELSE 
            TRUE

\* NodeToVerify == "c0"

\* Liveness == 
\*     \* targeted liveness condition
\*     data[NodeToVerify] = {} ~> data[NodeToVerify] = AllChunks

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================