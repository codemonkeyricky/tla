--------------------------- MODULE dynamo ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES 
    cluster, 
    debug_ring, 
    local_ring,
    local_kv, 
    debug_kv, 
    debug

vars == <<cluster, debug_ring, local_kv, debug_kv, debug>>

Nodes == {"n0", "n1", "n2"}

NodeState == {"version", "token", "status"}

StatusOffline == "offline"
StatusOnline == "online"
StatusPrepare == "prepare"

KeySpace == {0, 1, 2, 3, 4, 5}
N == Cardinality(KeySpace)
    
ValueToKey(f, v) == 
    CHOOSE only \in {n \in DOMAIN f: f[n] = v}: TRUE

TokensClaimed == 
    DOMAIN debug_ring

\* old and new may co-exist at the same time
\* old may not be aware it is old, will stll persist traffic 
\* new may not have all the data
\* new must notify old 
\* old always forward traffic to new 

RECURSIVE FindNextToken(_, _)
FindNextToken(ring, k) ==
    IF k \in DOMAIN ring THEN
        k 
    ELSE 
        FindNextToken(ring, (k + 1) % N) 

RECURSIVE FindPrevToken(_, _)
FindPrevToken(ring, k) ==
    IF k \in DOMAIN ring THEN
        k
    ELSE 
        FindPrevToken(ring, (k - 1 + N) % N) 

Gossip(u, v, w) == 
    LET 
        updated ==  IF local_ring[u][w]["version"] < local_ring[v][w]["version"] THEN 
                        local_ring[v][w]
                    ELSE 
                        local_ring[u][w]
        local_ring_u == [local_ring EXCEPT ![u] = updated]
        local_ring_uv == [local_ring_u EXCEPT ![v] = updated]
    IN 
        local_ring' = local_ring_uv

DataSet(ring, my_key) == 
    LET 
        prev_key == FindPrevToken(ring, (my_key + N -1) % N)
        pkey_next == (prev_key + 1) % N
    IN 
        IF pkey_next <= my_key THEN
            {k \in pkey_next..my_key:   k \in debug_kv}
        ELSE 
            {k \in pkey_next..N-1:      k \in debug_kv} \cup
            {k \in 0..my_key:           k \in debug_kv}

Init ==
    /\ cluster = {}
    /\ local_ring = [i \in Nodes |-> [j \in Nodes |-> [k \in NodeState |-> 
        IF k = "version" THEN 0 
        ELSE IF k = "token" THEN 0
        ELSE IF k = "status" THEN "offline"
        ELSE "unused"]]] 
    /\ local_kv = [i \in Nodes |-> <<>>]
    /\ debug_kv = {}
    /\ debug_ring = <<>>
    /\ debug = {}

Join(u) == 
    /\ \E key \in KeySpace:
        /\ key \notin TokensClaimed
        /\ debug_ring' = [x \in (DOMAIN debug_ring) \cup {key} |->
                        IF x = key THEN u ELSE debug_ring[x]]
        /\  IF Cardinality(cluster) # 0 THEN
                LET 
                    data == DataSet(debug_ring', key)
                    updated == [n \in DOMAIN local_kv \cup {u} |-> 
                                IF n # u THEN 
                                    local_kv[n] \ data 
                                ELSE 
                                    data]
                IN 
                    /\ local_kv' = updated
            ELSE 
                UNCHANGED local_kv
    /\ cluster' = cluster \cup {u}
    /\ UNCHANGED <<debug_kv, debug>>
       
Leave(u) == 
    LET 
        k == ValueToKey(debug_ring, u)
        key_next == FindNextToken(debug_ring, (k + 1) % N)
        owner_next == debug_ring[key_next]
        kv1 == [local_kv EXCEPT ![u] = {}]
        kv2 == [kv1 EXCEPT ![owner_next] = kv1[owner_next] \cup DataSet(debug_ring, k)]
        updated_set == DOMAIN debug_ring \ {k}
    IN 
        /\ Cardinality(cluster) > 1
        /\ debug_ring' = [x \in DOMAIN debug_ring \ {k} |-> debug_ring[x]]
        /\ local_kv' = kv2
        /\ cluster' = cluster \ {u}
        /\ UNCHANGED <<debug_kv, debug>>

Write(u, k) == 
    LET 
        key == FindNextToken(debug_ring, k)
        owner == debug_ring[key]
        up == [local_kv EXCEPT ![owner] = local_kv[owner] \cup {k}]
    IN 
        /\ local_kv' = up
        /\ debug_kv' = debug_kv \cup {k}
        /\ UNCHANGED <<cluster, debug_ring, debug>>

NotInCluster ==
    Nodes \ {cluster}

Next ==
    \/ \E u, v, w \in Nodes:
        /\ u # v
        /\ Gossip(u, v, w)
    \/ \E u \in Nodes:
        /\ u \notin cluster
        /\ Join(u) 
    \/ \E u \in cluster:
        /\ Leave(u) 
    \/ \E u \in cluster:
        /\ \E k \in KeySpace:
            /\ k \notin debug_kv
            /\ Write(u, k)

KVConsistent == 
    /\ UNION {local_kv[n] : n \in Nodes} = debug_kv

KVXOR == 
    Cardinality(cluster) > 1 => 
        \A u, v \in cluster: u # v => (local_kv[u] \intersect local_kv[v]) = {}

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================