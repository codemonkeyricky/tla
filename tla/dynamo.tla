--------------------------- MODULE dynamo ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES 
    cluster, 
    local_ring,
    local_kv, 
    debug_ring, 
    debug_kv, 
    debug

vars == <<cluster, local_ring, local_kv, debug_ring, debug_kv, debug>>

Nodes == {"n0", "n1", "n2"}

NodeState == {"version", "token", "status"}

StatusOffline == "offline"
StatusOnline == "online"
StatusPrepare == "prepare"

KeySpace == {0, 1, 2, 3, 4, 5}
N == Cardinality(KeySpace)
    
ValueToKey(f, v) == 
    CHOOSE only \in {n \in DOMAIN f: f[n] = v}: TRUE

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

Gossip(u, v) == 
    LET 
        updated(w) ==   IF local_ring[u][w]["version"] < local_ring[v][w]["version"] THEN 
                            local_ring[v][w]
                        ELSE 
                            local_ring[u][w]
    IN 
        /\ Cardinality(cluster) >= 2
        /\ local_ring' = [k \in Nodes |-> 
            IF k = u \/ k = v THEN 
                [w \in Nodes |-> updated(w)]
            ELSE 
                local_ring[k]]
        /\ UNCHANGED <<cluster, local_kv, debug_ring, debug_kv, debug>>

\* vars == <<cluster, local_ring, local_kv, debug_ring, debug_kv, debug>>

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
        ELSE IF k = "token" THEN -1
        ELSE IF k = "status" THEN "offline"
        ELSE "unused"]]] 
    /\ local_kv = [i \in Nodes |-> <<>>]
    /\ debug_kv = {}
    /\ debug_ring = <<>>
    /\ debug = {}

Join(u) == 
    /\ \E key \in KeySpace:
        /\ key \notin DOMAIN debug_ring \* TODO: hack
        \* update local_ring[u][u]
        /\ local_ring' = [local_ring EXCEPT ![u] 
                            = [local_ring[u] EXCEPT ![u]
                                = [k \in NodeState |-> 
                                    IF k = "version" THEN local_ring[u][u][k] + 1
                                    ELSE IF k = "token" THEN key
                                    ELSE IF k = "status" THEN StatusPrepare
                                    ELSE "unused"]]]
        /\ debug_ring' = [kk \in DOMAIN debug_ring \cup {key} |-> 
                            IF kk = key THEN u 
                            ELSE debug_ring[kk]]
    /\ cluster' = cluster \cup {u}
    /\ UNCHANGED <<local_kv, debug_kv, debug>>
       
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

NotInCluster ==
    Nodes \ {cluster}

RECURSIVE FindNextToken2(_, _)
FindNextToken2(key, ring) ==
    LET 
        condition(v) == ring[v]["status"] = StatusOnline /\ ring[v]["token"] = key
        exists == \E v \in DOMAIN ring: condition(v)
        owner == CHOOSE only \in DOMAIN ring: condition(only)
    IN 
        IF exists THEN
            owner
        ELSE 
            FindNextToken2((key + 1) % N, ring)

\* find tokens owned by someone else and sync
DataMigrate(u) == 
    LET 
        owner(k) == FindNextToken2(k, local_ring[u])
    IN 
        /\ u \in cluster
        /\ \A k \in DOMAIN local_kv[u]:
            IF FindNextToken2(k, local_ring[u]) # u THEN
                \* migrate 
                Assert(0,"")
            ELSE 
                UNCHANGED local_ring
        /\ UNCHANGED vars

BecomeReady(u) ==
    LET 
        no_one_ready ==
            \A k \in cluster: local_ring[k][k]["status"] # StatusOnline
    IN 
        /\ u \in cluster 
        /\ local_ring[u][u]["status"] = StatusPrepare
        /\ IF no_one_ready THEN 
                local_ring' = [local_ring EXCEPT ![u] 
                                = [local_ring[u] EXCEPT ![u]
                                    = [k \in NodeState |-> 
                                        IF k = "status" THEN StatusOnline
                                        ELSE local_ring[u][u][k]]]]
           ELSE 
                UNCHANGED local_ring
        /\ UNCHANGED <<cluster, local_kv, debug_ring, debug_kv, debug>>

Write(u, k) == 
    LET 
        owner == FindNextToken2(k, local_ring[u])
    IN 
        \* only accept if u is owner
        /\ local_ring[u][u]["status"] = StatusOnline
        /\ u = owner
        /\ local_kv' = [local_kv EXCEPT ![u] 
                        = [kk \in DOMAIN local_kv[u] \cup {k} |-> 
                            IF kk = k THEN k 
                            ELSE local_kv[u][kk]]]
        /\ debug_kv' = debug_kv \cup {k}
        /\ UNCHANGED <<cluster, local_ring, debug_ring, debug>>

Next ==
    \/ \E u, v \in Nodes:
        /\ Gossip(u, v)
    \/ \E u \in Nodes:
        \/ BecomeReady(u)
        \/ DataMigrate(u)
    \/ \E u \in Nodes:
        /\ u \notin cluster
        /\ Join(u) 
    \* \/ \E u \in cluster:
    \*     /\ Leave(u) 
    \/ \E u \in Nodes:
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