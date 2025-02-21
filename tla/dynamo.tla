--------------------------- MODULE consistent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES cluster, global_ring, local_kv, global_kv, debug

vars == <<cluster, global_ring, local_kv, global_kv, debug>>

Nodes == {"n0", "n1", "n2"}
KeySpace == {0, 1, 2, 3, 4, 5}
N == Cardinality(KeySpace)
    
ValueToKey(f, v) == 
    CHOOSE only \in {n \in DOMAIN f: f[n] = v}: TRUE

TokensClaimed == 
    DOMAIN global_ring

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

DataSet(ring, my_key) == 
    LET 
        prev_key == FindPrevToken(ring, (my_key + N -1) % N)
        pkey_next == (prev_key + 1) % N
    IN 
        IF pkey_next <= my_key THEN
            {k \in pkey_next..my_key:   k \in global_kv}
        ELSE 
            {k \in pkey_next..N-1:      k \in global_kv} \cup
            {k \in 0..my_key:           k \in global_kv}

Init ==
    /\ cluster = {}
    /\ global_ring = [kk \in {} |-> ""]
    /\ local_kv = [k \in Nodes |-> {}]
    /\ global_kv = {}
    /\ debug = {}

Join(u) == 
    /\ \E key \in KeySpace:
        /\ key \notin TokensClaimed
        /\ global_ring' = [x \in (DOMAIN global_ring) \cup {key} |->
                        IF x = key THEN u ELSE global_ring[x]]
        /\  IF Cardinality(cluster) # 0 THEN
                LET 
                    data == DataSet(global_ring', key)
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
    /\ UNCHANGED <<global_kv, debug>>
       
Leave(u) == 
    LET 
        k == ValueToKey(global_ring, u)
        key_next == FindNextToken(global_ring, (k + 1) % N)
        owner_next == global_ring[key_next]
        kv1 == [local_kv EXCEPT ![u] = {}]
        kv2 == [kv1 EXCEPT ![owner_next] = kv1[owner_next] \cup DataSet(global_ring, k)]
        updated_set == DOMAIN global_ring \ {k}
    IN 
        /\ Cardinality(cluster) > 1
        /\ global_ring' = [x \in DOMAIN global_ring \ {k} |-> global_ring[x]]
        /\ local_kv' = kv2
        /\ cluster' = cluster \ {u}
        /\ UNCHANGED <<global_kv, debug>>

\* Read(u, k) == 
\*     LET 
\*         kk == FindNextToken(global_ring, k)
\*         owner == global_ring[kk]
\*     IN 
\*         \* key exists
\*         /\ Assert(\E key \in DOMAIN global_ring: key = k,"")
\*         /\ k \in local_kv[owner]
\*         /\ UNCHANGED <<cluster, global_ring, local_kv, global_kv, debug>>

Write(u, k) == 
    LET 
        key == FindNextToken(global_ring, k)
        owner == global_ring[key]
        up == [local_kv EXCEPT ![owner] = local_kv[owner] \cup {k}]
    IN 
        /\ local_kv' = up
        /\ global_kv' = global_kv \cup {k}
        /\ UNCHANGED <<cluster, global_ring, debug>>

NotInCluster ==
    Nodes \ {cluster}

Next ==
    \/ \E u \in Nodes:
        /\ u \notin cluster
        /\ Join(u) 
    \/ \E u \in cluster:
        /\ Leave(u) 
    \/ \E u \in cluster:
        /\ \E k \in KeySpace:
            /\ k \notin global_kv
            /\ Write(u, k)

KVConsistent == 
    /\ UNION {local_kv[n] : n \in Nodes} = global_kv

KVXOR == 
    Cardinality(cluster) > 1 => 
        \A u, v \in cluster: u # v => (local_kv[u] \intersect local_kv[v]) = {}

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================