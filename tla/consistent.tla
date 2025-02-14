--------------------------- MODULE consistent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES cluster, global_ring, local_kv, global_kv

vars == <<cluster, global_ring, local_kv, global_kv>>

Nodes == {"n0", "n1", "n2"}
KeySpace == {0, 1, 2, 3, 4, 5}
N == Cardinality(KeySpace)
    
ValueToKey(f, v) == 
    CHOOSE only \in {n \in DOMAIN f: f[n] = v}: TRUE

Init ==
    /\ cluster = {}
    /\ global_ring = [kk \in {} |-> ""]
    /\ local_kv = [k \in Nodes |-> {}]
    /\ global_kv = {}

KeysClaimed == 
    DOMAIN global_ring

RECURSIVE FindNextKey(_, _)
FindNextKey(ring, k) ==
    IF k \in DOMAIN ring THEN
        k 
    ELSE 
        FindNextKey(ring, (k + 1) % N) 

RECURSIVE FindPrevKey(_, _)
FindPrevKey(ring, k) ==
    IF k \in DOMAIN ring THEN
        k
    ELSE 
        FindPrevKey(ring, (k - 1 + N) % N) 

DataSet(ring, my_key) == 
    LET 
        prev_key == FindPrevKey(ring, (my_key + N -1) % N)
        pkey_next == (prev_key + 1) % N
    IN 
        IF pkey_next <= my_key THEN
            {k \in pkey_next..my_key:   k \in global_kv}
        ELSE 
            {k \in pkey_next..N-1:      k \in global_kv} \cup
            {k \in 0..my_key:           k \in global_kv}

Join(u) == 
    /\ \E key \in KeySpace:
        /\ key \notin KeysClaimed
        /\ global_ring' = [x \in (DOMAIN global_ring) \cup {key} |->
                        IF x = key THEN u ELSE global_ring[x]]
        /\  IF Cardinality(cluster) # 0 THEN
                local_kv' = [local_kv EXCEPT ![u] = DataSet(global_ring', key)]
            ELSE 
                UNCHANGED local_kv
    /\ cluster' = cluster \cup {u}
    /\ UNCHANGED <<global_kv>>
       
Leave(u) == 
    LET 
        k == ValueToKey(global_ring, u)
        key_next == FindNextKey(global_ring, (k + 1) % N)
        owner_next == global_ring[key_next]
        kv1 == [local_kv EXCEPT ![u] = {}]
        kv2 == [kv1 EXCEPT ![owner_next] = kv1[owner_next] \cup DataSet(global_ring, k)]
    IN 
        /\ Cardinality(cluster) > 1
        /\ global_ring' = [n \in DOMAIN global_ring \ {k} |-> global_ring[n]]
        /\ local_kv' = kv2
        /\ cluster' = cluster \ {u}
        /\ UNCHANGED << global_kv>>

Read(u, k) == 
    LET 
        kk == FindNextKey(global_ring, k)
        owner == global_ring[kk]
    IN 
        \* key exists
        /\ \E key \in DOMAIN global_ring: key = k
        /\ k \in local_kv[owner]
        /\ UNCHANGED <<cluster, global_ring, local_kv, global_kv>>

Write(u, k) == 
    LET 
        key == FindNextKey(global_ring, k)
        owner == global_ring[key]
        up == [local_kv EXCEPT ![owner] = local_kv[owner] \cup {k}]
    IN 
        /\ local_kv' = up
        /\ global_kv' = global_kv \cup {k}
        /\ UNCHANGED <<cluster, global_ring>>

NotInCluster ==
    Nodes \ {cluster}

Next ==
    \/ \E u \in Nodes:
        /\ u \notin cluster
        /\ Join(u) 
    \/ \E u \in cluster:
        /\ Leave(u) 
    \/ \E u \in cluster:
        \E k \in global_kv:
            Read(u, k)
    \/ \E u \in cluster:
        /\ \E k \in KeySpace:
            /\ k \notin global_kv
            /\ Write(u, k)

KVConsistent == 
    UNION {local_kv[n] : n \in Nodes} = global_kv

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================