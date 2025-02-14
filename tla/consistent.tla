--------------------------- MODULE consistent ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES cluster, local_ring, global_ring, local_kv, global_kv

vars == <<cluster, local_ring, global_ring, local_kv, global_kv>>

Nodes == {"n0", "n1", "n2"}
KeySpace == {0, 1, 2, 3, 4, 5, 6, 7}
N == Cardinality(KeySpace)

\* UnionLocalKV == 

RF == 2

EmptyFunction == 
    [kk \in {} |-> ""]

ValueToKey(f, v) == 
    CHOOSE only \in {n \in DOMAIN f: f[n] = v}: TRUE

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

KeysClaimed == 
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

DataSet(ring, my_key) == 
    LET 
        prev_key == FindPrevKey(ring, (my_key + N -1) % N)
        pkey_next == (prev_key + 1) % N
        \* TODO: add to book
    IN 
        IF pkey_next <= my_key THEN
            {k \in pkey_next..my_key:   k \in global_kv}
        ELSE 
            {k \in pkey_next..N-1:      k \in global_kv} \cup
            {k \in 0..my_key:           k \in global_kv}

Join(u) == 
    /\ \E key \in KeySpace:
        \* /\ PrintT(claim)
        /\ key \notin KeysClaimed
        /\ global_ring' = [x \in (DOMAIN global_ring) \cup {key} |->
                        IF x = key THEN u ELSE global_ring[x]]
        /\ local_ring' = [local_ring EXCEPT ![u] = global_ring']
        /\  IF Cardinality(cluster) # 0 THEN
                local_kv' = [local_kv EXCEPT ![u] = 
                    DataSet(global_ring', key) \cup 
                    DataSet(global_ring', FindPrevKey(global_ring', (key + N -1)% N))]
            ELSE 
                UNCHANGED local_kv
    /\ cluster' = cluster \cup {u}
    /\ UNCHANGED <<global_kv>>
       
Gossip(u) == 
    LET 
        my_key == CHOOSE only \in {x \in DOMAIN global_ring: IF global_ring[x] = u THEN TRUE ELSE FALSE} : TRUE
        to_add == DataSet(global_ring, my_key)
    IN 
        \* /\ Cardinality(DOMAIN global_ring) > 1
        /\ local_ring' = [local_ring EXCEPT ![u] = global_ring]
        \* TODO: account for to_remove?
        /\ local_kv' = [local_kv EXCEPT ![u] = local_kv[u] \cup to_add]
        /\ UNCHANGED <<cluster, global_ring, global_kv>>
        \* /\ PrintT(UnionLocalKV)

        \* /\ PrintT(u) 
        \* /\ PrintT(pkey_next)
        \* /\ PrintT(my_key)
        \* /\ PrintT({k \in pkey_next..my_key: k \in global_kv})
        \* /\ PrintT(global_kv)
        \* /\ PrintT(prev_key)
        \* /\ PrintT(to_add)

Leave(u) == 
    LET 
        k == ValueToKey(global_ring, u)
    IN 
        /\ Cardinality(cluster) = Cardinality(Nodes)
        \* /\ PrintT(u)
        \* /\ PrintT(k)
        /\ global_ring' = [n \in DOMAIN global_ring \ {k} |-> global_ring[n]]
        /\ local_kv' = [local_kv EXCEPT ![u] = {}]
        /\ cluster' = cluster \ {u}
        /\ UNCHANGED <<local_ring, global_kv>>

Read(u, k) == 
    LET 
        owner == Find(local_ring[u], k)
    IN 
        \* key exists
        /\ \E key \in DOMAIN global_ring: key = k
        /\ k \in local_kv[owner]
        /\ UNCHANGED <<cluster, local_ring, global_ring, local_kv, global_kv>>

        \* /\ PrintT(local_kv)
        \* /\ PrintT(owner)
        \* /\ PrintT(k)

Write(u, k) == 
    LET 
        \* TODO
        \* owner == Find(local_ring[u], k)
        owner == Find(global_ring, k)
        owner_key == ValueToKey(global_ring, owner)
        owner_next == Find(global_ring, (owner_key + 1) % N)

        up1 == [local_kv EXCEPT ![owner] = local_kv[owner] \cup {k}]
        up2 == [up1 EXCEPT ![owner_next] = up1[owner_next] \cup {k}]

    IN 
        /\ Assert(RF = 2, "")
        \* /\ PrintT(local_ring[u])
        \* /\ PrintT(k)
        \* /\ PrintT(owner)
        \* /\ PrintT(owner_next)
        /\ local_kv' = up2
        /\ global_kv' = global_kv \cup {k}
        /\ UNCHANGED <<cluster, local_ring, global_ring>>

NotInCluster ==
    Nodes \ {cluster}

Next ==
    \/ \E u \in Nodes:
        /\ u \notin cluster
        /\ Join(u) 
    \/ \E u \in cluster:
        /\ Leave(u) 
    \/ \E u \in cluster:
        Gossip(u)
    \/ \E u \in cluster:
        \E k \in global_kv:
            Read(u, k)
    \/ \E u \in cluster:
        /\ Cardinality(cluster) >= RF
        /\ \E k \in KeySpace:
            /\ k \notin global_kv
            /\ Write(u, k)

KVConsistent == 
    UNION {local_kv[n] : n \in Nodes} = global_kv

RingConsistent == 
    UNION {DOMAIN local_ring[n] : n \in Nodes} = DOMAIN global_ring

\* Safety == 
    \* \A u, v \in cluster:
    \*     IF u # v /\ local_kv[u] # {} /\ local_kv[v] # {} THEN 
    \*        local_kv[u] \intersect local_kv[v] = {}
    \*     ELSE 
    \*         TRUE
    \* /\ Cardinality(global_kv) < 7

\* NodeToVerify == "c0"

\* Liveness == 
\*     \* targeted liveness condition
\*     data[NodeToVerify] = {} ~> data[NodeToVerify] = AllChunks

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================