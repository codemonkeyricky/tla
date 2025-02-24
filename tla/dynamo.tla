--------------------------- MODULE dynamo ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES 
    cluster, 
    local_ring,
    local_kv, 
    \* debug_ring, 
    debug_kv,
    d1
    \* d2,
    \* d3

vars == <<cluster, local_ring, local_kv, debug_kv, d1>>

Nodes == {"n0", "n1", "n2"}

NodeState == {"version", "token", "status"}

StatusOffline == "offline"
StatusOnline == "online"
StatusPrepare == "prepare"
StatusExit == "exit"

KeySpace == {0, 1, 2, 3, 4, 5}
N == Cardinality(KeySpace)
    
Merge(u, v) == 
    LET 
        updated(w) ==   IF local_ring[u][w]["version"] < local_ring[v][w]["version"] THEN 
                            local_ring[v][w]
                        ELSE 
                            local_ring[u][w]
    IN 
        [k \in Nodes |-> IF k = u \/ k = v 
                         THEN [w \in Nodes |-> updated(w)]
                         ELSE local_ring[k]]

Gossip(u, v) == 
    /\ local_ring[u][u]["status"] # StatusOffline
    /\ local_ring[v][v]["status"] # StatusOffline
    /\ local_ring' = Merge(u, v)
    /\ UNCHANGED <<cluster, local_kv, debug_kv, d1>>

AllTokens(u) == 
    LET 
        not_offline == {v \in Nodes: local_ring[u][v]["status"] # StatusOffline}
    IN 
        {local_ring[u][v]["token"]: v \in not_offline} 

AllOnlineTokens(u) == 
    LET 
        online == {v \in Nodes: local_ring[u][v]["status"] = StatusOnline}
    IN 
        {local_ring[u][v]["token"]: v \in online} 

ClaimedToken == 
    LET 
        not_offline == {v \in Nodes: local_ring[v][v]["status"] # StatusOffline}
    IN 
        {local_ring[k][k]["token"]: k \in not_offline}

Join(u) == 
    LET 
        key == CHOOSE any \in KeySpace \ ClaimedToken: TRUE
    IN 
        \* Only ever one node joining at a time
        /\ u \notin cluster
        /\ local_ring' = [local_ring EXCEPT ![u] 
                            = [local_ring[u] EXCEPT ![u]
                                = [k \in NodeState |-> 
                                    IF k = "version" THEN local_ring[u][u][k] + 1
                                    ELSE IF k = "token" THEN key
                                    ELSE IF k = "status" THEN StatusPrepare
                                    ELSE "unused"]]]
        /\ cluster' = cluster \cup {u}
        /\ UNCHANGED <<local_kv, debug_kv, d1>>

Leave(u) == 
    LET 
        updated == [k \in NodeState |-> 
                     IF k = "version" THEN local_ring[u][u][k] + 1
                     ELSE IF k = "token" THEN local_ring[u][u][k]
                     ELSE IF k = "status" THEN StatusExit
                     ELSE "unused"]
    IN 
        \* Only ever one node joining at a time
        /\ u \in cluster
        \* can only leave if we are already online 
        /\ local_ring[u][u]["status"] = StatusOnline
        \* can only leave if there's at least another server to migrate data to
        /\ Cardinality(AllOnlineTokens(u)) >= 2
        /\ local_ring' = [local_ring EXCEPT ![u] 
                            = [local_ring[u] EXCEPT ![u]
                                = updated]] 
        /\ UNCHANGED <<cluster, local_kv, debug_kv, d1>>
       
RECURSIVE FindNextToken(_, _)
FindNextToken(key, ring) ==
    LET 
        condition(v) == 
            (ring[v]["status"] = StatusOnline \/ ring[v]["status"] = StatusExit)
                /\ ring[v]["token"] = key
        exists == \E v \in DOMAIN ring: condition(v)
        owner == CHOOSE only \in DOMAIN ring: condition(only)
    IN 
        IF exists THEN
            owner
        ELSE 
            FindNextToken((key + 1) % N, ring)

RECURSIVE FindPrevToken(_, _)
FindPrevToken(key, ring) ==
    LET 
        condition(v) == ring[v]["status"] # StatusOffline /\ ring[v]["token"] = key
        exists == \E v \in DOMAIN ring: condition(v)
        owner == CHOOSE only \in DOMAIN ring: condition(only)
    IN 
        IF exists THEN
            owner
        ELSE 
            FindPrevToken((key + N - 1) % N, ring)

MyToken(u) == 
    local_ring[u][u]["token"]

\* TODO: when collecting all keys to migrate, stop at the frist *online* token
RECURSIVE DataSet(_, _, _)
DataSet(k, all_tokens, all_keys) ==
    LET 
        k_prev == (k + N - 1) % N
        include == {k} \intersect all_keys
    IN 
        include \cup IF k_prev \in all_tokens THEN {} 
                     ELSE DataSet(k_prev, all_tokens, all_keys)

\* find tokens owned by someone else and sync
JoinMigrate(u) == 
    LET 
        \* previous token
        v == FindPrevToken((local_ring[u][u]["token"] + N - 1) % N, local_ring[u])
        all_keys == local_kv[u]
        all_online_tokens == AllOnlineTokens(u)
        v_token == local_ring[u][v]["token"]
        v_data == DataSet(v_token, all_online_tokens, all_keys)
        updated == [k \in NodeState |-> 
                            IF k = "version" THEN local_ring[u][v]["version"] + 1
                            ELSE IF k = "token" THEN local_ring[u][v]["token"]
                            ELSE IF k = "status" THEN StatusOnline
                            ELSE "unused"]
        merged == Merge(u, v)
        local_ring_u == [merged EXCEPT ![u] 
                            = [merged[u] EXCEPT ![v] = updated]]
        local_ring_uv == [local_ring_u EXCEPT ![v] 
                            = [local_ring_u[v] EXCEPT ![v] = updated]]
    IN 
        \* TODO: limit
        /\ local_ring[u][u]["version"] # 3
        /\ u \in cluster
        /\ Cardinality(AllTokens(u)) >= 2
        /\ local_ring[u][u]["status"] = StatusOnline
        /\ local_ring[u][v]["status"] = StatusPrepare
        /\ Cardinality(all_keys) # 0
        /\ IF v_data # {} THEN 
                \* migrate data to v and mark v as ready 
                /\ local_ring' = local_ring_uv
                /\ local_kv' = [k \in Nodes |-> 
                                IF k = u THEN local_kv[k] \ v_data
                                ELSE IF k = v THEN local_kv[k] \cup v_data
                                ELSE local_kv[k]]
            ELSE 
                UNCHANGED <<local_ring, local_kv>>
        /\ UNCHANGED <<cluster, debug_kv, d1>>

\* surviving node copying from leaving node
LeaveMigrate(u) == 
    LET 
        token == (local_ring[u][u]["token"] + N - 1) % N
        v == FindPrevToken(token, local_ring[u])
        data == local_kv[u] 

        updated == [k \in NodeState |-> 
                            IF k = "version" THEN local_ring[u][v]["version"] + 1
                            ELSE IF k = "token" THEN local_ring[u][v]["token"]
                            ELSE IF k = "status" THEN StatusOffline
                            ELSE "unused"]
        merged == Merge(u, v)
        local_ring_u == [merged EXCEPT ![u] 
                            = [merged[u] EXCEPT ![v] = updated]]
        local_ring_uv == [local_ring_u EXCEPT ![v] 
                            = [local_ring_u[v] EXCEPT ![v] = updated]]

    IN 
        /\ u \in cluster
        \* /\ Cardinality(cluster) >= 2
        \* copying from v to u
        /\ local_ring[u][u]["status"] = StatusOnline
        /\ local_ring[u][v]["status"] = StatusExit
        \* update version 
        /\ local_ring' = local_ring_uv
        \* migrate data
        /\ local_kv' = [k \in Nodes |-> 
                        IF k = v THEN {} 
                        ELSE IF k = u THEN local_kv[v] \cup local_kv[u] 
                        ELSE local_kv[k]]
        /\ UNCHANGED <<cluster, debug_kv, d1>>

Write(u, k) == 
    LET 
        owner == FindNextToken(k, local_ring[u])
    IN 
        \* only accept if u is owner
        /\ \/ local_ring[u][u]["status"] = StatusOnline
           \/ local_ring[u][u]["status"] = StatusExit
        /\ u = owner
        /\ local_kv' = [local_kv EXCEPT ![u] 
                        = local_kv[u] \cup {k}]
        /\ debug_kv' = debug_kv \cup {k}
        /\ UNCHANGED <<cluster, local_ring, d1>>

Init ==
    LET 
        offline == [k \in NodeState |-> 
            IF k = "version" THEN 0 
            ELSE IF k = "token" THEN -1
            ELSE IF k = "status" THEN "offline"
            ELSE "unused"]
        seed == [k \in NodeState |-> 
            IF k = "version" THEN 1 
            ELSE IF k = "token" THEN 0
            ELSE IF k = "status" THEN "online"
            ELSE "unused"]
    IN 
        /\ cluster = {"n0"}
        /\ local_ring = [i \in Nodes |-> 
                            [j \in Nodes |-> 
                                IF i = "n0" /\ j = "n0" 
                                THEN seed
                                ELSE offline ]] 
        /\ local_kv = [i \in Nodes |-> {}]
        /\ debug_kv = {}
        /\ d1 = {}

Next ==
    \/ \E u, v \in Nodes:
        /\ Gossip(u, v)
    \/ \E u \in Nodes:
        \/ JoinMigrate(u)
        \/ Join(u) 
        \/ Leave(u)
        \/ LeaveMigrate(u)
    \/ \E u \in Nodes:
        /\ \E k \in KeySpace:
            /\ k \notin debug_kv
            /\ Write(u, k)

\* data in kv store are unique per node
DataUnique == 
    \A u, v \in Nodes:
        /\ u # v => local_kv[u] \intersect local_kv[v] = {}

TokenLocation == 
    \A u \in Nodes:
        \A k \in local_kv[u]: 
            u = FindNextToken(k, local_ring[u])

SomeoneAlwaysOnline == 
    Cardinality(cluster) >= 2 => \E u \in Nodes: local_ring[u][u]["status"] = StatusOnline

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