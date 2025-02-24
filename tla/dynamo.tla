--------------------------- MODULE dynamo ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences, SequencesExt, Integers
VARIABLES 
    local_ring,
    local_kv, 
    \* debug_ring, 
    debug_kv,
    debug
    \* d2,
    \* d3

vars == <<local_ring, local_kv, debug_kv, debug>>

RGs == {"rg0", "rg1", "rg2"}

SeedRG == "rg0"

RGState == {"version", "token", "state"}

StateOffline == "offline"
StateOnline == "online"
StatePrepare == "prepare"
StateExit == "exit"

KeySpace == {0, 1, 2, 3, 4, 5}
N == Cardinality(KeySpace)

RECURSIVE FindNextToken(_, _)
FindNextToken(key, ring) ==
    LET 
        condition(v) == 
            (ring[v]["state"] = StateOnline \/ ring[v]["state"] = StateExit)
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
        condition(v) == ring[v]["state"] # StateOffline /\ ring[v]["token"] = key
        exists == \E v \in DOMAIN ring: condition(v)
        owner == CHOOSE only \in DOMAIN ring: condition(only)
    IN 
        IF exists THEN
            owner
        ELSE 
            FindPrevToken((key + N - 1) % N, ring)

\* TODO: when collecting all keys to migrate, stop at the frist *online* token
RECURSIVE DataSet(_, _, _)
DataSet(k, all_tokens, all_keys) ==
    LET 
        k_prev == (k + N - 1) % N
        include == {k} \intersect all_keys
    IN 
        include \cup IF k_prev \in all_tokens THEN {} 
                     ELSE DataSet(k_prev, all_tokens, all_keys)

Merge(u, v) == 
    LET 
        updated(w) ==   IF local_ring[u][w]["version"] < local_ring[v][w]["version"] THEN 
                            local_ring[v][w]
                        ELSE 
                            local_ring[u][w]
    IN 
        [k \in RGs |-> IF k = u \/ k = v 
                         THEN [w \in RGs |-> updated(w)]
                         ELSE local_ring[k]]

Gossip(u, v) == 
    /\ local_ring[u][u]["state"] # StateOffline
    /\ local_ring[v][v]["state"] # StateOffline
    /\ local_ring' = Merge(u, v)
    /\ UNCHANGED <<local_kv, debug_kv, debug>>

AllTokens(u) == 
    LET 
        not_offline == {v \in RGs: local_ring[u][v]["state"] # StateOffline}
    IN 
        {local_ring[u][v]["token"]: v \in not_offline} 

AllOnlineTokens(u) == 
    LET 
        online == {v \in RGs: local_ring[u][v]["state"] = StateOnline}
    IN 
        {local_ring[u][v]["token"]: v \in online} 

ClaimedToken == 
    LET 
        not_offline == {v \in RGs: local_ring[v][v]["state"] # StateOffline}
    IN 
        {local_ring[k][k]["token"]: k \in not_offline}

Join(u) == 
    LET 
        key == CHOOSE any \in KeySpace \ ClaimedToken: TRUE
    IN 
        /\ local_ring[u][u]["version"] < 3
        \* Only ever one node joining at a time
        /\ local_ring[u][u]["state"] = StateOffline
        /\ local_ring' = [local_ring EXCEPT ![u] 
                            = [local_ring[u] EXCEPT ![u]
                                = [k \in RGState |-> 
                                    IF k = "version" THEN local_ring[u][u][k] + 1
                                    ELSE IF k = "token" THEN key
                                    ELSE IF k = "state" THEN StatePrepare
                                    ELSE "unused"]]]
        /\ UNCHANGED <<local_kv, debug_kv, debug>>

Leave(u) == 
    LET 
        updated == [k \in RGState |-> 
                     IF k = "version" THEN local_ring[u][u][k] + 1
                     ELSE IF k = "token" THEN local_ring[u][u][k]
                     ELSE IF k = "state" THEN StateExit
                     ELSE "unused"]
    IN 
        \* can only leave if we are already online 
        /\ local_ring[u][u]["state"] = StateOnline
        \* can only leave if there's at least another server to migrate data to
        /\ Cardinality(AllOnlineTokens(u)) >= 2
        /\ local_ring' = [local_ring EXCEPT ![u] 
                            = [local_ring[u] EXCEPT ![u]
                                = updated]] 
        /\ UNCHANGED <<local_kv, debug_kv, debug>>
       
\* find tokens owned by someone else and sync
JoinMigrate(u) == 
    LET 
        \* previous token
        v == FindPrevToken((local_ring[u][u]["token"] + N - 1) % N, local_ring[u])
        all_keys == local_kv[u]
        all_online_tokens == AllOnlineTokens(u)
        v_token == local_ring[u][v]["token"]
        v_data == DataSet(v_token, all_online_tokens, all_keys)
        updated == [k \in RGState |-> 
                            IF k = "version" THEN local_ring[u][v]["version"] + 1
                            ELSE IF k = "token" THEN local_ring[u][v]["token"]
                            ELSE IF k = "state" THEN StateOnline
                            ELSE "unused"]
        merged == Merge(u, v)
        local_ring_u == [merged EXCEPT ![u] 
                            = [merged[u] EXCEPT ![v] = updated]]
        local_ring_uv == [local_ring_u EXCEPT ![v] 
                            = [local_ring_u[v] EXCEPT ![v] = updated]]
    IN 
        \* TODO: limit
        \* /\ local_ring[u][u]["version"] < 3
        /\ Cardinality(AllTokens(u)) >= 2
        /\ local_ring[u][u]["state"] = StateOnline
        /\ local_ring[u][v]["state"] = StatePrepare
        /\ Cardinality(all_keys) # 0
        /\ IF v_data # {} THEN 
                /\ local_ring' = local_ring_uv
                /\ local_kv' = [k \in RGs |-> 
                                IF k = u THEN local_kv[k] \ v_data
                                ELSE IF k = v THEN local_kv[k] \cup v_data
                                ELSE local_kv[k]]
            ELSE 
                UNCHANGED <<local_ring, local_kv>>
        /\ UNCHANGED <<debug_kv, debug>>

\* surviving node copying from leaving node
LeaveMigrate(u) == 
    LET 
        token == (local_ring[u][u]["token"] + N - 1) % N
        v == FindPrevToken(token, local_ring[u])
        data == local_kv[u] 

        updated == [k \in RGState |-> 
                            IF k = "version" THEN local_ring[u][v]["version"] + 1
                            ELSE IF k = "token" THEN local_ring[u][v]["token"]
                            ELSE IF k = "state" THEN StateOffline
                            ELSE "unused"]
        merged == Merge(u, v)
        local_ring_u == [merged EXCEPT ![u] 
                            = [merged[u] EXCEPT ![v] = updated]]
        local_ring_uv == [local_ring_u EXCEPT ![v] 
                            = [local_ring_u[v] EXCEPT ![v] = updated]]

    IN 
        \* copying from v to u
        /\ local_ring[u][u]["state"] = StateOnline
        /\ local_ring[u][v]["state"] = StateExit
        \* update version 
        /\ local_ring' = local_ring_uv
        \* migrate data
        /\ local_kv' = [k \in RGs |-> 
                        IF k = v THEN {} 
                        ELSE IF k = u THEN local_kv[v] \cup local_kv[u] 
                        ELSE local_kv[k]]
        /\ UNCHANGED <<debug_kv, debug>>

Write(u, k) == 
    LET 
        owner == FindNextToken(k, local_ring[u])
    IN 
        \* only accept if u is owner
        /\ \/ local_ring[u][u]["state"] = StateOnline
           \/ local_ring[u][u]["state"] = StateExit
        /\ u = owner
        /\ local_kv' = [local_kv EXCEPT ![u] 
                        = local_kv[u] \cup {k}]
        /\ debug_kv' = debug_kv \cup {k}
        /\ UNCHANGED <<local_ring, debug>>

offline == [k \in RGState |-> 
            IF k = "version" THEN 0 
            ELSE IF k = "token" THEN -1
            ELSE IF k = "state" THEN "offline"
            ELSE "unused"]
seed == [k \in RGState |-> 
            IF k = "version" THEN 1 
            ELSE IF k = "token" THEN 0
            ELSE IF k = "state" THEN "online"
            ELSE "unused"]

Init ==
    /\ local_ring = [i \in RGs |-> 
                        [j \in RGs |-> 
                            IF i = SeedRG /\ j = SeedRG
                            THEN seed
                            ELSE offline ]] 
    /\ local_kv = [i \in RGs |-> {}]
    /\ debug_kv = {}
    /\ debug = {}

Next ==
    \/ \E u, v \in RGs:
        /\ Gossip(u, v)
    \/ \E u \in RGs:
        \/ JoinMigrate(u)
        \/ Join(u) 
        \/ Leave(u)
        \/ LeaveMigrate(u)
    \/ \E u \in RGs:
        /\ \E k \in KeySpace:
            /\ k \notin debug_kv
            /\ Write(u, k)

\* data in kv store are unique per node
DataUnique == 
    \A u, v \in RGs:
        /\ u # v => local_kv[u] \intersect local_kv[v] = {}

TokenLocation == 
    \A u \in RGs:
        \A k \in local_kv[u]: 
            u = FindNextToken(k, local_ring[u])

KVConsistent == 
    /\ UNION {local_kv[n] : n \in RGs} = debug_kv

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
=============================================================================