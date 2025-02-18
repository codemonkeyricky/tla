--------------------------- MODULE dropbox ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers
VARIABLES 
    meta_server, 
    \* meta_server, 
    \* sync_server,
    client

vars == <<meta_server, client>>

Clients == {"c0", "c1"}
Files == {"f0", "f1"}

MinS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x >= y

Init ==
    /\ meta_server = [f \in Files |-> {1}]                 \* track all versions of files
    /\ client = [k \in Clients |-> [f \in Files |-> {1}]]   \* client local storage

Update(k, f) ==
    \* base version match
    /\ MaxS(meta_server[f]) = MinS(client[k][f])
    \* bump the base version
    /\ client' = [client EXCEPT ![k] 
                    = [client[k] EXCEPT ![f] 
                        = {MinS(client[k][f]), MinS(client[k][f]) + 1}]]
    \* /\ PrintT(client')
    /\ UNCHANGED <<meta_server>>

Sync(k, f) == 
    IF MaxS(meta_server[f]) = MinS(client[k][f]) THEN 
        \* base version match
        /\ meta_server' = [meta_server EXCEPT ![f] = meta_server[f] \cup {MaxS(client[k][f])}] \* upload our version
        /\ client' = [client EXCEPT ![k]
                        = [client[k] EXCEPT ![f]
                             = {MaxS(client[k][f])}]]
    ELSE 
        \* k is stale - force sync to latest
        /\ client' = [client EXCEPT ![k]
                        = [client[k] EXCEPT ![f]
                             = {MaxS(meta_server[f])}]]
        /\ UNCHANGED meta_server

Next ==
    \/ \E k \in Clients: 
        \E f \in Files: 
            Update(k, f)
    \/ \E k \in Clients: 
        \E f \in Files: 
            Sync(k, f)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================