--------------------------- MODULE dropbox ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers
VARIABLES 
    meta_server, 
    \* meta_server, 
    \* sync_server,
    client_block,
    client_meta

vars == <<meta_server, client_meta, client__block>>

Clients == {"c0", "c1"}
Files == {"f0", "f1"}

MinS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x >= y

Init ==
    /\ meta_server = [f \in Files |-> {1}]                 \* track all versions of files
    /\ client_meta = [k \in Clients |-> [f \in Files |-> {1}]]   \* client local storage
    /\ client_block = [k \in Clients |-> <<>>]

Modify(k, f) ==
    \* bump the base version
    /\ client_meta' = [client_meta EXCEPT ![k] 
                    = [client_meta[k] EXCEPT ![f] 
                        = {MinS(client_meta[k][f]), MinS(client_meta[k][f]) + 1}]]
    \* /\ PrintT(client_meta')
    /\ UNCHANGED <<meta_server>>

Upload(k, f) == 
    IF MaxS(meta_server[f]) = MinS(client_meta[k][f]) THEN 
        \* base version match
        /\ meta_server' = [meta_server EXCEPT ![f] = meta_server[f] \cup {MaxS(client_meta[k][f])}] \* upload our version
        /\ client_meta' = [client_meta EXCEPT ![k]
                        = [client_meta[k] EXCEPT ![f]
                             = {MaxS(client_meta[k][f])}]]
    ELSE 
        \* k is stale - force sync to latest
        /\ client_meta' = [client_meta EXCEPT ![k]
                        = [client_meta[k] EXCEPT ![f]
                             = {MaxS(meta_server[f])}]]
        /\ UNCHANGED meta_server

Download(k, f) == 
    IF f \notin client_block[k]
    /\ client_meta[k][f] = meta_server[f]
    \* Download the latest version
    /\ client_block = [client_block EXCEPT ![k] = {MaxS(meta_server[f])}]

SyncMeta(k) == 
    /\ client_meta[k] # meta_server
    

Next ==
    \/ \E k \in Clients: 
        \E f \in Files: 
            \/ SyncMeta(k)
            \/ Download(k, f)
            \/ Modify(k, f)
            \/ Upload(k, f)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================