--------------------------- MODULE dropbox ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers
VARIABLES 
    meta_server, 
    block_server,
    \* meta_server, 
    \* sync_server,
    client_block,
    client_meta

vars == <<meta_server, block_server, client_meta, client_block>>

Clients == {"c0", "c1"}
Files == {"f0", "f1"}

MinS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x >= y

Init ==
    /\ meta_server = [f \in Files |-> {1}]                 \* track all versions of files
    /\ block_server = [f \in Files |-> {1}]
    /\ client_meta = [k \in Clients |-> [f \in Files |-> {1}]]   \* client local storage
    /\ client_block = [k \in Clients |-> <<>>]

Modify(k, f) ==
    \* only one version ahead - no point modeling 2 or more versions head
    /\ MaxS(client_meta[k][f]) = MaxS(meta_server[f])
    \* add new version to client meta
    /\ client_meta' 
        = [client_meta EXCEPT ![k] 
            = [client_meta[k] EXCEPT ![f] 
                = client_meta[k][f] \cup {MaxS(client_meta[k][f]) + 1}]]
    \* bump client block
    /\ f \in DOMAIN client_block[k]
    /\ client_block'
        = [client_block EXCEPT ![k] 
            = [client_block[k] EXCEPT ![f] 
                = MaxS(client_meta[k][f]) + 1]]
    /\ UNCHANGED <<meta_server, block_server>>
    \* /\ Assert(0,"")

MetaUpToDate(k, f) == 
    \* ensure meta is up-to-date, local changes allowed
    MinS(client_meta[k][f]) = MaxS(meta_server[f])

Download(k, f) == 
    \* only download if there's no local changes
    /\ MaxS(client_meta[k][f]) = MaxS(meta_server[f])
    \* /\ client_meta[k][f] = meta_server[f]
    \* Download the latest version
    /\ client_block'
        = [client_block EXCEPT ![k] 
            = [ff \in DOMAIN client_block[k] \cup {f} 
                |-> IF ff # f THEN client_block[k][ff] ELSE MaxS(block_server[f])]]
    /\ UNCHANGED <<client_meta, meta_server, block_server>>
    \* /\ PrintT(client_block')
    \* /\ Assert(0,"")

SyncObject(k, f) == 
    IF f \in DOMAIN client_block[k] THEN 
        client_block' 
            = [client_block EXCEPT ![k] 
                = [client_block[k] EXCEPT ![f]
                    = MaxS(block_server[f]) ]]
    ELSE 
        UNCHANGED client_block

SyncMeta(k, f) == 
    /\ ~MetaUpToDate(k, f)
    \* sync client meta
    /\ client_meta' 
        = [client_meta EXCEPT ![k] 
            = [client_meta[k] EXCEPT ![f]
                = meta_server[f]]]
    \* sync downloaded file
    /\ SyncObject(k, f)
    /\ UNCHANGED <<meta_server, block_server>>

Upload(k, f) == 
        \* do we have the latest? 
    /\ IF meta_server[f] \subseteq client_meta[k][f] THEN 
        \* are we ahead? 
        IF MaxS(client_meta[k][f]) > MaxS(meta_server[f]) THEN 
            \* something to upload
            /\ meta_server' = [meta_server EXCEPT ![f] = meta_server[f] \cup {MaxS(client_meta[k][f])}] \* upload our version
            /\ block_server' = [block_server EXCEPT ![f] = block_server[f] \cup {MaxS(client_meta[k][f])}]
            \* /\ client_meta' = [client_meta[k] EXCEPT ![f] = meta_server'[f]]
            /\ UNCHANGED <<client_block, client_meta>>
        ELSE 
            \* nothing to upload
            /\ UNCHANGED vars 
       ELSE 
        \* k is stale - force sync to latest
        /\ SyncMeta(k, f) 
        /\ UNCHANGED <<meta_server, block_server>>

Next ==
    \/ \E k \in Clients: 
        \E f \in Files: 
            \/ SyncMeta(k, f)
            \/ Download(k, f)
            \/ Modify(k, f)
            \/ Upload(k, f)

\* if client has downloaded the file, downloaded version must match the meta data
Consistent == 
    \A k \in Clients:
        \A f \in Files:
            f \in DOMAIN client_block[k] 
                => MaxS(client_meta[k][f]) = client_block[k][f]

\* client is at most one change ahead of server
Consistent2 == 
    \A k \in Clients:
        \A f \in Files:
            f \in DOMAIN client_meta[k] 
                => Cardinality(client_meta[k][f] \ meta_server[f]) <= 1

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================