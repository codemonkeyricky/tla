--------------------------- MODULE dropbox ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers
VARIABLES 
    meta_server, 
    block_server,
    \* meta_server, 
    \* sync_server,
    client_block,
    client_change,
    client_meta

vars == <<meta_server, block_server, client_meta, client_block, client_change>>

Clients == {"c0", "c1"}
Files == {"f0", "f1"}
Sizes == {5, 7, 9}

MaxS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x >= y

TailIndex(s) ==
    MaxS(DOMAIN s)

Init ==
    \* track all versions of files 
    \* even version means uploaded and odd means local changes
    /\ meta_server = [f \in Files |-> 1]
    \* track size of all versions, ordered tuple starts from version 1
    /\ block_server = [f \in Files |-> <<5>>]
    \* client local storage
    /\ client_meta = [k \in Clients |-> meta_server]
    /\ client_change = [k \in Clients |-> [f \in Files |-> FALSE]]
    \* Client may copy a subset of the files, each file is represented using size
    /\ client_block = [k \in Clients |-> <<>>]

Modify(k, f) ==
    \* /\ client_meta[k][f] < 3
    /\ client_change[k][f] = FALSE
    \* add new version to client meta
    /\ client_meta' 
        = [client_meta EXCEPT ![k] 
            = [client_meta[k] EXCEPT ![f] 
                = client_meta[k][f] + 1]]
    \* bump client block
    /\ f \in DOMAIN client_block[k]
    /\ \E s \in Sizes: 
       client_block'
        = [client_block EXCEPT ![k] 
            = [client_block[k] EXCEPT ![f] = s]]
    /\ client_change' 
        = [client_change EXCEPT ![k] 
            = [client_change[k] EXCEPT ![f] = TRUE]]
    /\ UNCHANGED <<meta_server, block_server>>
    \* /\ Assert(0,"")

Download(k, f) == 
    \* only download if meta is up-to-date with no local changes
    /\ client_change[k][f] = FALSE
    /\ client_meta[k][f] = meta_server[f]
    \* Download the latest version
    /\ client_block'
        = [client_block EXCEPT ![k] 
            = [ff \in DOMAIN client_block[k] \cup {f} 
                |-> IF ff # f 
                    THEN client_block[k][ff] 
                    ELSE block_server[f][MaxS(DOMAIN block_server[f])]]]
    /\ UNCHANGED <<client_change, client_meta, meta_server, block_server>>
    \* /\ PrintT(client_block')
    \* /\ Assert(0,"")

SyncObject(k, f) == 
    IF f \in DOMAIN client_block[k] THEN 
        client_block' 
            = [client_block EXCEPT ![k] 
                = [client_block[k] EXCEPT ![f]
                    = block_server[f][TailIndex(block_server[f])]]]
    ELSE 
        UNCHANGED client_block

SyncMeta(k, f) == 
    IF client_meta[k][f] < meta_server[f]
    \/ (client_meta[k][f] = meta_server[f] /\ client_change[k][f]) THEN 
        \* sync client meta
        /\ client_meta' 
            = [client_meta EXCEPT ![k] 
                = [client_meta[k] EXCEPT ![f]
                    = meta_server[f]]]
        \* sync downloaded file
        /\ SyncObject(k, f)
        /\ client_change' 
            = [client_change EXCEPT ![k] 
                = [client_change[k] EXCEPT ![f] = FALSE]]
        /\ UNCHANGED <<meta_server, block_server>>
    ELSE 
        /\ UNCHANGED vars

Upload(k, f) == 
    \* client is ahead of the remote with local change
    /\ meta_server[f] < client_meta[k][f]
    /\ client_change[k][f]
    /\ meta_server' 
        = [meta_server EXCEPT ![f] 
            = client_meta[k][f]] \* upload our version
    /\ block_server' = [block_server EXCEPT ![f] 
                        = Append(block_server[f], client_block[k][f])]
    /\ client_change' 
        = [client_change EXCEPT ![k] 
            = [client_change[k] EXCEPT ![f] = FALSE]]
    /\ UNCHANGED <<client_block, client_meta>>

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
            (client_change[k][f] = FALSE /\ f \in DOMAIN client_block[k])
                => client_block[k][f] = block_server[f][client_meta[k][f]]

\* client is at most one change ahead of server
Consistent2 == 
    \A k \in Clients:
        \A f \in Files:
            f \in DOMAIN client_meta[k] 
                => (client_meta[k][f] - meta_server[f]) <= 1

\* If client is ahead of remote, client must have local change
Consistent3 == 
    \A k \in Clients:
        \A f \in Files:
            client_meta[k][f] > meta_server[f] => client_change[k][f]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================