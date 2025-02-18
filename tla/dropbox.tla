--------------------------- MODULE dropbox ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC
VARIABLES 
    block_server, 
    \* meta_server, 
    \* sync_server,
    client

vars == <<block_server, client>>

Clients == {"c0", "c1"}
Files == {"f0", "f1"}

MinS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x <= y

MaxS(s) ==                                                                                                                                                                               
    CHOOSE x \in s: \A y \in s: x >= y

Init ==
    /\ block_server = [f \in Files |-> {1}]                 \* track all versions of files
    \* /\ meta_server = [f \in Files |-> 1]                    \* track latest version of files
    /\ client = [k \in Clients |-> [f \in Files |-> {1}]]   \* client local storage

Update(k, f) ==
    \* base version match
    \* /\ Assert(MaxS(block_server[f]) = 1, "")
    /\ MaxS(block_server[f]) = MinS(client[k][f])
    \* /\ Assert(0, "")
    \* bump the base version
    /\ client' = [client EXCEPT ![k] 
                    = [client[k] EXCEPT ![f] 
                        = {MinS(client[k][f]), MinS(client[k][f]) + 1}]]
    \* /\ PrintT(client')
    /\ UNCHANGED <<block_server>>

Sync(k, f) == 
    IF MaxS(block_server[f]) = MinS(client[k][f]) THEN 
        \* base version match
        /\ block_server' = [block_server EXCEPT ![f] = block_server[f] \cup {MaxS(client[k][f])}] \* upload our version
        /\ client' = [client EXCEPT ![k]
                        = [client[k] EXCEPT ![f]
                             = {MaxS(client[k][f])}]]
        \* /\ UNCHANGED client
        \* /\ Assert(Cardinality(client'[k][f]) = 1, "")
        \* /\ PrintT(client)
        \* /\ PrintT(client')
        \* /\ PrintT(block_server)
        \* /\ PrintT(block_server')
        \* /\ Assert(Cardinality(client[k][f]) = 1, "")
        \* /\ Assert(MinS(client[k][f]) = MaxS(client[k][f]),"")
    ELSE 
        \* we are stale - force sync to latest
        /\ client' = [client EXCEPT ![k]
                        = [client[k] EXCEPT ![f]
                             = {MaxS(block_server[f])}]]
        /\ UNCHANGED block_server

Next ==
    \/ \E k \in Clients: 
        \E f \in Files: 
            Update(k, f)
    \/ \E k \in Clients: 
        \A f \in DOMAIN client[k]:
            Sync(k, f)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================