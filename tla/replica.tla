--------------------------- MODULE replica ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Integers

VARIABLES cluster, state, kv

vars == <<cluster, state, kv>>

Nodes == {"n0", "n1", "n2"}

Follower    == 0
Leader      == 1

Init ==
    /\ state = [k \in Nodes |-> Follower]
    /\ cluster = <<>>
    /\ kv = [k \in Nodes |-> <<>>]

EelectLeader == 
    /\ \A k \in Nodes: state[k] = Follower
    /\ \E k \in Nodes: 
        state' = [state EXCEPT ![k] = Leader]

Join(k) == 
    /\ k \notin cluster 
    /\ cluster' = cluster \cup {k}
    /\ UNCHANGED state

Put(u, k, v) == 
    /\ state[u] = Leader
    /\ Cardinality(cluster) >= Cardinality(Nodes) \div 2 + 1
    /\ kv' = [uu \in Nodes |-> 
                IF uu \in cluster THEN kv[uu] @@ [k |-> v]
                ELSE kv[uu]]

LeaderIndex ==
    CHOOSE only \in {k \in cluster: state[k] = Leader} : TRUE

Sync(u) == 
    /\ state[u] # Leader
    /\ kv' = [kv EXCEPT ![u] = kv[LeaderIndex]]

Next ==
    \/ EelectLeader 
    \/ \E k \in Nodes: 
        \/ Join(k)
        \/ Sync(k)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================