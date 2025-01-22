--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers
VARIABLES state, messages
vars == <<state, messages>>

Follower == 0 
Candidate == 1
Leader == 2

Servers == {"s0", "s1", "s2"}

Init ==
    /\ state = [s \in Servers |-> Follower]
    /\ messages = [m \in {} |-> 0]

KeepAlive(i, j) == 
    /\ state[i] = Leader
    /\ UNCHANGED <<vars>>

Next == 
    \/ \E i, j \in Servers : KeepAlive(i, j)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================