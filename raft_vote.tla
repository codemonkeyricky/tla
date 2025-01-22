--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers, FiniteSets, TLC
VARIABLES state, messages
vars == <<state, messages>>

Follower == 0 
Candidate == 1
Leader == 2

Servers == {"s0", "s1", "s2"}

Init ==
    /\ state = [s \in Servers |-> Follower]
    /\ messages = [m \in {} |-> 0]

AddMessage(to_add) == 
    IF to_add \in DOMAIN messages THEN 
        [messages EXCEPT ![to_add] = @ + 1]
    ELSE 
        messages @@ (to_add :> 1)

Tx(msg) == messages' = AddMessage(msg)

KeepAlive(i, j) == 
    /\ state[i] = Leader
    /\ Tx([src |-> i,
           dst |-> j])
    /\ UNCHANGED <<vars>>

Next == 
    \/ \E i, j \in Servers : KeepAlive(i, j)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================