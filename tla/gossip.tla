--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals

CONSTANTS 
    Servers

VARIABLES 
    version, network

\* Servers == {"s0", "s1", "s2"}

vars == <<version>> 

Init ==
    /\ version = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ network = {}

AddMsg(m, msgs) == 
    msgs \cup {m}

RemoveMsg(m, msgs) ==
    msgs \ {m}

Send(i, j) == 
    /\ i # j
    /\ network' = AddMsg([
        src |-> i, dst |-> j, 
        data |-> version[i]], network)
    /\ UNCHANGED version

Receive(m) == 
    LET 
        i == m.dst
        j == m.src
        v == m.data
        Max(a, b) == IF a > b THEN a ELSE b
    IN 
        /\ version' = [version EXCEPT ![i] = [k \in Servers |-> Max(version[i][k], v[k])]]
        /\ network' = RemoveMsg(m, network)

Bump(i) == 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN version[i][k] ELSE version[i][k] + 1]]
    /\ UNCHANGED network

Next ==
    \/ \E i \in Servers:
        Bump(i)
    \/ \E i, j \in Servers:
        Send(i, j)
    \/ \E msg \in network:
        Receive(msg)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================