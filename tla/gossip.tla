--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Servers

VARIABLES 
    version, network

MaxDivergence == 1
MaxVersion == 2
MaxNetworkOutstanding == 1

vars == <<version, network>> 

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
        src |-> i, 
        dst |-> j, 
        data |-> version[i]], network)
    /\ UNCHANGED version

HighestVersion ==
    LET Values == {version[i][j] : i \in Servers, j \in Servers}
    IN IF Values = {} THEN 0 ELSE CHOOSE x \in Values : \A y \in Values : y <= x

LowestVersion ==
    LET Values == {version[i][j] : i \in Servers, j \in Servers}
    IN IF Values = {} THEN 0 ELSE CHOOSE x \in Values : \A y \in Values : y >= x

LimitDivergence(i) == 
    \/ version[i][i] # HighestVersion
    \/ /\ version[i][i] = HighestVersion
       /\ HighestVersion - LowestVersion < MaxDivergence

LimitNetworkOutstanding ==
    Cardinality(network) < MaxNetworkOutstanding

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
    /\ version[i][i] # MaxVersion 
    /\ LimitDivergence(i)
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN version[i][k] ELSE version[i][k] + 1]]
    /\ UNCHANGED network

Drop(m) == 
    /\ network' = RemoveMsg(m, network)    
    /\ UNCHANGED version

Restart(i) == 
    /\ version[i][i] # MaxVersion 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 0]]
    /\ UNCHANGED network

Next ==
    \/ \E i \in Servers:
        Bump(i)
    \/ \E i, j \in Servers:
        /\ LimitNetworkOutstanding
        /\ Send(i, j)
    \/ \E msg \in network:
        Receive(msg)
    \/ \E i \in Servers:
        /\ version[i][i] # HighestVersion
        /\ Restart(i)

Liveness == 
    \A i, j \in Servers: 
        \* version[i][j] = 0 ~> version[i][j] = 1
          <>[](version[i][j] = MaxVersion)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \A v \in 0..MaxVersion-1:
        \A i \in Servers: 
        SF_vars(version[i][i] = v /\ Bump(i))
  /\ \A i, j \in Servers: 
        SF_vars(Send(i, j))
  /\ SF_vars(\E m \in network: Receive(m))
=============================================================================