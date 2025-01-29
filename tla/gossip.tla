--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Servers

VARIABLES 
    version, network

MaxDivergence == 1
MaxVersion == 2
MaxNetworkOutstanding == 1

vars == <<version, network>> 

Init ==
    /\ version = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ network = {}

AddMsg(m, msgs) == 
    msgs \cup {m}

RemoveMsg(m, msgs) ==
    msgs \ {m}

InitiateGossip(i, j) == 
    /\ i # j
    /\ network' = AddMsg([src |-> i, dst |-> j], network)
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

ExchangeGossip(m) == 
    LET 
        i == m.dst
        j == m.src
        Max(a, b) == IF a > b THEN a ELSE b
        updated == [k \in Servers |-> Max(version[i][k], version[j][k])]
        version_a == [version EXCEPT ![i] = updated]
        version_ab == [version_a EXCEPT ![j] = updated]
    IN 
        /\ version' = version_ab 
        /\ network' = RemoveMsg(m, network)

Bump(i) == 
    /\ Assert(i # 2, "")
    /\ version[i][i] # MaxVersion 
    /\ LimitDivergence(i)
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN version[i][k] ELSE version[i][k] + 1]]
    /\ UNCHANGED network

Drop(m) == 
    /\ network' = RemoveMsg(m, network)    
    /\ UNCHANGED version

Restart(i) == 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> IF i # k THEN version[i][i] - MaxDivergence ELSE version[i][i]]]
    /\ UNCHANGED network

Next ==
    \/ \E i \in Servers:
        Bump(i)
    \/ \E i, j \in Servers:
        /\ LimitNetworkOutstanding
        /\ InitiateGossip(i, j)
    \/ \E msg \in network:
        ExchangeGossip(msg)
    \/ \E i \in Servers:
        /\ Restart(i)

Liveness == 
    \E i \in Servers: 
        []<>(version[i][i] = MaxVersion)

CheckDivergence == 
    HighestVersion - LowestVersion <= MaxDivergence + 1

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \A i \in Servers: 
    SF_vars(Bump(i))
  /\ \A i, j \in Servers: 
    SF_vars(InitiateGossip(i, j))
  /\ SF_vars(\E m \in network: ExchangeGossip(m))
=============================================================================