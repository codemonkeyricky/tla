--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Servers

VARIABLES 
    version, ready

MaxDivergence == 1
MaxVersion == 3
MaxNetworkOutstanding == 1

vars == <<version, ready >> 

Init ==
    /\ version = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ ready = [i \in Servers |-> 1]

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

\* LimitNetworkOutstanding ==
\*     Cardinality(network) < MaxNetworkOutstanding

ExchangeGossip(i, j) == 
    LET 
        Max(a, b) == IF a > b THEN a ELSE b
        updated == [k \in Servers |-> Max(version[i][k], version[j][k])]
        version_a == [version EXCEPT ![i] = updated]
        version_ab == [version_a EXCEPT ![j] = updated]
    IN 
        /\ version' = version_ab 
        /\ ready' = [ready EXCEPT ![i] = 1]

Bump(i) == 
    /\ version[i][i] # MaxVersion 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN version[i][k] ELSE version[i][k] + 1]]
    /\ UNCHANGED <<ready>>

Restart(i) == 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN 0 ELSE version[i][i]]]
    /\ ready' = [ready EXCEPT ![i] = 0]

Next ==
    \/ \E i \in Servers:
        /\ ready[i] = 1
        /\ Bump(i)
    \/ \E i, j \in Servers:
        /\ ready[i] = 1
        /\ ExchangeGossip(i, j)
    \/ \E i \in Servers:
        /\ ready[i] = 1
        /\ Cardinality({s \in Servers : ready[s] = 1}) > 1
        /\ Restart(i)

Liveness == 
    \A i,j \in Servers: 
        <>[](version[i][j] = MaxVersion)

CheckDivergence == 
    HighestVersion - LowestVersion <= MaxDivergence + 1

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \A i \in Servers: 
    SF_vars(Bump(i))
=============================================================================