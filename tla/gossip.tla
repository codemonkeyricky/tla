--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals, FiniteSets, TLC, Naturals

CONSTANTS 
    Servers

VARIABLES 
    version, ready

MaxDivergence == 1
MaxVersion == 3
MaxNetworkOutstanding == 1

vars == <<version, ready>> 

Init ==
    /\ version = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ ready = [i \in Servers |-> 1]

HighestVersion ==
    LET Values == {version[i][j] : i \in Servers, j \in Servers}
    IN IF Values = {} THEN 0 ELSE CHOOSE x \in Values : \A y \in Values : y <= x

\* LowestVersion ==
\*     LET Values == {version[i][j] : i \in Servers, j \in Servers}
\*     IN IF Values = {} THEN 0 ELSE CHOOSE x \in Values : \A y \in Values : y >= x

\* LimitDivergence(i) == 
\*     \/ version[i][i] # HighestVersion
\*     \/ /\ version[i][i] = HighestVersion
\*        /\ HighestVersion - LowestVersion < MaxDivergence

ExchangeGossip(i, j) == 
    LET 
        Max(a, b) == IF a > b THEN a ELSE b
        updated == [k \in Servers |-> Max(version[i][k], version[j][k])]
        version_a == [version EXCEPT ![i] = updated]
        version_ab == [version_a EXCEPT ![j] = updated]
    IN 
        \* /\ ready[i] = 1
        /\ version' = version_ab 
        /\ ready' = [ready EXCEPT ![j] = 1]

Bump(i) == 
    /\ version[i][i] # MaxVersion 
    \* /\ ready[i] = 1
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN version[i][k] ELSE version[i][k] + 1]]
    /\ UNCHANGED <<ready>>

Restart(i) == 
    \* /\ ready[i] = 1
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN 0 ELSE version[i][i]]]
    /\ ready' = [ready EXCEPT ![i] = 0]

Next ==
    \/ \E i \in Servers:
        /\ Bump(i)
    \/ \E i, j \in Servers:
        /\ ExchangeGossip(i, j)
    \/ \E i \in Servers:
        \* /\ version[i][i] # HighestVersion
        /\ Cardinality({s \in Servers : ready[s] = 1}) > 1
        /\ Restart(i)

Liveness == 
    \E i \in Servers: 
        []<>(version[i][i] = MaxVersion)

\* CheckDivergence == 
\*     HighestVersion - LowestVersion <= MaxDivergence + 1

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \E i \in Servers: 
    SF_vars(Bump(i))
\*   /\ \A i \in Servers: 
\*     SF_vars(Restart(i))
\*   /\ \A i,j \in Servers: 
\*     SF_vars(ExchangeGossip(i,j))
=============================================================================