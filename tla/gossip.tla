--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals, FiniteSets, TLC, Naturals

CONSTANTS 
    Servers

VARIABLES 
    version

MaxDivergence == 1
MaxVersion == 3
MaxNetworkOutstanding == 1

vars == <<version>> 

Init ==
    /\ version = [i \in Servers |-> [j \in Servers |-> 0]]

ExchangeGossip(i, j) == 
    LET 
        Max(a, b) == IF a > b THEN a ELSE b
        updated == [k \in Servers |-> Max(version[i][k], version[j][k])]
        version_a == [version EXCEPT ![i] = updated]
        version_ab == [version_a EXCEPT ![j] = updated]
    IN 
        /\ version' = version_ab 

Bump(i) == 
    /\ version[i][i] # MaxVersion 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN version[i][k] ELSE version[i][k] + 1]]

Restart(i) == 
    /\ version' = [version EXCEPT ![i] = [k \in Servers |-> 
        IF i # k THEN 0 ELSE version[i][i]]]

Next ==
    \/ \E i \in Servers:
        /\ Bump(i)
    \/ \E i, j \in Servers:
        /\ ExchangeGossip(i, j)
    \/ \E i \in Servers:
        /\ Restart(i)

Liveness == 
    \E i \in Servers: 
        []<>(version[i][i] = MaxVersion)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \E i \in Servers: 
    SF_vars(Bump(i))
=============================================================================