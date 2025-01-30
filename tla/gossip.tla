--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals, FiniteSets, TLC, Naturals

CONSTANTS 
    Servers

VARIABLES 
    version

MaxVersion == 3

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

\* Ensure multiple modes have made it to MaxVersion and communicated at least once
Liveness == 
    \E i, j \in Servers: 
        /\ i # j
        /\ []<>(version[i][i] = MaxVersion /\ version[i][i] = MaxVersion /\ version[i][j] = MaxVersion)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \A i \in Servers: 
    SF_vars(Bump(i))
=============================================================================