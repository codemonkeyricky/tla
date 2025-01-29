--------------------------- MODULE gossip ----------------------------
EXTENDS Naturals

CONSTANTS 
    Servers

VARIABLES 
    version

\* Servers == {"s0", "s1", "s2"}

vars == <<version>> 
\* Type_OK == 
\*     /\ hour \in 0..23
\*     /\ minute \in 0..59
\* Liveness ==
\*     /\ hour = 23 /\ minute = 59 ~> hour = 0 /\ minute = 0
Init ==
    /\ version = [i \in Servers |-> [j \in Servers |-> 0]]
\* NextMinute ==
\*     /\ minute = 59 
\*     /\ hour' = (hour + 1) % 24
\*     /\ minute' = 0
\* NextHour == 
\*     /\ minute # 59
\*     /\ hour' = hour 
\*     /\ minute' = minute + 1 
Next ==
    \/ TRUE

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================