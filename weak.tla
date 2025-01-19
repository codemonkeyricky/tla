--------------------------- MODULE weak ----------------------------
EXTENDS Naturals

VARIABLES c
vars == <<c>>

Liveness == 
    /\ c[0] = 0 ~> c[0] = 1

Init ==
    /\ c = [i \in 0..1|-> 0] 

MoveOne == 
    /\ c' = [c EXCEPT ![1] = (c[1] + 1) % 2]

MoveBoth ==
    /\ c' = [i \in 0..1 |-> (c[i] + 1) % 2]

Next == 
    \/ MoveOne
    \/ MoveBoth

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
\*   /\ WF_vars(MoveBoth)
=============================================================================