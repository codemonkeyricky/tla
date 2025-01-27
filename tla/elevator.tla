--------------------------- MODULE elevator ----------------------------
EXTENDS Integers
VARIABLES a
vars == <<a>>

TOP == 4
BOTTOM == 1

Liveness ==
    /\ a = 1 ~> a = TOP

Init ==
    /\ a = 1
Up == 
    /\ a # TOP
    /\ a' = a + 1
Down == 
    /\ a # BOTTOM
    /\ a' = a - 1

Spec ==
  /\ Init
  /\ [][Up \/ Down]_a
  /\ WF_a(Down)
  /\ \A f \in BOTTOM..TOP-1: 
    /\ SF_a(Up /\ f = a)
=============================================================================
