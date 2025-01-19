--------------------------- MODULE weak ----------------------------
EXTENDS Naturals
VARIABLES a, b
vars == <<a, b>>
Liveness == 
    /\ a = 0 ~> a = 1
Init ==
    /\ a = 0
    /\ b = 0
BumpA == 
    /\ a' = (a + 1) % 2
    /\ UNCHANGED b
BumpB ==
    /\ b' = (b + 1) % 2
    /\ UNCHANGED a
Next == 
    \/ BumpA
    \/ BumpB
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
\*   /\ WF_vars(BumpA)
=============================================================================