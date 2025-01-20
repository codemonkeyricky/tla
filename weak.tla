--------------------------- MODULE weak ----------------------------
EXTENDS Naturals
VARIABLES a, b,c
vars == <<a, b,c >>
Liveness == 
    /\ b = 0 ~> b = 1
Init ==
    /\ a = 0
    /\ b = 0
    /\ c = 0
FlipA == 
    /\ a' = 1 - a
    /\ UNCHANGED <<b,c>>
FlipB ==
    /\ b' = 1 - b
    /\ UNCHANGED <<a,c>>
FlipC ==
    /\ c' = 1 - c
    /\ UNCHANGED <<a,b>>
FlipBorC == 
    \/ FlipB
    \/ FlipC
Next == 
    \/ FlipA
    \/ FlipB
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
\*   /\ SF_vars(FlipBorC)
=============================================================================