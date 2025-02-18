--------------------------- MODULE dropbox ----------------------------
EXTENDS Naturals
VARIABLES counter 
vars == <<counter>>

Init ==
    /\ counter = 0

Next ==
    /\ TRUE

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================