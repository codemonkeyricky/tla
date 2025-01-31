--------------------------- MODULE liveness ----------------------------
EXTENDS Naturals
VARIABLES counter 
vars == <<counter>>
Init ==
    /\ counter = 0
Inc == 
    /\ counter' = counter + 1
Dec == 
    /\ counter' = counter - 1
EventuallyAlways ==
    <>[](counter = 3)
AlwaysEventually ==
    []<>(counter = 3)
Next ==
    \/ /\ counter # 3
       /\ Inc
    \/ /\ counter = 3
       /\ Dec
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================