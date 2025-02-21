--------------------------- MODULE dynamo ----------------------------
EXTENDS Naturals
VARIABLES counter 
vars == <<counter>>
EventuallyAlways == <>[](counter = 3)
AlwaysEventually == []<>(counter = 3)
LeadsTo == counter = 4 ~> counter = 3

Init ==
    /\ counter = 0
Inc == 
    /\ counter' = counter + 1
Dec == 
    /\ counter' = counter - 1

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