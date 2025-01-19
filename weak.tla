--------------------------- MODULE weak ----------------------------

EXTENDS Naturals

VARIABLES s
vars == <<s>>

Init ==
    /\ s = 0

Move == 
    /\ s' = (s + 1) % 8

Stay == 
    /\ UNCHANGED s 

Next == 
    \/ Move 
    \/ Stay 

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================