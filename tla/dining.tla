--------------------------- MODULE dining ----------------------------
EXTENDS Naturals, TLC
VARIABLES forks, eaten
vars == <<forks, eaten>>

P == 3
UNUSED == 100

Init ==
    /\ forks = [k \in 0.. P-1 |-> UNUSED]
    /\ eaten = [k \in 0.. P-1 |-> 0]

First(k) == k
Second(k) == (k+1 )% P
\* First(k) == IF k # P-1 THEN k ELSE 0
\* Second(k) == IF k # P-1 THEN k+1 ELSE k

TakeFirst(k) == 
    /\ eaten[k] = 0
    /\ forks[First(k)] = UNUSED
    /\ forks' = [forks EXCEPT ![First(k)] = k]
    \* /\ PrintT(forks')
    /\ UNCHANGED eaten

TakeSecond(k) ==
    /\ eaten[k] = 0
    /\ forks[First(k)] = k
    /\ forks[Second(k)] = UNUSED
    /\ forks' = [forks EXCEPT ![Second(k)] = k]
    /\ UNCHANGED eaten

Eat(k) == 
    LET 
        left == k 
        right == (k+1) % P
    IN 
        /\ forks[left] = k
        /\ forks[right] = k
        /\ eaten' = [eaten EXCEPT ![k] = 1]
        /\ UNCHANGED forks

PutFirst(k) == 
    /\ eaten[k] = 1
    /\ forks[First(k)] = k 
    /\ forks' = [forks EXCEPT ![First(k)] = UNUSED]
    /\ UNCHANGED eaten

PutSecond(k) == 
    /\ eaten[k] = 1
    /\ forks[First(k)] # k 
    /\ forks[Second(k)] = k 
    /\ forks' = [forks EXCEPT ![Second(k)] = UNUSED]
    /\ eaten' = [eaten EXCEPT ![k] = 0]

Liveness ==
    \E k \in 0..P-1:
        /\ eaten[k] = 0 ~> eaten[k] = 1
        /\ eaten[k] = 1 ~> eaten[k] = 0

Next ==
    \/ \E k \in 0.. P-1:
        TakeFirst(k)
    \/ \E k \in 0.. P-1:
        TakeSecond(k)
    \/ \E k \in 0.. P-1:
        Eat(k)
    \/ \E k \in 0.. P-1:
        PutFirst(k)
    \/ \E k \in 0.. P-1:
        PutSecond(k)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
\*   /\ \A k \in 0..P-1:
\*     WF_vars(PutFirst(k))
=============================================================================