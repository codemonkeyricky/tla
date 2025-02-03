--------------------------- MODULE dining ----------------------------
EXTENDS Naturals, TLC
VARIABLES forks, eaten
vars == <<forks, eaten>>

P == 3
UNUSED == 100

Init ==
    /\ forks = [k \in 0.. P-1 |-> UNUSED]
    /\ eaten = [k \in 0.. P-1 |-> 0]

First(k) == IF k # P-1 THEN k ELSE 0
Second(k) == IF k # P-1 THEN k+1 ELSE k

TakeFirst(k) == 
    /\ forks[First(k)] = UNUSED
    /\ forks' = [forks EXCEPT ![First(k)] = k]
    /\ UNCHANGED eaten

TakeSecond(k) ==
    /\ forks[First(k)] = k
    /\ forks[Second(k)] = UNUSED
    /\ forks' = [forks EXCEPT ![Second(k)] = k]
    /\ UNCHANGED eaten

PutLeft(k) == 
    LET 
        left == k 
    IN 
        /\ forks[left] = k 
        /\ forks' = [forks EXCEPT ![left] = UNUSED]
        /\ UNCHANGED eaten

PutRight(k) == 
    LET 
        right == (k+1) % P
    IN 
        /\ forks[right] = k
        /\ forks' = [forks EXCEPT ![right] = UNUSED]
        /\ UNCHANGED eaten

Eat(k) == 
    LET 
        left == k 
        right == (k+1) % P
    IN 
        /\ forks[left] = k
        /\ forks[right] = k
        /\ eaten' = [eaten EXCEPT ![k] = 1 - eaten[k]]
        /\ UNCHANGED forks
    
Liveness ==
    \E k \in 0..P-1:
        /\ eaten[k] = 0 ~> eaten[k] = 1
        /\ eaten[k] = 1 ~> eaten[k] = 0

Next ==
    \/ \E k \in 0.. P-1:
        TakeFirst(k)
    \/ \E k \in 0.. P-1:
        TakeSecond(k)
    \* \/ \E k \in 0.. P-1:
    \*     TakeBoth(k)
    \/ \E k \in 0.. P-1:
        PutLeft(k)
    \/ \E k \in 0.. P-1:
        PutRight(k)
    \/ \E k \in 0.. P-1:
        Eat(k)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ \A k \in 0..P-1: 
    /\ SF_vars(TakeFirst(k))
    /\ SF_vars(TakeSecond(k))
    /\ SF_vars(Eat(k))
    \* /\ SF_vars(TakeFirst(k))
    \* /\ SF_vars(TakeSecond(k))
    \* /\ WF_vars(TakeBoth(k))
=============================================================================