--------------------------- MODULE dining ----------------------------
EXTENDS Naturals, TLC
VARIABLES forks, eaten
vars == <<forks, eaten>>

\*  P == {"p0", "p1", "p2"}
\* forks == {"p0", "p1", "p2"}

P == 2
UNUSED == 100

Init ==
    /\ forks = [k \in 0.. P-1 |-> UNUSED]
    /\ eaten = [k \in 0.. P-1 |-> 0]

TakeLeft(k) == 
    LET 
        left == k 
    IN 
        /\ forks[left] = UNUSED
        /\ forks' = [forks EXCEPT ![left] = k]
        /\ UNCHANGED eaten

TakeRight(k) == 
    LET 
        right == (k+1) % P
    IN 
        /\ forks[right] = UNUSED
        /\ forks' = [forks EXCEPT ![right] = k]
        /\ UNCHANGED eaten

TakeBoth(k) == 
    LET 
        left == k 
        right == (k+1) % P
        forkp == [forks EXCEPT ![left] = k]
        forkpp == [forkp EXCEPT ![right] = k]
    IN 
        /\ forks[left] = UNUSED
        /\ forks[right] = UNUSED
        /\ forks' = forkpp
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
        \* forksp == [forks EXCEPT ![left] = ""]
        \* forkspp == [forksp EXCEPT ![right] = ""]
    IN 
        \* /\ PrintT("eat")
        /\ forks[left] = k
        /\ forks[right] = k
        /\ eaten' = [eaten EXCEPT ![k] = 1 - eaten[k]]
        \* /\ forks' = forkspp
        /\ UNCHANGED forks
    
Liveness ==
    \E k \in 0..P-1:
        /\ eaten[k] = 0 ~> eaten[k] = 1
        /\ eaten[k] = 1 ~> eaten[k] = 0

Next ==
    \* \/ \E k \in 0.. P-1:
    \*     TakeLeft(k)
    \* \/ \E k \in 0.. P-1:
    \*     TakeRight(k)
    \/ \E k \in 0.. P-1:
        TakeBoth(k)
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
    \* /\ SF_vars(TakeLeft(k))
    /\ SF_vars(Eat(k))
    \* /\ SF_vars(TakeLeft(k))
    \* /\ SF_vars(TakeRight(k))
    \* /\ WF_vars(TakeBoth(k))
=============================================================================