--------------------------- MODULE scheduler ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, SequencesExt

CONSTANTS 
    N, Tasks


VARIABLES 
    ready_q,
    blocked_q,
    blocked,
    cpus,
    lock_owner

vars == <<ready_q, blocked_q, blocked, cpus, lock_owner>>

Init ==
    /\ cpus = [i \in 0..N-1 |-> ""] 
    /\ ready_q = SetToSeq(Tasks)
    /\ blocked_q = <<>>
    /\ blocked = [t \in Tasks |-> 0]
    /\ lock_owner = ""

\* schedule a task to a free CPU
Ready == 
    \E t \in DOMAIN ready_q:
        \E k \in DOMAIN cpus:
        /\ cpus[k] = "" 
        /\ cpus' = [cpus EXCEPT ![k] = Head(ready_q)]
        /\ ready_q' = Tail(ready_q)
        /\ UNCHANGED <<lock_owner, blocked_q, blocked>>

\* can only move to ready if not holding a lock
MoveToReady(k) == 
    /\ cpus[k] # "" 
    /\ lock_owner # cpus[k]
    /\ ready_q' = Append(ready_q, cpus[k]) 
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ UNCHANGED <<lock_owner, blocked_q, blocked>>

\* get the lock
Lock(k) == 
    \* lock is empty
    \/  /\ cpus[k] # "" 
        /\ lock_owner = ""
        /\ lock_owner' = cpus[k]
        /\ UNCHANGED <<ready_q, cpus, blocked_q, blocked>> 
    \* someone else has the lock
    \/  /\ cpus[k] # "" 
        /\ lock_owner # ""
        /\ lock_owner # cpus[k] \* cannot double lock
        /\ blocked_q' = Append(blocked_q, cpus[k])
        /\ blocked' = [blocked EXCEPT ![cpus[k]] = 1]
        /\ cpus' = [cpus EXCEPT ![k] = ""]
        /\ UNCHANGED <<ready_q, lock_owner>>

\* unlock
Unlock(k) == 
    \/  /\ cpus[k] # "" 
        /\ Len(blocked_q) # 0
        /\ lock_owner = cpus[k]
        /\ lock_owner' = Head(blocked_q)
        /\ cpus' = [cpus EXCEPT ![k] = Head(blocked_q)]
        /\ ready_q' = ready_q \o <<cpus[k]>>
        /\ blocked_q' = Tail(blocked_q)
        /\ blocked' = [blocked EXCEPT ![Head(blocked_q)] = 0]
    \/  /\ cpus[k] # "" 
        /\ Len(blocked_q) = 0
        /\ lock_owner' = ""
        /\ UNCHANGED <<ready_q, blocked_q, blocked, cpus>>

Running == 
    \E k \in DOMAIN cpus:
        \/ MoveToReady(k)
        \/ Lock(k)
        \/ Unlock(k)

Liveness == 
    \A t \in Tasks:
        blocked[t] = 1 ~> FALSE \*lock_owner = t

Next == 
    \/ Running
    \/ Ready

HoldingLock(t) == 
    /\ lock_owner = t

L ==
    \A t \in Tasks :
        \A n \in 0..(N-1) :
            WF_vars(HoldingLock(t) /\ Unlock(n))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ L 
=============================================================================