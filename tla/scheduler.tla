--------------------------- MODULE scheduler ----------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANTS 
    N,
    Tasks

VARIABLES 
    ready_q,
    blocked_q,
    cpus,
    lock_owner

vars == <<ready_q, cpus, lock_owner>>

RECURSIVE S2T(_)
S2T(S) == IF Cardinality(S) = 0 THEN <<>>
          ELSE
          LET
            x == CHOOSE x \in S : TRUE
          IN
            <<x>> \o S2T(S \ {x})

Init ==
    /\ cpus = [i \in 0..N-1 |-> ""] 
    /\ ready_q = S2T(Tasks)
    /\ blocked_q = <<>>
    /\ lock_owner = ""

\* schedule a task to a free CPU
Ready == 
    \E t \in DOMAIN ready_q:
        \E k \in DOMAIN cpus:
        /\ cpus[k] = "" 
        /\ cpus' = [cpus EXCEPT ![k] = Head(ready_q)]
        /\ ready_q' = Tail(ready_q)
        /\ UNCHANGED <<lock_owner, blocked_q>>

\* can only move to ready if not holding a lock
MoveToReady(k) == 
    /\ cpus[k] # "" 
    /\ lock_owner # cpus[k]
    /\ ready_q' = Append(ready_q, cpus[k]) 
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ UNCHANGED <<lock_owner, blocked_q>>

\* get the lock
Lock(k) == 
    \* lock is empty
    \/  /\ cpus[k] # "" 
        /\ lock_owner = ""
        /\ lock_owner' = cpus[k]
        /\ UNCHANGED <<ready_q, cpus, blocked_q>>
    \* someone else has the lock
    \/  /\ cpus[k] # "" 
        /\ lock_owner # ""
        /\ lock_owner # cpus[k] \* cannot double lock
        /\ blocked_q' = Append(blocked_q, cpus[k])
        /\ cpus' = [cpus EXCEPT ![k] = ""]
        /\ UNCHANGED <<ready_q, lock_owner>>

\* unlock
Unlock(k) == 
    /\ cpus[k] # "" 
    /\ lock_owner = cpus[k]
    /\ lock_owner' = ""
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ ready_q' = ready_q \o blocked_q \o <<cpus[k]>>
    /\ blocked_q' = <<>>

Running == 
    \E k \in DOMAIN cpus:
        /\ cpus[k] # "" 
        /\ \/ MoveToReady(k)
           \/ Lock(k)
           \/ Unlock(k)

\* verify pid0 is eventually scheduled
Liveness == 
    \A t \in Tasks:
        LET 
            b == {x \in DOMAIN blocked_q : blocked_q[x] = t}
        IN 
            /\ b # {} ~> b = {}

Liveness2 == 
    \A t \in Tasks:
        LET 
            s == {x \in DOMAIN ready_q : ready_q[x] = t}
            b == {x \in DOMAIN blocked_q : blocked_q[x] = t}
        IN 
            /\ s # {} ~> s = {}
            /\ b # {} ~> b = {}

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