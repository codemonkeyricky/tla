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
    \* /\ Assert(0,"")

\* can only move to ready if not holding a lock
MoveToReady(k) == 
    /\ cpus[k] # "" 
    /\ lock_owner # cpus[k]
    /\ ready_q' = Append(ready_q, cpus[k]) 
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ UNCHANGED <<lock_owner, blocked_q>>
    \* /\ Assert(0,"")

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
    LET 
        s == {x \in DOMAIN ready_q : ready_q[x] = "pid0"}
        b == {x \in DOMAIN blocked_q : blocked_q[x] = "pid0"}
    IN 
        /\ WF_vars(Ready)
        /\ WF_vars(Running)
        /\ s # {} ~> s = {}
        /\ b # {} ~> b = {}

Next == 
    \/ Running
    \/ Ready

\* v == 
\*     <<>>

HoldingLock2 == 
    /\ lock_owner = "pid2"

L == 
    /\ SF_vars(Unlock(1) /\ HoldingLock2)
    /\ SF_vars(Unlock(0) /\ HoldingLock2)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ L 
=============================================================================