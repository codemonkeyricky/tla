--------------------------- MODULE scheduler ----------------------------
EXTENDS Naturals, TLC, Sequences

\* Constants
N == 2
Tasks == <<"pid0", "pid1", "pid2", "pid3">>

VARIABLES 
    ready_q,
    blocked_q,
    cpus,
    lock_owner

vars == <<ready_q, cpus, lock_owner>>

Init ==
    /\ cpus = [i \in 0..N-1 |-> ""] 
    /\ ready_q = Tasks
    /\ blocked_q = <<>>
    /\ lock_owner = ""

\* schedule a task to a busy CPU
Ready == 
    LET 
        k ==
            IF \E x \in DOMAIN cpus: cpus[x] = "" THEN 
                CHOOSE x \in DOMAIN cpus: cpus[x] = ""
            ELSE 
                100
        t ==
            IF ready_q # <<>> THEN 
                Head(ready_q)
            ELSE 
                "none"
    IN 
        /\ k # 100
        /\ t # "none"
        /\ cpus' = [cpus EXCEPT ![k] = t]
        /\ ready_q' = Tail(ready_q)
        /\ UNCHANGED <<lock_owner, blocked_q>>

\* deschedule a task
MoveToReadyy(k) == 
    /\ k # 100
    /\ ready_q' = Append(ready_q, cpus[k]) 
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ UNCHANGED <<lock_owner, blocked_q>>

MoveToBlocked(k) == 
    /\ k # 100
    /\ blocked_q' = Append(blocked_q, cpus[k]) 
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ UNCHANGED <<lock_owner, ready_q>>

Lock(k) == 
    \* acquire lock if lock is free 
    \/  /\ k # 100
        /\ lock_owner = ""
        /\ lock_owner' = cpus[k]
        /\ UNCHANGED <<ready_q, cpus, blocked_q>>
    \* deschedule if lock is taken
    \/  /\ k # 100
        /\ lock_owner # ""
        /\ cpus[k] # lock_owner
        /\ MoveToBlocked(k)

\* unblock one blocked task
Unblock == 
    /\ blocked_q # <<>>
    /\ blocked_q' = Tail(blocked_q)
    /\ ready_q' = Append(ready_q, Head(blocked_q))
    /\ UNCHANGED <<cpus>>

Unlock(k) == 
    /\ k # 100 
    /\ lock_owner = cpus[k]
    /\ lock_owner' = ""
    /\ Unblock

Running == 
    LET 
        k == 
            IF \E x \in DOMAIN cpus: cpus[x] # "" THEN 
                CHOOSE x \in DOMAIN cpus: cpus[x] # ""
            ELSE 
                100
    IN 
        \/ MoveToReadyy(k)
        \/ Lock(k)
        \/ Unlock(k)

Next == 
    \/ Ready
    \/ Running

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================