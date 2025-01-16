--------------------------- MODULE scheduler ----------------------------
EXTENDS Naturals, TLC, Sequences

\* Constants
N == 2
Tasks == <<"pid0", "pid1", "pid2", "pid3">>

VARIABLES 
    ready_q,
    cpus,
    lock_owner

vars == <<ready_q, cpus, lock_owner>>

Init ==
    /\ cpus = [i \in 0..N-1 |-> ""] 
    /\ ready_q = Tasks
    /\ lock_owner = ""

\* schedule a task to a busy CPU
Read == 
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
        /\ UNCHANGED lock_owner

\* deschedule a task
Deschedule(k) == 
    /\ k # 100
    /\ ready_q' = Append(ready_q, cpus[k]) 
    /\ cpus' = [cpus EXCEPT ![k] = ""]
    /\ UNCHANGED lock_owner

Lock(k) == 
    \* acquire lock if lock is free 
    \/  /\ k # 100
        /\ lock_owner = ""
        /\ lock_owner' = cpus[k]
        /\ UNCHANGED <<ready_q, cpus>>
    \* deschedule if lock is taken
    \/  /\ k # 100
        /\ lock_owner # ""
        /\ Deschedule(k)

Unlock(k) == 
    /\ k # 100 
    /\ lock_owner = cpus[k]
    /\ lock_owner' = ""
    /\ UNCHANGED <<ready_q, cpus>>

Running == 
    LET 
        k == 
            IF \E x \in DOMAIN cpus: cpus[x] # "" THEN 
                CHOOSE x \in DOMAIN cpus: cpus[x] # ""
            ELSE 
                100
    IN 
        \/ Deschedule(k)
        \/ Lock(k)
        \/ Unlock(k)

Next == 
    \/ Read
    \/ Running

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================