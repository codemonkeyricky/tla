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

\* deschedule a busy CPU
Deschedule == 
    LET 
        k == 
            IF \E x \in DOMAIN cpus: cpus[x] # "" THEN 
                CHOOSE x \in DOMAIN cpus: cpus[x] # ""
            ELSE 
                100
    IN 
        /\ k # 100
        /\ ready_q' = Append(ready_q, cpus[k]) 
        /\ cpus' = [cpus EXCEPT ![k] = ""]
        /\ UNCHANGED lock_owner


\* any running thread can acquire lock
Lock == 
    LET 
        k == 
            IF \E x \in DOMAIN cpus: cpus[x] # "" THEN 
                CHOOSE x \in DOMAIN cpus: cpus[x] # ""
            ELSE 
                100
    IN 
        /\ k # 100
        /\ lock_owner = ""
        /\ lock_owner' = cpus[k]
        /\ UNCHANGED <<ready_q, cpus>>

Unlock == 
    LET 
        k == 
            IF \E x \in DOMAIN cpus: lock_owner # "" /\ cpus[x] = lock_owner THEN 
                CHOOSE x \in DOMAIN cpus: cpus[x] = lock_owner
            ELSE 
                100
    IN 
        /\ k # 100 
        /\ lock_owner' = ""
        /\ UNCHANGED <<ready_q, cpus>>

Running == 
    \/ Deschedule
    \/ Lock
    \/ Unlock

Next == 
    \/ Read
    \/ Running

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================