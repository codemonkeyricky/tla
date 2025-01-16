--------------------------- MODULE scheduler ----------------------------
EXTENDS Naturals, TLC, Sequences

\* Constants
N == 2
Tasks == <<"pid0", "pid1", "pid2", "pid3">>

VARIABLES 
    ready_q,
    cpus

vars == <<ready_q, cpus>>

Init ==
    /\ cpus = [i \in 0..N-1 |-> ""] 
    /\ ready_q = Tasks

\* schedule a task to a busy CPU
Schedule == 
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

Next == 
    \/ Schedule
    \/ Deschedule

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================