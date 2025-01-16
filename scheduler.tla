--------------------------- MODULE scheduler ----------------------------
EXTENDS Naturals, TLC

CONSTANTS
    N, Tasks

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
            IF ready_q # {} THEN 
                CHOOSE x \in ready_q : TRUE 
            ELSE 
                "none"
    IN 
        /\ k # 100
        /\ t # "none"
        /\ cpus' = [cpus EXCEPT ![k] = t]
        /\ ready_q' = ready_q \ {t}

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
        /\ ready_q' = ready_q \union {cpus[k]} 
        /\ cpus' = [cpus EXCEPT ![k] = ""]

Next == 
    \/ Schedule
    \/ Deschedule

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================