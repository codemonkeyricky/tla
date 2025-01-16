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
    /\ ready_q = {"pid0", "pid1"}

Schedule == 
    LET 
        idle_cpus == {i \in 0..N-1 : cpus[i] = ""}
        k == CHOOSE s \in idle_cpus : TRUE
        t == CHOOSE p \in ready_q : TRUE
    IN 
        /\ idle_cpus # {}
        /\ cpus' = [cpus EXCEPT ![k] = t]
        /\ ready_q' = ready_q \ {t}

Deschedule == 
    LET 
        k == 
            IF \E x \in DOMAIN cpus: cpus[x] # ""
            THEN 
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