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
    /\ ready_q = {"idle"}

Schedule == 
    LET 
        idle_cpus == {i \in 0..N-1 : cpus[i] = ""}
        k == CHOOSE s \in idle_cpus : TRUE
    IN 
        /\ idle_cpus # {}
        /\ cpus' = [cpus EXCEPT ![k] = "a" ]
        /\ UNCHANGED ready_q
     \* /\ pc' = [pc EXCEPT ![self] = "r_read_buf"]


Next == 
    /\ Schedule

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
=============================================================================