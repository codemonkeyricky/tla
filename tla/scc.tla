--------------------------- MODULE scc ----------------------------
EXTENDS Naturals, TLC
VARIABLES edges, phase, vout, vin
vars == <<edges>>

Vertex == {0, 1, 2}

Edges == {{0,1}, {1,0}, {2,2}}

INIT    == "Init"
UPDATE  == "Update"
TRIM    == "Trim"

Max(a, b) == IF a > b THEN a ELSE b

Init ==
    /\ phase = "Init"
    /\ edges = Edges 
    /\ vin = [k \in Vertex |-> k]
    /\ vout = [k \in Vertex |-> k]

PhaseInit == 
    /\ phase = "Init" 
    /\ phase' = "Update"

PhaseUpdate == 
    /\ phase = "Update"
    /\ \/ /\ \E e \in edges: 
                /\ vin' = [vin EXCEPT ![e] = {}]
                /\ vout' = [vin EXCEPT ![e] = {}]
                /\ edges' = edges \ {e}
          /\ UNCHANGED <<phase>>
       \/ /\ edges = {}
          /\ phase' = "Trim"

PhaseTrim == 
    /\ phase = "Trim"

Next == 
    \/ PhaseInit
    \/ PhaseUpdate
    \/ PhaseTrim

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
\*   /\ \A k \in 0..P-1:
\*     WF_vars(PutFirst(k))
=============================================================================