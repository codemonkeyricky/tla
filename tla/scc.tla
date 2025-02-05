--------------------------- MODULE scc ----------------------------
EXTENDS Naturals, TLC, Sequences
VARIABLES edges, phase, vout, vin, updated, converged
vars == <<edges>>

Vertex == {0, 1, 2, 3}

Edges == {<<0,1>>, <<1,2>>, <<2,0>>, <<3,3>>}

INIT    == "Init"
UPDATE  == "Update"
TRIM    == "Trim"

Max(a, b) == IF a > b THEN a ELSE b

Init ==
    /\ phase = "Init"
    /\ edges = Edges 
    /\ vin = [k \in Vertex |-> k]
    /\ vout = [k \in Vertex |-> k]
    /\ updated = 0
    /\ converged = 0

PhaseInit == 
    /\ phase = "Init" 
    /\ phase' = "Update"
    /\ vin' = [k \in Vertex |-> k]
    /\ vout' = [k \in Vertex |-> k]
    /\ edges' = Edges
    /\ updated' = 0
    /\ converged' = 0

PhaseUpdate == 
    /\ phase = "Update"
    /\ \/ /\ \E e \in edges: 
            LET 
                src == e[1]
                dst == e[2]
            IN 
                /\ vin' = [vin EXCEPT ![dst] = Max(vin[src], vin[dst])]
                /\ vout' = [vout EXCEPT ![src] = Max(vout[src], vout[dst])]
                /\ edges' = edges \ {e}
                /\ \/ /\ vin' # vin \/ vout' # vout
                      /\ updated' = 1
                   \/ /\ vin' = vin /\ vout' = vout
                      /\ updated' = 0
          /\ UNCHANGED <<phase, converged>>
       \/ /\ edges = {}
          /\ updated = 0
          /\ phase' = "Trim"
          /\ UNCHANGED <<edges, vin, vout, updated, converged>>
       \/ /\ edges = {}
          /\ updated # 0
          /\ edges' = Edges
          /\ UNCHANGED <<phase, vin, vout, updated, converged>>

PhaseTrim == 
    /\ phase = "Trim"
    /\ \/ /\ vin = vout
          /\ converged' = 1
          /\ UNCHANGED <<phase, edges, vin, vout, updated>>
       \/ /\ vin # vout
          /\ phase' = "Init"
          /\ UNCHANGED <<vin, edges, vout, updated, converged>>

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