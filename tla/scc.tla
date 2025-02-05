--------------------------- MODULE scc ----------------------------
EXTENDS Naturals, TLC, Sequences
VARIABLES phase, edges, new_edges, in, out, updated, converged
vars == <<edges>>

Vertex == {0, 1, 2, 3}

Edges == {<<0,1>>, <<1,2>>, <<2,3>>, <<3,0>>}

INIT    == "Init"
UPDATE  == "Update"
TRIM    == "Trim"

Max(a, b) == IF a > b THEN a ELSE b

Init ==
    /\ phase = "Init"
    /\ new_edges = Edges
    /\ edges = new_edges 
    /\ in = [k \in Vertex |-> k]
    /\ out = [k \in Vertex |-> k]
    /\ updated = 0
    /\ converged = 0

PhaseInit == 
    /\ phase = "Init" 
    /\ phase' = "Update"
    /\ edges' = new_edges
    /\ new_edges' = new_edges
    /\ in' = [k \in Vertex |-> k]
    /\ out' = [k \in Vertex |-> k]
    /\ updated' = 0
    /\ converged' = 0

PhaseUpdate == 
    /\ phase = "Update"
    /\ \/ /\ \E e \in edges: 
            LET 
                src == e[1]
                dst == e[2]
            IN 
                /\ in' = [in EXCEPT ![dst] = Max(in[src], in[dst])]
                /\ out' = [out EXCEPT ![src] = Max(out[src], out[dst])]
                /\ edges' = edges \ {e}
                /\ \/ /\ in' # in \/ out' # out
                      /\ updated' = 1
                   \/ /\ in' = in /\ out' = out
                      /\ updated' = 0
          /\ UNCHANGED <<new_edges, phase, converged>>
       \/ /\ edges = {}
          /\ updated = 0
          /\ phase' = "Trim"
          /\ UNCHANGED <<edges, new_edges, in, out, updated, converged>>
       \/ /\ edges = {}
          /\ updated # 0
          /\ edges' = new_edges
          /\ UNCHANGED <<phase, new_edges, in, out, updated, converged>>

PhaseTrim == 
    /\ phase = "Trim"
    /\ \/ /\ edges = {}
          /\ in = out
          /\ converged' = 1
        \*   /\ Assert(0,"")
          /\ UNCHANGED <<phase, new_edges, edges, in, out, updated>>
       \/ /\ edges = {}
          /\ in # out
          /\ phase' = "Init"
          /\ UNCHANGED <<in, new_edges, edges, out, updated, converged>>
       \/ /\ edges # {}
          /\ \E e \in edges:
            LET 
                src == e[1]
                dst == e[2]
            IN
                /\ \/ /\ out[src] # out[dst] \/ in[src] # in[dst]
                      /\ new_edges' = new_edges \ {e}
                   \/ /\ out[src] = out[dst] /\ in[src] = in[dst]
                      /\ UNCHANGED new_edges
                /\ edges' = edges \ {e}
          /\ UNCHANGED <<phase, in, out, updated, converged>>

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