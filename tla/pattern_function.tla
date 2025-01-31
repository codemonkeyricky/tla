--------------------------- MODULE pattern_function ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLES 
    v
vars == <<v>>

SetA == {"a", "b", "c"}
SetB == {"c", "d", "e"}

\* Create a mapping with keys a, b, c with values 0, 0, 0
a == [k \in SetA |-> 0]
b == [k \in SetB |-> 1]
\* Concatenate 
c == a @@ b
\* Subtraction
d == [x \in (DOMAIN c \ DOMAIN b) |-> c[x]]
\* Create a mapping with keys a, b, c with values {}, {}, {}
e == [k \in SetA |-> {}]
\* Create a mapping that is the same as e, except key a's value is {"a", "b", "c"}
f == [e EXCEPT !["a"] = {"a", "b", "c"}] 

Init ==
    /\ PrintT(a)
    /\ PrintT(b)
    /\ PrintT(c)
    /\ PrintT(d)
    /\ PrintT(e)
    /\ PrintT(f)
    \* /\ PrintT(b)
    \* /\ PrintT(c)
    \* /\ PrintT(d)
    \* /\ PrintT(e)
    \* /\ PrintT(f)
    \* /\ PrintT(g)
    \* /\ PrintT(h)
    \* /\ PrintT(i)
    \* /\ PrintT(j)
    \* /\ PrintT(k)
    \* /\ PrintT(A)
    \* /\ PrintT(B)
    \* /\ PrintT(C)
    \* /\ PrintT(D)
    \* /\ PrintT(E)
    \* /\ PrintT(F)
    \* /\ PrintT(G)
    \* \* /\ PrintT(I)
    \* /\ PrintT(J)
    \* /\ PrintT(K)

Next ==
    \* /\ v' = A \o B
    /\ TRUE

Spec ==
  /\ Init
  /\ [][Next]_vars
\*   /\ WF_vars(Next)
=============================================================================