--------------------------- MODULE pattern ----------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLES 
    v
vars == <<v>>

a == {0, 1, 2}
b == {2, 3, 4}
c == a \union b         \* \{0, 1, 2, 3, 4\}
d == a \intersect b     \* \{2\}
e == \E x \in c: x > 3  \* TRUE - because 4 in c is bigger than 3
f == \E x \in c: x > 5  \* FALSE - nothing in c is bigger than 5
g == \A x \in c: x < 3  \* FALSE - not all elements in c are smaller than 3
h == \A x \in c: x < 5  \* TRUE - all elements in c are smaller than 3
i == {x \in c: x < 3}   \* \{0, 1, 2\} - all elementse less than 3
j == Cardinality(c)     \* 5 - the number of elements in c
k == c \ d              \* \{0, 1, 3, 4\} - c substracts d

\* A == [x \in 0..2 |-> x]
\* B == [x \in 2..4 |-> x]

A == <<0, 1, 2>>                    
B == <<2, 3, 4>>
C == A \o B                         \* <<0, 1, 2, 2, 3, 4>>
D == Len(C)                         \* 6
E == \A x \in 1..Len(C) : C[x] # 10 \* TRUE - every C[x] is not 10
                                    \* First tuple element is at index 1 (not 0)
F == \E x \in 1..Len(C) : C[x] = 2  \* TRUE - there exists a C[x] that is 2
G == {x \in 1..Len(C) : C[x] = 2}   \* {3, 4} - when index is 3 or 4, C[x] = 2

c2 == Append(A, 3) 

\* gets head: 0
c3 == Head(A) 

\* removes head: 1, 2
c4 == Tail(A) 
 

Init ==
    /\ PrintT(c2)
    /\ PrintT(c3)
    /\ PrintT(c4)
    /\ PrintT(a)
    /\ PrintT(b)
    /\ PrintT(c)
    /\ PrintT(d)
    /\ PrintT(e)
    /\ PrintT(f)
    /\ PrintT(g)
    /\ PrintT(h)
    /\ PrintT(i)
    /\ PrintT(j)
    /\ PrintT(k)
    /\ PrintT(A)
    /\ PrintT(B)
    /\ PrintT(C)
    /\ PrintT(D)
    /\ PrintT(E)
    /\ PrintT(F)
    /\ PrintT(G)
    \* /\ PrintT(I)
    \* /\ PrintT(J)
    \* /\ PrintT(K)

Next ==
    \* /\ v' = A \o B
    /\ v' = v \o  <<>>

Spec ==
  /\ Init
  /\ [][Next]_vars
\*   /\ WF_vars(Next)
=============================================================================