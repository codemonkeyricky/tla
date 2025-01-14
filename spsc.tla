----------------------------- MODULE spsc -----------------------------

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT M, N, Reader, Writer  \* Fixed size of the array

(*--algorithm spmc 

variables 
    rptr = 0,
    wptr = 0,
    buffer = [kk \in 0..N-1 |-> 0],

define
written == 
    IF rptr <= wptr THEN 
        {k \in rptr..wptr - 1: TRUE}
    ELSE 
        {k \in rptr..N-1: TRUE} \cup 
        {k \in 0..wptr-1: TRUE} 

writing == 
    {wptr}

reading == 
     IF rptr <= wptr THEN 
        {k \in rptr..wptr - 1: TRUE}
    ELSE 
        {k \in rptr..N-1: TRUE} \cup 
        {k \in 0..wptr-1: TRUE} 

to_be_read ==
    {k \in 0..N-1: buffer[k] # 0}

all ==
    {k \in 0..N-1: TRUE}

unused ==
    all \ (written \cup writing)

\* Confirm all indicies will be used eventually
Liveness ==
    \A k \in 0..N-1:
    <>(buffer[k] # 0)

Liveness2 ==
    /\ (\A k \in 0..N-1: buffer[k] = 0 ~> buffer[k] = 1000 + k)
    /\ (\A k \in 0..N-1: buffer[k] = 1000+k ~> buffer[k] = 0)

end define;

procedure reader(i) 
variable 
begin
r_chk_empty:        if rptr = wptr then 
r_early_ret:            return;
                    end if;
r_read_buf:         assert buffer[rptr] # 0;
r_cs:               buffer[rptr] := 0;
r_upd_rtpr:         rptr := (rptr + 1) % N;
                    return;
end procedure; 

procedure writer(i) begin
w_chk_full:         if (wptr + 1) % N = rptr then 
w_early_ret:            return; 
                    end if;
w_write_buf:        assert buffer[wptr] = 0;
w_cs:               buffer[wptr] := wptr + 1000;
w_upd_wptr:         wptr := (wptr + 1) % N;
                    return;
end procedure; 

fair process writer_0 = 100
begin 
    w_while:
    while TRUE do
        call writer(0);
    end while;
end process; 

fair process reader_0 = 101
begin 
    r_start: 
    while TRUE do
        call reader(0);
    end while;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "522fdc4e" /\ chksum(tla) = "e3208692")
\* Parameter i of procedure reader at line 52 col 18 changed to i_
CONSTANT defaultInitValue
VARIABLES rptr, wptr, buffer, pc, stack

(* define statement *)
written ==
    IF rptr <= wptr THEN
        {k \in rptr..wptr - 1: TRUE}
    ELSE
        {k \in rptr..N-1: TRUE} \cup
        {k \in 0..wptr-1: TRUE}

writing ==
    {wptr}

reading ==
     IF rptr <= wptr THEN
        {k \in rptr..wptr - 1: TRUE}
    ELSE
        {k \in rptr..N-1: TRUE} \cup
        {k \in 0..wptr-1: TRUE}

to_be_read ==
    {k \in 0..N-1: buffer[k] # 0}

all ==
    {k \in 0..N-1: TRUE}

unused ==
    all \ (written \cup writing)


Liveness ==
    \A k \in 0..N-1:
    <>(buffer[k] # 0)

Liveness2 ==
    /\ (\A k \in 0..N-1: buffer[k] = 0 ~> buffer[k] = 1000 + k)
    /\ (\A k \in 0..N-1: buffer[k] = 1000+k ~> buffer[k] = 0)

VARIABLES i_, i

vars == << rptr, wptr, buffer, pc, stack, i_, i >>

ProcSet == {100} \cup {101}

Init == (* Global variables *)
        /\ rptr = 0
        /\ wptr = 0
        /\ buffer = [kk \in 0..N-1 |-> 0]
        (* Procedure reader *)
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure writer *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 100 -> "w_while"
                                        [] self = 101 -> "r_start"]

r_chk_empty(self) == /\ pc[self] = "r_chk_empty"
                     /\ IF rptr = wptr
                           THEN /\ pc' = [pc EXCEPT ![self] = "r_early_ret"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "r_read_buf"]
                     /\ UNCHANGED << rptr, wptr, buffer, stack, i_, i >>

r_early_ret(self) == /\ pc[self] = "r_early_ret"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << rptr, wptr, buffer, i >>

r_read_buf(self) == /\ pc[self] = "r_read_buf"
                    /\ Assert(buffer[rptr] # 0, 
                              "Failure of assertion at line 58, column 21.")
                    /\ pc' = [pc EXCEPT ![self] = "r_cs"]
                    /\ UNCHANGED << rptr, wptr, buffer, stack, i_, i >>

r_cs(self) == /\ pc[self] = "r_cs"
              /\ buffer' = [buffer EXCEPT ![rptr] = 0]
              /\ pc' = [pc EXCEPT ![self] = "r_upd_rtpr"]
              /\ UNCHANGED << rptr, wptr, stack, i_, i >>

r_upd_rtpr(self) == /\ pc[self] = "r_upd_rtpr"
                    /\ rptr' = (rptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << wptr, buffer, i >>

reader(self) == r_chk_empty(self) \/ r_early_ret(self) \/ r_read_buf(self)
                   \/ r_cs(self) \/ r_upd_rtpr(self)

w_chk_full(self) == /\ pc[self] = "w_chk_full"
                    /\ IF (wptr + 1) % N = rptr
                          THEN /\ pc' = [pc EXCEPT ![self] = "w_early_ret"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "w_write_buf"]
                    /\ UNCHANGED << rptr, wptr, buffer, stack, i_, i >>

w_early_ret(self) == /\ pc[self] = "w_early_ret"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << rptr, wptr, buffer, i_ >>

w_write_buf(self) == /\ pc[self] = "w_write_buf"
                     /\ Assert(buffer[wptr] = 0, 
                               "Failure of assertion at line 68, column 21.")
                     /\ pc' = [pc EXCEPT ![self] = "w_cs"]
                     /\ UNCHANGED << rptr, wptr, buffer, stack, i_, i >>

w_cs(self) == /\ pc[self] = "w_cs"
              /\ buffer' = [buffer EXCEPT ![wptr] = wptr + 1000]
              /\ pc' = [pc EXCEPT ![self] = "w_upd_wptr"]
              /\ UNCHANGED << rptr, wptr, stack, i_, i >>

w_upd_wptr(self) == /\ pc[self] = "w_upd_wptr"
                    /\ wptr' = (wptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << rptr, buffer, i_ >>

writer(self) == w_chk_full(self) \/ w_early_ret(self) \/ w_write_buf(self)
                   \/ w_cs(self) \/ w_upd_wptr(self)

w_while == /\ pc[100] = "w_while"
           /\ /\ i' = [i EXCEPT ![100] = 0]
              /\ stack' = [stack EXCEPT ![100] = << [ procedure |->  "writer",
                                                      pc        |->  "w_while",
                                                      i         |->  i[100] ] >>
                                                  \o stack[100]]
           /\ pc' = [pc EXCEPT ![100] = "w_chk_full"]
           /\ UNCHANGED << rptr, wptr, buffer, i_ >>

writer_0 == w_while

r_start == /\ pc[101] = "r_start"
           /\ /\ i_' = [i_ EXCEPT ![101] = 0]
              /\ stack' = [stack EXCEPT ![101] = << [ procedure |->  "reader",
                                                      pc        |->  "r_start",
                                                      i_        |->  i_[101] ] >>
                                                  \o stack[101]]
           /\ pc' = [pc EXCEPT ![101] = "r_chk_empty"]
           /\ UNCHANGED << rptr, wptr, buffer, i >>

reader_0 == r_start

Next == writer_0 \/ reader_0
           \/ (\E self \in ProcSet: reader(self) \/ writer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(writer_0) /\ WF_vars(writer(100))
        /\ WF_vars(reader_0) /\ WF_vars(reader(101))

\* END TRANSLATION 

\* reader and writer cannot operator on the same index
MUTEX ==
    ~ ((pc[100] = "w_cs") /\ (pc[101] = "r_cs") /\ rptr = wptr)

Inv_Basics == 
    /\ ((written \cup writing) \cup unused) = all
    /\ reading \subseteq written                            \* reading is a subset of written
    \* /\ to_read \subseteq written                            \* to_read is a subset of written
    \* /\ read_reserved \intersect unused = {}
    \* /\ (reading \cup to_read) = written
    /\ \A kk \in unused : buffer[kk] = 0
    \* /\ \A kk \in written : buffer[kk] # 0
    \* /\ (reading \cup to_read) = written
    \* /\ \A kk \in to_read : buffer[kk] # 0                     \* to_read must be populated
    \* /\ \A kk \in read_reserved : buffer[kk] # 0
    \* /\ \A kk \in reading : rrsvd[kk] = 0 => buffer[kk] = 0     \* part of reading but not reserved - read done.
    \* /\ \A kk \in reading : rrsvd[kk] # 0 => buffer[kk] # 0     \* part of reading but reserved - read in progress.
    \* /\ Cardinality(read_reserved) <= Reader                 \* at most 'Reader' indices can be reserved
    /\ \/ Cardinality(to_be_read) + 1 = Cardinality(reading) 
       \/ Cardinality(to_be_read)     = Cardinality(reading) + 1
       \/ Cardinality(to_be_read)     = Cardinality(reading)
    /\ MUTEX

===============================================================================
