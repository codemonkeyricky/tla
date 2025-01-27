----------------------------- MODULE spsc -----------------------------

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT M, N, Reader, Writer  \* Fixed size of the array

(*--algorithm spmc 

variables 
    rptr = 0,
    wptr = 0,
    buffer = [i \in 0..N-1 |-> 0],

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


READER == 0
WRITER == 1

end define;

procedure reader()
begin
r_chk_empty:        if rptr = wptr then 
r_early_ret:            return;
                    end if;
r_read_buf:         assert buffer[rptr] # 0;
r_cs:               buffer[rptr] := 0;
r_upd_rtpr:         rptr := (rptr + 1) % N;
                    return;
end procedure; 

procedure writer() 
begin
w_chk_full:         if (wptr + 1) % N = rptr then 
w_early_ret:            return; 
                    end if;
w_write_buf:        assert buffer[wptr] = 0;
w_cs:               buffer[wptr] := wptr + 1000;
w_upd_wptr:         wptr := (wptr + 1) % N;
                    return;
end procedure; 

fair process WriterP = WRITER
begin 
    w_while:
    while TRUE do
        call writer();
    end while;
end process; 

fair process ReaderP = READER
begin 
    r_start: 
    while TRUE do
        call reader();
    end while;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "681cb983" /\ chksum(tla) = "cda1a5ca")
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


READER == 0
WRITER == 1


vars == << rptr, wptr, buffer, pc, stack >>

ProcSet == {WRITER} \cup {READER}

Init == (* Global variables *)
        /\ rptr = 0
        /\ wptr = 0
        /\ buffer = [i \in 0..N-1 |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = WRITER -> "w_while"
                                        [] self = READER -> "r_start"]

r_chk_empty(self) == /\ pc[self] = "r_chk_empty"
                     /\ IF rptr = wptr
                           THEN /\ pc' = [pc EXCEPT ![self] = "r_early_ret"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "r_read_buf"]
                     /\ UNCHANGED << rptr, wptr, buffer, stack >>

r_early_ret(self) == /\ pc[self] = "r_early_ret"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << rptr, wptr, buffer >>

r_read_buf(self) == /\ pc[self] = "r_read_buf"
                    /\ Assert(buffer[rptr] # 0, 
                              "Failure of assertion at line 61, column 21.")
                    /\ pc' = [pc EXCEPT ![self] = "r_cs"]
                    /\ UNCHANGED << rptr, wptr, buffer, stack >>

r_cs(self) == /\ pc[self] = "r_cs"
              /\ buffer' = [buffer EXCEPT ![rptr] = 0]
              /\ pc' = [pc EXCEPT ![self] = "r_upd_rtpr"]
              /\ UNCHANGED << rptr, wptr, stack >>

r_upd_rtpr(self) == /\ pc[self] = "r_upd_rtpr"
                    /\ rptr' = (rptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << wptr, buffer >>

reader(self) == r_chk_empty(self) \/ r_early_ret(self) \/ r_read_buf(self)
                   \/ r_cs(self) \/ r_upd_rtpr(self)

w_chk_full(self) == /\ pc[self] = "w_chk_full"
                    /\ IF (wptr + 1) % N = rptr
                          THEN /\ pc' = [pc EXCEPT ![self] = "w_early_ret"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "w_write_buf"]
                    /\ UNCHANGED << rptr, wptr, buffer, stack >>

w_early_ret(self) == /\ pc[self] = "w_early_ret"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << rptr, wptr, buffer >>

w_write_buf(self) == /\ pc[self] = "w_write_buf"
                     /\ Assert(buffer[wptr] = 0, 
                               "Failure of assertion at line 72, column 21.")
                     /\ pc' = [pc EXCEPT ![self] = "w_cs"]
                     /\ UNCHANGED << rptr, wptr, buffer, stack >>

w_cs(self) == /\ pc[self] = "w_cs"
              /\ buffer' = [buffer EXCEPT ![wptr] = wptr + 1000]
              /\ pc' = [pc EXCEPT ![self] = "w_upd_wptr"]
              /\ UNCHANGED << rptr, wptr, stack >>

w_upd_wptr(self) == /\ pc[self] = "w_upd_wptr"
                    /\ wptr' = (wptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << rptr, buffer >>

writer(self) == w_chk_full(self) \/ w_early_ret(self) \/ w_write_buf(self)
                   \/ w_cs(self) \/ w_upd_wptr(self)

w_while == /\ pc[WRITER] = "w_while"
           /\ stack' = [stack EXCEPT ![WRITER] = << [ procedure |->  "writer",
                                                      pc        |->  "w_while" ] >>
                                                  \o stack[WRITER]]
           /\ pc' = [pc EXCEPT ![WRITER] = "w_chk_full"]
           /\ UNCHANGED << rptr, wptr, buffer >>

WriterP == w_while

r_start == /\ pc[READER] = "r_start"
           /\ stack' = [stack EXCEPT ![READER] = << [ procedure |->  "reader",
                                                      pc        |->  "r_start" ] >>
                                                  \o stack[READER]]
           /\ pc' = [pc EXCEPT ![READER] = "r_chk_empty"]
           /\ UNCHANGED << rptr, wptr, buffer >>

ReaderP == r_start

Next == WriterP \/ ReaderP
           \/ (\E self \in ProcSet: reader(self) \/ writer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(WriterP) /\ WF_vars(writer(WRITER))
        /\ WF_vars(ReaderP) /\ WF_vars(reader(READER))

\* END TRANSLATION 

\* reader and writer cannot operator on the same index
MUTEX ==
    ~ ((pc[WRITER] = "w_cs") /\ (pc[READER] = "r_cs") /\ rptr = wptr)

Inv_Basics == 
    /\ ((written \cup writing) \cup unused) = all
    /\ reading \subseteq written                            \* reading is a subset of written
    /\ \A i \in unused : buffer[i] = 0
    /\ \/ Cardinality(to_be_read) + 1 = Cardinality(reading) 
       \/ Cardinality(to_be_read)     = Cardinality(reading) + 1
       \/ Cardinality(to_be_read)     = Cardinality(reading)
    /\ MUTEX

===============================================================================
