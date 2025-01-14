----------------------------- MODULE spmc -----------------------------

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT M, N, Reader, Writer  \* Fixed size of the array

(*--algorithm spmc 

variables 
    reader_k = 0,
    rrsvd = [kk \in 0..N-1 |-> 0],
    \* rptr_rsvd = [kk \in 0..Reader-1 |-> 100 + kk],
    rptr = [kk \in 0..Reader-1 |-> 0],
    wptr = 0,
    outstanding = 0,
    \* rstate = [kk \in 0..Reader-1 |-> "read_init"],
    buffer = [kk \in 0..N-1 |-> 0],
    \* wstate = "write_init";

define
\* written == 
\*     IF rptr <= wptr THEN 
\*         {k \in rptr..wptr - 1: TRUE}
\*     ELSE 
\*         {k \in rptr..N-1: TRUE} \cup 
\*         {k \in 0..wptr-1: TRUE} 

\* writing == 
\*     {wptr}

reading == 
    {k \in 0..N-1: rrsvd[k] = 2}

\* reading == 
\*      IF rptr <= rptr_next THEN 
\*         {k \in rptr..rptr_next - 1: TRUE}
\*     ELSE 
\*         {k \in rptr..N-1: TRUE} \cup 
\*         {k \in 0..rptr_next-1: TRUE} 

\* to_read == 
\*     IF rptr_next <= wptr THEN 
\*         {k \in rptr_next..wptr - 1: TRUE}
\*     ELSE 
\*         {k \in rptr_next..N-1: TRUE} \cup 
\*         {k \in 0..wptr-1: TRUE} 

\* all ==
\*     {k \in 0..N-1: TRUE}

\* read_reserved ==  
\*     {k \in 0..N-1: rrsvd[k] = 1}

\* unused ==
\*     all \ (written \cup writing)

\* reader_reading == 
\*     {k \in written : rrsvd[k] = 1}

\* reader_read == 
\*     {k \in written : rrsvd[k] = 0} 

\* \* all index eventually become reserved
\* Liveness == 
\*     \A k \in 0..N-1:
\*     <>(buffer[k] # 0)

\* \* we can get weird interleaving patterns with spmc, a later reserved index done
\* \* before an earlier reserved index. Confirms the earlier reserved index eventually 
\* \* clear. 
\* Liveness2 == 
\*     /\ (rrsvd[0] = 1 /\ rrsvd[1] = 0 /\ rrsvd[2] = 1) ~> (rrsvd[0] = 0)
\*     \* /\ (rrsvd[0] = 1 /\ rrsvd[1] = 0 /\ rrsvd[2] = 1) ~> (rrsvd[2] = 0)

end define;

\* unused, ready_to_read, ready_to_write

procedure reader() 
variable 
    i = self;
begin
r_chk_empty:        if outstanding # 0 then 
                        outstanding := outstanding - 1; 
                    else 
                        return;
                    end if;
                    \* reserved a read - now find it
r_try_lock:         if rrsvd[rptr[i]] = 1 then 
                        rrsvd[rptr[i]] := 2;
                    else 
                        rptr[i] := (rptr[i] + 1) % N;
                        goto r_try_lock;
                    end if;
r_data_chk:         assert buffer[rptr[i]] = rptr[i] + 1000;
r_read_buf:         buffer[rptr[i]] := 0;
                    rrsvd[rptr[i]] := 0;
r_done:                    return;
end procedure; 

\* rrsvd = 0 is unused, 1 written, 2 reserved for read

procedure writer(i) begin
w_is_full:          if outstanding = N - 1 then 
w_early_return:         return; 
                    end if;
w_chk_st:           if rrsvd[wptr] # 0 then 
                        return;
                    end if;
w_write_buf:        buffer[wptr] := wptr + 1000;
w_mark_written:     rrsvd[wptr] := 1;
w_inc:              outstanding := outstanding + 1;
w_inc_wptr:         wptr := (wptr + 1) % N;
w_done:             return;
end procedure; 

fair process writer_0 = 100
begin 
    w_while:
    while TRUE do
        call writer(0);
    end while;
end process; 

fair process reader_k \in 0..Reader-1 
begin 
    r_start: 
    while TRUE do
        call reader();
    end while;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "91186815" /\ chksum(tla) = "9c9890dc")
\* Process reader_k at line 125 col 6 changed to reader_k_
\* Procedure variable i of procedure reader at line 81 col 5 changed to i_
CONSTANT defaultInitValue
VARIABLES reader_k, rrsvd, rptr, wptr, outstanding, buffer, pc, stack

(* define statement *)
reading ==
    {k \in 0..N-1: rrsvd[k] = 2}

VARIABLES i_, i

vars == << reader_k, rrsvd, rptr, wptr, outstanding, buffer, pc, stack, i_, i
        >>

ProcSet == {100} \cup (0..Reader-1)

Init == (* Global variables *)
        /\ reader_k = 0
        /\ rrsvd = [kk \in 0..N-1 |-> 0]
        /\ rptr = [kk \in 0..Reader-1 |-> 0]
        /\ wptr = 0
        /\ outstanding = 0
        /\ buffer = [kk \in 0..N-1 |-> 0]
        (* Procedure reader *)
        /\ i_ = [ self \in ProcSet |-> self]
        (* Procedure writer *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 100 -> "w_while"
                                        [] self \in 0..Reader-1 -> "r_start"]

r_chk_empty(self) == /\ pc[self] = "r_chk_empty"
                     /\ IF outstanding # 0
                           THEN /\ outstanding' = outstanding - 1
                                /\ pc' = [pc EXCEPT ![self] = "r_try_lock"]
                                /\ UNCHANGED << stack, i_ >>
                           ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED outstanding
                     /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, buffer, i >>

r_try_lock(self) == /\ pc[self] = "r_try_lock"
                    /\ IF rrsvd[rptr[i_[self]]] = 1
                          THEN /\ rrsvd' = [rrsvd EXCEPT ![rptr[i_[self]]] = 2]
                               /\ pc' = [pc EXCEPT ![self] = "r_data_chk"]
                               /\ rptr' = rptr
                          ELSE /\ rptr' = [rptr EXCEPT ![i_[self]] = (rptr[i_[self]] + 1) % N]
                               /\ pc' = [pc EXCEPT ![self] = "r_try_lock"]
                               /\ rrsvd' = rrsvd
                    /\ UNCHANGED << reader_k, wptr, outstanding, buffer, stack, 
                                    i_, i >>

r_data_chk(self) == /\ pc[self] = "r_data_chk"
                    /\ Assert(buffer[rptr[i_[self]]] = rptr[i_[self]] + 1000, 
                              "Failure of assertion at line 95, column 21.")
                    /\ pc' = [pc EXCEPT ![self] = "r_read_buf"]
                    /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                    buffer, stack, i_, i >>

r_read_buf(self) == /\ pc[self] = "r_read_buf"
                    /\ buffer' = [buffer EXCEPT ![rptr[i_[self]]] = 0]
                    /\ rrsvd' = [rrsvd EXCEPT ![rptr[i_[self]]] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "r_done"]
                    /\ UNCHANGED << reader_k, rptr, wptr, outstanding, stack, 
                                    i_, i >>

r_done(self) == /\ pc[self] = "r_done"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                buffer, i >>

reader(self) == r_chk_empty(self) \/ r_try_lock(self) \/ r_data_chk(self)
                   \/ r_read_buf(self) \/ r_done(self)

w_is_full(self) == /\ pc[self] = "w_is_full"
                   /\ IF outstanding = N - 1
                         THEN /\ pc' = [pc EXCEPT ![self] = "w_early_return"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "w_chk_st"]
                   /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                   buffer, stack, i_, i >>

w_early_return(self) == /\ pc[self] = "w_early_return"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, 
                                        outstanding, buffer, i_ >>

w_chk_st(self) == /\ pc[self] = "w_chk_st"
                  /\ IF rrsvd[wptr] # 0
                        THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "w_write_buf"]
                             /\ UNCHANGED << stack, i >>
                  /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                  buffer, i_ >>

w_write_buf(self) == /\ pc[self] = "w_write_buf"
                     /\ buffer' = [buffer EXCEPT ![wptr] = wptr + 1000]
                     /\ pc' = [pc EXCEPT ![self] = "w_mark_written"]
                     /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                     stack, i_, i >>

w_mark_written(self) == /\ pc[self] = "w_mark_written"
                        /\ rrsvd' = [rrsvd EXCEPT ![wptr] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "w_inc"]
                        /\ UNCHANGED << reader_k, rptr, wptr, outstanding, 
                                        buffer, stack, i_, i >>

w_inc(self) == /\ pc[self] = "w_inc"
               /\ outstanding' = outstanding + 1
               /\ pc' = [pc EXCEPT ![self] = "w_inc_wptr"]
               /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, buffer, stack, i_, 
                               i >>

w_inc_wptr(self) == /\ pc[self] = "w_inc_wptr"
                    /\ wptr' = (wptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = "w_done"]
                    /\ UNCHANGED << reader_k, rrsvd, rptr, outstanding, buffer, 
                                    stack, i_, i >>

w_done(self) == /\ pc[self] = "w_done"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                buffer, i_ >>

writer(self) == w_is_full(self) \/ w_early_return(self) \/ w_chk_st(self)
                   \/ w_write_buf(self) \/ w_mark_written(self)
                   \/ w_inc(self) \/ w_inc_wptr(self) \/ w_done(self)

w_while == /\ pc[100] = "w_while"
           /\ /\ i' = [i EXCEPT ![100] = 0]
              /\ stack' = [stack EXCEPT ![100] = << [ procedure |->  "writer",
                                                      pc        |->  "w_while",
                                                      i         |->  i[100] ] >>
                                                  \o stack[100]]
           /\ pc' = [pc EXCEPT ![100] = "w_is_full"]
           /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, buffer, 
                           i_ >>

writer_0 == w_while

r_start(self) == /\ pc[self] = "r_start"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "reader",
                                                          pc        |->  "r_start",
                                                          i_        |->  i_[self] ] >>
                                                      \o stack[self]]
                 /\ i_' = [i_ EXCEPT ![self] = self]
                 /\ pc' = [pc EXCEPT ![self] = "r_chk_empty"]
                 /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, outstanding, 
                                 buffer, i >>

reader_k_(self) == r_start(self)

Next == writer_0
           \/ (\E self \in ProcSet: reader(self) \/ writer(self))
           \/ (\E self \in 0..Reader-1: reader_k_(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(writer_0) /\ WF_vars(writer(100))
        /\ \A self \in 0..Reader-1 : WF_vars(reader_k_(self)) /\ WF_vars(reader(self))

\* END TRANSLATION 

Inv_Basics == 
    /\ Cardinality(reading) <= Reader
\*     /\ ((written \cup writing) \cup unused) = all
\*     /\ reading \subseteq written                            \* reading is a subset of written
\*     /\ to_read \subseteq written                            \* to_read is a subset of written
\*     /\ read_reserved \intersect unused = {}
\*     /\ (reading \cup to_read) = written
\*     /\ \A kk \in unused : buffer[kk] = 0
\*     /\ (reading \cup to_read) = written
\*     /\ \A kk \in unused : buffer[kk] = 0
\*     /\ \A kk \in to_read : buffer[kk] # 0                     \* to_read must be populated
\*     /\ \A kk \in read_reserved : buffer[kk] # 0
\*     /\ \A kk \in reading : rrsvd[kk] = 0 => buffer[kk] = 0     \* part of reading but not reserved - read done.
\*     /\ \A kk \in reading : rrsvd[kk] # 0 => buffer[kk] # 0     \* part of reading but reserved - read in progress.
\*     /\ Cardinality(read_reserved) <= Reader                 \* at most 'Reader' indices can be reserved

===============================================================================
