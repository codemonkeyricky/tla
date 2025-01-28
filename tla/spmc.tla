----------------------------- MODULE spmc -----------------------------

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT N, READERS \* Fixed size of the array

(*--algorithm spmc 

variables 
    status = [k \in 0..N-1 |-> "unused"],
    rptr = [k \in READERS |-> 0],
    wptr = 0,
    outstanding = 0,
    buffer = [kk \in 0..N-1 |-> 0],

define

UNUSED == "unused" 
WRITTEN == "written"
READING == "reading"

reading == 
    {k \in 0..N-1: status[k] = READING}

written == 
    {k \in 0..N-1: status[k] = WRITTEN}

buffer_filled == 
    {k \in 0..N-1: buffer[k] # 0}

\* all index eventually become reserved
Liveness == 
    \A k \in 0..N-1:
        buffer[k] = 0 ~> buffer[k] # 0

\* we can get weird interleaving patterns with spmc, a later reserved index done
\* before an earlier reserved index. Confirms the earlier reserved index eventually 
\* clear. 
Liveness2 == 
    /\ (status[0] = WRITTEN /\ status[1] = UNUSED /\ status[2] = WRITTEN) ~> (status[0] = UNUSED)
    /\ (status[0] = WRITTEN /\ status[1] = UNUSED /\ status[2] = WRITTEN) ~> (status[2] = UNUSED)

WRITER == "w0"

Perms == Permutations(READERS) 


end define;

\* unused, ready_to_read, ready_to_write

procedure reader() 
variable 
    i = self;
begin
r_chk_empty:        
    if outstanding # 0 then 
        outstanding := outstanding - 1; 
    else 
    r_early_ret:            
        return;
    end if;
\* reserved a read - now find it
r_try_lock:         
    if status[rptr[i]] = WRITTEN then 
        status[rptr[i]] := READING;
    else 
    r_retry:                
        rptr[i] := (rptr[i] + 1) % N;
            goto r_try_lock;
    end if;
r_data_chk:         
    assert buffer[rptr[i]] = rptr[i] + 1000;
r_read_buf:         
    buffer[rptr[i]] := 0;
r_unlock:           
    status[rptr[i]] := UNUSED;
r_done:             
    return;
end procedure; 

\* status = 0 is unused, 1 written, 2 reserved for read

procedure writer() begin
w_chk_full:         
    if outstanding = N - 1 then 
    w_early_ret:            
        return; 
    end if;
w_chk_st:           
    if status[wptr] # UNUSED then 
    w_early_ret2:           
        return;
    end if;
w_write_buf:        
    buffer[wptr] := wptr + 1000;
w_mark_written:     
    status[wptr] := WRITTEN;
w_inc_wptr:         
    wptr := (wptr + 1) % N;
w_inc:              
    outstanding := outstanding + 1;
w_done:             
    return;
end procedure; 

fair process w = WRITER
begin 
    w_while:
    while TRUE do
        call writer();
    end while;
end process; 

fair process r \in READERS
begin 
    r_start: 
    while TRUE do
        call reader();
    end while;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c2209f36" /\ chksum(tla) = "18466047")
VARIABLES status, rptr, wptr, outstanding, buffer, pc, stack

(* define statement *)
UNUSED == "unused"
WRITTEN == "written"
READING == "reading"

reading ==
    {k \in 0..N-1: status[k] = READING}

written ==
    {k \in 0..N-1: status[k] = WRITTEN}

buffer_filled ==
    {k \in 0..N-1: buffer[k] # 0}


Liveness ==
    \A k \in 0..N-1:
        buffer[k] = 0 ~> buffer[k] # 0




Liveness2 ==
    /\ (status[0] = WRITTEN /\ status[1] = UNUSED /\ status[2] = WRITTEN) ~> (status[0] = UNUSED)
    /\ (status[0] = WRITTEN /\ status[1] = UNUSED /\ status[2] = WRITTEN) ~> (status[2] = UNUSED)

WRITER == "w0"

Perms == Permutations(READERS)

VARIABLE i

vars == << status, rptr, wptr, outstanding, buffer, pc, stack, i >>

ProcSet == {WRITER} \cup (READERS)

Init == (* Global variables *)
        /\ status = [k \in 0..N-1 |-> "unused"]
        /\ rptr = [k \in READERS |-> 0]
        /\ wptr = 0
        /\ outstanding = 0
        /\ buffer = [kk \in 0..N-1 |-> 0]
        (* Procedure reader *)
        /\ i = [ self \in ProcSet |-> self]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = WRITER -> "w_while"
                                        [] self \in READERS -> "r_start"]

r_chk_empty(self) == /\ pc[self] = "r_chk_empty"
                     /\ IF outstanding # 0
                           THEN /\ outstanding' = outstanding - 1
                                /\ pc' = [pc EXCEPT ![self] = "r_try_lock"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "r_early_ret"]
                                /\ UNCHANGED outstanding
                     /\ UNCHANGED << status, rptr, wptr, buffer, stack, i >>

r_early_ret(self) == /\ pc[self] = "r_early_ret"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << status, rptr, wptr, outstanding, buffer >>

r_try_lock(self) == /\ pc[self] = "r_try_lock"
                    /\ IF status[rptr[i[self]]] = WRITTEN
                          THEN /\ status' = [status EXCEPT ![rptr[i[self]]] = READING]
                               /\ pc' = [pc EXCEPT ![self] = "r_data_chk"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "r_retry"]
                               /\ UNCHANGED status
                    /\ UNCHANGED << rptr, wptr, outstanding, buffer, stack, i >>

r_retry(self) == /\ pc[self] = "r_retry"
                 /\ rptr' = [rptr EXCEPT ![i[self]] = (rptr[i[self]] + 1) % N]
                 /\ pc' = [pc EXCEPT ![self] = "r_try_lock"]
                 /\ UNCHANGED << status, wptr, outstanding, buffer, stack, i >>

r_data_chk(self) == /\ pc[self] = "r_data_chk"
                    /\ Assert(buffer[rptr[i[self]]] = rptr[i[self]] + 1000, 
                              "Failure of assertion at line 73, column 5.")
                    /\ pc' = [pc EXCEPT ![self] = "r_read_buf"]
                    /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, 
                                    stack, i >>

r_read_buf(self) == /\ pc[self] = "r_read_buf"
                    /\ buffer' = [buffer EXCEPT ![rptr[i[self]]] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "r_unlock"]
                    /\ UNCHANGED << status, rptr, wptr, outstanding, stack, i >>

r_unlock(self) == /\ pc[self] = "r_unlock"
                  /\ status' = [status EXCEPT ![rptr[i[self]]] = UNUSED]
                  /\ pc' = [pc EXCEPT ![self] = "r_done"]
                  /\ UNCHANGED << rptr, wptr, outstanding, buffer, stack, i >>

r_done(self) == /\ pc[self] = "r_done"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << status, rptr, wptr, outstanding, buffer >>

reader(self) == r_chk_empty(self) \/ r_early_ret(self) \/ r_try_lock(self)
                   \/ r_retry(self) \/ r_data_chk(self) \/ r_read_buf(self)
                   \/ r_unlock(self) \/ r_done(self)

w_chk_full(self) == /\ pc[self] = "w_chk_full"
                    /\ IF outstanding = N - 1
                          THEN /\ pc' = [pc EXCEPT ![self] = "w_early_ret"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "w_chk_st"]
                    /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, 
                                    stack, i >>

w_early_ret(self) == /\ pc[self] = "w_early_ret"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, 
                                     i >>

w_chk_st(self) == /\ pc[self] = "w_chk_st"
                  /\ IF status[wptr] # UNUSED
                        THEN /\ pc' = [pc EXCEPT ![self] = "w_early_ret2"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "w_write_buf"]
                  /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, 
                                  stack, i >>

w_early_ret2(self) == /\ pc[self] = "w_early_ret2"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, 
                                      i >>

w_write_buf(self) == /\ pc[self] = "w_write_buf"
                     /\ buffer' = [buffer EXCEPT ![wptr] = wptr + 1000]
                     /\ pc' = [pc EXCEPT ![self] = "w_mark_written"]
                     /\ UNCHANGED << status, rptr, wptr, outstanding, stack, i >>

w_mark_written(self) == /\ pc[self] = "w_mark_written"
                        /\ status' = [status EXCEPT ![wptr] = WRITTEN]
                        /\ pc' = [pc EXCEPT ![self] = "w_inc_wptr"]
                        /\ UNCHANGED << rptr, wptr, outstanding, buffer, stack, 
                                        i >>

w_inc_wptr(self) == /\ pc[self] = "w_inc_wptr"
                    /\ wptr' = (wptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = "w_inc"]
                    /\ UNCHANGED << status, rptr, outstanding, buffer, stack, 
                                    i >>

w_inc(self) == /\ pc[self] = "w_inc"
               /\ outstanding' = outstanding + 1
               /\ pc' = [pc EXCEPT ![self] = "w_done"]
               /\ UNCHANGED << status, rptr, wptr, buffer, stack, i >>

w_done(self) == /\ pc[self] = "w_done"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, i >>

writer(self) == w_chk_full(self) \/ w_early_ret(self) \/ w_chk_st(self)
                   \/ w_early_ret2(self) \/ w_write_buf(self)
                   \/ w_mark_written(self) \/ w_inc_wptr(self)
                   \/ w_inc(self) \/ w_done(self)

w_while == /\ pc[WRITER] = "w_while"
           /\ stack' = [stack EXCEPT ![WRITER] = << [ procedure |->  "writer",
                                                      pc        |->  "w_while" ] >>
                                                  \o stack[WRITER]]
           /\ pc' = [pc EXCEPT ![WRITER] = "w_chk_full"]
           /\ UNCHANGED << status, rptr, wptr, outstanding, buffer, i >>

w == w_while

r_start(self) == /\ pc[self] = "r_start"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "reader",
                                                          pc        |->  "r_start",
                                                          i         |->  i[self] ] >>
                                                      \o stack[self]]
                 /\ i' = [i EXCEPT ![self] = self]
                 /\ pc' = [pc EXCEPT ![self] = "r_chk_empty"]
                 /\ UNCHANGED << status, rptr, wptr, outstanding, buffer >>

r(self) == r_start(self)

Next == w
           \/ (\E self \in ProcSet: reader(self) \/ writer(self))
           \/ (\E self \in READERS: r(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(w) /\ WF_vars(writer(WRITER))
        /\ \A self \in READERS : WF_vars(r(self)) /\ WF_vars(reader(self))

\* END TRANSLATION 

Inv_Basics == 
    /\ Cardinality(reading) <= Cardinality(READERS)
    /\ Cardinality(buffer_filled) <= Cardinality(written) + Cardinality(reading) + 1
    \* /\ Cardinality(written) <= outstanding + Reader
    \* /\ (Cardinality(reading) + Cardinality(written)) <= outstanding + 1
    \* /\ ~(status[0] = 1 /\ status[1] = 0 /\ status[2] = 1)
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
\*     /\ \A kk \in reading : status[kk] = 0 => buffer[kk] = 0     \* part of reading but not reserved - read done.
\*     /\ \A kk \in reading : status[kk] # 0 => buffer[kk] # 0     \* part of reading but reserved - read in progress.
\*     /\ Cardinality(read_reserved) <= Reader                 \* at most 'Reader' indices can be reserved

===============================================================================
