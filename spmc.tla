----------------------------- MODULE spmc -----------------------------

EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANT M, N, Reader, Writer  \* Fixed size of the array

(*--algorithm spmc 

variables 
    reader_k = 0,
    rrsvd = [kk \in 0..N-1 |-> 0],
    \* rptr_rsvd = [kk \in 0..Reader-1 |-> 100 + kk],
    rptr = 0,
    wptr = 0,
    rptr_next = 0,
    \* rstate = [kk \in 0..Reader-1 |-> "read_init"],
    buffer = [kk \in 0..N-1 |-> 0],
    \* wstate = "write_init";

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
     IF rptr <= rptr_next THEN 
        {k \in rptr..rptr_next - 1: TRUE}
    ELSE 
        {k \in rptr..N-1: TRUE} \cup 
        {k \in 0..rptr_next-1: TRUE} 

to_read == 
    IF rptr_next <= wptr THEN 
        {k \in rptr_next..wptr - 1: TRUE}
    ELSE 
        {k \in rptr_next..N-1: TRUE} \cup 
        {k \in 0..wptr-1: TRUE} 

all ==
    {k \in 0..N-1: TRUE}

read_reserved ==  
    {k \in 0..N-1: rrsvd[k] = 1}

unused ==
    all \ (written \cup writing)

reader_reading == 
    {k \in written : rrsvd[k] = 1}

reader_read == 
    {k \in written : rrsvd[k] = 0} 

\* all index eventually become reserved
Liveness == 
    \A k \in 0..N-1:
    <>(buffer[k] # 0)

end define;

procedure reader(i) 
variable 
    k = 100;
begin
r_try_lock:         if rptr_next # wptr /\ rrsvd[rptr_next] = 0 then 
                        k := rptr_next;
                        rrsvd[k] := 1;
                    end if;
r_chk_early_exit:   if k = 100 then
                        return;
                    end if;
r_upd_rtpr_next:    rptr_next := (k + 1) % N;
r_read_buf:         buffer[k] := 0;
                    rrsvd[k] := 0;
r_recycle_check:    while rptr # rptr_next /\ rrsvd[rptr] = 0 do 
                        rptr := (rptr + 1) % N;
                    end while;
                    return;
end procedure; 

procedure writer(i) begin
w_is_full:          if (wptr + 1) % N = rptr then 
w_early_return:         return; 
                    end if;
w_write_buf:        buffer[wptr] := wptr + 1000;
w_inc_wptr:         wptr := (wptr + 1) % N;
                    return;
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
        call reader(reader_k);
    end while;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "915d7331" /\ chksum(tla) = "f15dc65c")
\* Process reader_k at line 104 col 6 changed to reader_k_
\* Parameter i of procedure reader at line 67 col 18 changed to i_
CONSTANT defaultInitValue
VARIABLES reader_k, rrsvd, rptr, wptr, rptr_next, buffer, pc, stack

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
     IF rptr <= rptr_next THEN
        {k \in rptr..rptr_next - 1: TRUE}
    ELSE
        {k \in rptr..N-1: TRUE} \cup
        {k \in 0..rptr_next-1: TRUE}

to_read ==
    IF rptr_next <= wptr THEN
        {k \in rptr_next..wptr - 1: TRUE}
    ELSE
        {k \in rptr_next..N-1: TRUE} \cup
        {k \in 0..wptr-1: TRUE}

all ==
    {k \in 0..N-1: TRUE}

read_reserved ==
    {k \in 0..N-1: rrsvd[k] = 1}

unused ==
    all \ (written \cup writing)

reader_reading ==
    {k \in written : rrsvd[k] = 1}

reader_read ==
    {k \in written : rrsvd[k] = 0}


Liveness ==
    \A k \in 0..N-1:
    <>(buffer[k] # 0)

VARIABLES i_, k, i

vars == << reader_k, rrsvd, rptr, wptr, rptr_next, buffer, pc, stack, i_, k, 
           i >>

ProcSet == {100} \cup (0..Reader-1)

Init == (* Global variables *)
        /\ reader_k = 0
        /\ rrsvd = [kk \in 0..N-1 |-> 0]
        /\ rptr = 0
        /\ wptr = 0
        /\ rptr_next = 0
        /\ buffer = [kk \in 0..N-1 |-> 0]
        (* Procedure reader *)
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ k = [ self \in ProcSet |-> 100]
        (* Procedure writer *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 100 -> "w_while"
                                        [] self \in 0..Reader-1 -> "r_start"]

r_try_lock(self) == /\ pc[self] = "r_try_lock"
                    /\ IF rptr_next # wptr /\ rrsvd[rptr_next] = 0
                          THEN /\ k' = [k EXCEPT ![self] = rptr_next]
                               /\ rrsvd' = [rrsvd EXCEPT ![k'[self]] = 1]
                          ELSE /\ TRUE
                               /\ UNCHANGED << rrsvd, k >>
                    /\ pc' = [pc EXCEPT ![self] = "r_chk_early_exit"]
                    /\ UNCHANGED << reader_k, rptr, wptr, rptr_next, buffer, 
                                    stack, i_, i >>

r_chk_early_exit(self) == /\ pc[self] = "r_chk_early_exit"
                          /\ IF k[self] = 100
                                THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
                                     /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "r_upd_rtpr_next"]
                                     /\ UNCHANGED << stack, i_, k >>
                          /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, 
                                          rptr_next, buffer, i >>

r_upd_rtpr_next(self) == /\ pc[self] = "r_upd_rtpr_next"
                         /\ rptr_next' = (k[self] + 1) % N
                         /\ pc' = [pc EXCEPT ![self] = "r_read_buf"]
                         /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, buffer, 
                                         stack, i_, k, i >>

r_read_buf(self) == /\ pc[self] = "r_read_buf"
                    /\ buffer' = [buffer EXCEPT ![k[self]] = 0]
                    /\ rrsvd' = [rrsvd EXCEPT ![k[self]] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "r_recycle_check"]
                    /\ UNCHANGED << reader_k, rptr, wptr, rptr_next, stack, i_, 
                                    k, i >>

r_recycle_check(self) == /\ pc[self] = "r_recycle_check"
                         /\ IF rptr # rptr_next /\ rrsvd[rptr] = 0
                               THEN /\ rptr' = (rptr + 1) % N
                                    /\ pc' = [pc EXCEPT ![self] = "r_recycle_check"]
                                    /\ UNCHANGED << stack, i_, k >>
                               ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
                                    /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                    /\ rptr' = rptr
                         /\ UNCHANGED << reader_k, rrsvd, wptr, rptr_next, 
                                         buffer, i >>

reader(self) == r_try_lock(self) \/ r_chk_early_exit(self)
                   \/ r_upd_rtpr_next(self) \/ r_read_buf(self)
                   \/ r_recycle_check(self)

w_is_full(self) == /\ pc[self] = "w_is_full"
                   /\ IF (wptr + 1) % N = rptr
                         THEN /\ pc' = [pc EXCEPT ![self] = "w_early_return"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "w_write_buf"]
                   /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, rptr_next, 
                                   buffer, stack, i_, k, i >>

w_early_return(self) == /\ pc[self] = "w_early_return"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, rptr_next, 
                                        buffer, i_, k >>

w_write_buf(self) == /\ pc[self] = "w_write_buf"
                     /\ buffer' = [buffer EXCEPT ![wptr] = wptr + 1000]
                     /\ pc' = [pc EXCEPT ![self] = "w_inc_wptr"]
                     /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, rptr_next, 
                                     stack, i_, k, i >>

w_inc_wptr(self) == /\ pc[self] = "w_inc_wptr"
                    /\ wptr' = (wptr + 1) % N
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << reader_k, rrsvd, rptr, rptr_next, buffer, 
                                    i_, k >>

writer(self) == w_is_full(self) \/ w_early_return(self)
                   \/ w_write_buf(self) \/ w_inc_wptr(self)

w_while == /\ pc[100] = "w_while"
           /\ /\ i' = [i EXCEPT ![100] = 0]
              /\ stack' = [stack EXCEPT ![100] = << [ procedure |->  "writer",
                                                      pc        |->  "w_while",
                                                      i         |->  i[100] ] >>
                                                  \o stack[100]]
           /\ pc' = [pc EXCEPT ![100] = "w_is_full"]
           /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, rptr_next, buffer, i_, 
                           k >>

writer_0 == w_while

r_start(self) == /\ pc[self] = "r_start"
                 /\ /\ i_' = [i_ EXCEPT ![self] = reader_k]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "reader",
                                                             pc        |->  "r_start",
                                                             k         |->  k[self],
                                                             i_        |->  i_[self] ] >>
                                                         \o stack[self]]
                 /\ k' = [k EXCEPT ![self] = 100]
                 /\ pc' = [pc EXCEPT ![self] = "r_try_lock"]
                 /\ UNCHANGED << reader_k, rrsvd, rptr, wptr, rptr_next, 
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
    /\ ((written \cup writing) \cup unused) = all
    /\ reading \subseteq written                            \* reading is a subset of written
    /\ to_read \subseteq written                            \* to_read is a subset of written
    /\ read_reserved \intersect unused = {}
    /\ (reading \cup to_read) = written
    /\ \A kk \in unused : buffer[kk] = 0
    /\ (reading \cup to_read) = written
    /\ \A kk \in unused : buffer[kk] = 0
    /\ \A kk \in to_read : buffer[kk] # 0                     \* to_read must be populated
    /\ \A kk \in read_reserved : buffer[kk] # 0
    /\ \A kk \in reading : rrsvd[kk] = 0 => buffer[kk] = 0     \* part of reading but not reserved - read done.
    /\ \A kk \in reading : rrsvd[kk] # 0 => buffer[kk] # 0     \* part of reading but reserved - read in progress.
    /\ Cardinality(read_reserved) <= Reader                 \* at most 'Reader' indices can be reserved

===============================================================================
