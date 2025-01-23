--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers, FiniteSets, TLC, Sequences
VARIABLES state, messages, voted_for, vote_granted, vote_received, term
vars == <<state, messages, voted_for, term, vote_granted, vote_received>>

\* Follower == 0 
\* Candidate == 1
\* Leader == 2

Servers == {"s0", "s1", "s2"}

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ messages = [m \in {} |-> 0]
    /\ voted_for = [s \in Servers |-> ""]
    /\ vote_received = [s \in Servers |-> {}]
    /\ vote_granted = [s \in Servers |-> {}]
    /\ term = [s \in Servers |-> 0]

AddMessage(to_add, msgs) == 
    IF to_add \in DOMAIN msgs THEN 
        [msgs EXCEPT ![to_add] = @ + 1]
    ELSE 
        msgs @@ (to_add :> 1)

RemoveMessage(to_remove, msgs) ==
    IF to_remove \in DOMAIN msgs THEN                                                                                                                                                                 
        IF msgs[to_remove] <= 1 THEN [i \in DOMAIN msgs \ {to_remove} |-> msgs[i]]                                                                                                                            
        ELSE [msgs EXCEPT ![to_remove] = msgs[to_remove] - 1]                                                                                                                                                 
    ELSE                                                                                                                                                                                      
        msgs    

KeepAlive(i, j) == 
    /\ messages' = AddMessage([ fSrc |-> i,
                                fDst |-> j,
                                fType |-> "AppendEntryReq",
                                fTerm |-> term[i]], 
                    messages)
    /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>

Timeout(i) == 
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ voted_for' = [voted_for EXCEPT ![i] = i]             \* voted for myself
    /\ vote_received' = [vote_received EXCEPT ![i] = {i}]
    /\ vote_granted' = [vote_granted EXCEPT ![i] = {i}]
    /\ term' = [term EXCEPT ![i] = @ + 1]                   \* bump term
    /\ UNCHANGED <<messages>>
    \* /\ PrintT(state')

Campaign(i, j) == 
    /\ j \notin vote_received[i]
    /\ messages' = AddMessage([fSrc |-> i, 
                                fDst |-> j, 
                                fType |-> "RequestVoteReq", 
                                fTerm |-> term[i]], messages)
    /\ UNCHANGED <<state, term, vote_granted, vote_received, voted_for>>

RequestVoteReq(msg) == 
    LET 
        i == msg.fDst
        j == msg.fSrc
        type == msg.fType
        t == msg.fTerm
    IN 
        \* haven't voted, or whom we voted re-requested
        \/ /\ t = term[i]
           /\ voted_for[i] = j \/ voted_for[i] = ""
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 1],
                                        RemoveMessage(msg, messages))
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \* already voted someone else
        \/ /\ t = term[i]
           /\ voted_for[i] # j
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 0],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \/  /\ t < term[i]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> term[i], 
                                        fSuccess |-> 0],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \* revert back to follower
        \/  /\ t > term[i]
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ term' = [term EXCEPT ![i] = t]
            /\ voted_for' = [voted_for EXCEPT ![i] = ""]
            /\ vote_received' = [vote_received EXCEPT ![i] = {}]
            /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 1],
                                        RemoveMessage(msg, messages))

AppendEntryResp(msg) ==
    LET 
        i == msg.fDst
        j == msg.fSrc
        type == msg.fType
        t == msg.fTerm
        s == msg.fSuccess
    IN 
        \* become follower
        \/ /\ t > term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ state' = [state EXCEPT ![i] = "Follower"]
           /\ voted_for' = [voted_for EXCEPT ![i] = ""]
           /\ vote_received' = [vote_received EXCEPT ![i] = {}]
           /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
           /\ term' = [term EXCEPT ![i] = t]
        \* discard 
        \/ /\ t <= term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>

RequestVoteResp(msg) == 
    LET 
        i == msg.fDst
        j == msg.fSrc
        type == msg.fType
        t == msg.fTerm
        s == msg.fSuccess
    IN 
        \* same term success 
        \/ /\ t = term[i]
           /\ s = 1
           /\ vote_granted' = [vote_granted EXCEPT ![i] = @ \cup {j}]
           /\ vote_received' = [vote_received EXCEPT ![i] = @ \cup {j}]
           /\ UNCHANGED <<state, voted_for, term, messages>> 
        \* same term unsuccess 
        \/ /\ t = term[i]
           /\ s = 0
           /\ vote_received' = [vote_received EXCEPT ![i] = @ \cup {j}]
           /\ UNCHANGED <<state, voted_for, term, vote_granted, messages>> 
        \* response has smaller term - ignore
        \/ /\ t < term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \* response has higher term - become follower
        \/ /\ t > term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ state' = [state EXCEPT ![i] = "Follower"]
           /\ voted_for' = [voted_for EXCEPT ![i] = ""]
           /\ vote_received' = [vote_received EXCEPT ![i] = {}]
           /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
           /\ term' = [term EXCEPT ![i] = t]

AppendEntryReq(msg) == 
    LET 
        i == msg.fDst
        j == msg.fSrc
        t == msg.fTerm
        s == msg.fSuccess
    IN 
        \/ /\ t >= term[i]
           /\ state' = [state EXCEPT ![i] = "Follower"]
           /\ voted_for' = [voted_for EXCEPT ![i] = ""]
           /\ vote_received' = [vote_received EXCEPT ![i] = {i}]
           /\ vote_granted' = [vote_granted EXCEPT ![i] = {i}]
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 1],
                                        RemoveMessage(msg, messages))
           /\ term' = [term EXCEPT ![i] = t]    \* update term 
        \*    /\ UNCHANGED <<voted_for, vote_granted, vote_received>> 
        \/ /\ t < term[i]
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> term[i], 
                                        fSuccess |-> 0],
                                        RemoveMessage(msg, messages))
           /\ UNCHANGED <<state, voted_for, vote_granted, vote_received, term>> 

Receive(msg) == 
    \/ /\ msg.fType = "AppendEntryReq"
       /\ AppendEntryReq(msg) 
    \/ /\ msg.fType = "AppendEntryResp"
       /\ AppendEntryResp(msg) 
    \/ /\ msg.fType = "RequestVoteReq"
       /\ RequestVoteReq(msg) 
    \/ /\ msg.fType = "RequestVoteResp"
       /\ RequestVoteResp(msg) 

Leader(i) == 
    /\ state[i] = "Leader"
    /\ \E j \in Servers \ {i}: KeepAlive(i, j)

BecomeLeader(i) ==
    /\ Cardinality(vote_granted[i]) > Cardinality(Servers) \div 2
    /\ state' = [state EXCEPT ![i] = "Leader"]
    /\ UNCHANGED <<messages, voted_for, term, vote_granted, vote_received>>

Candidate(i) == 
    \/ /\ state[i] = "Candidate"
       /\ \E j \in Servers: Campaign(i, j)
    \/ /\ state[i] = "Candidate"
       /\ BecomeLeader(i)

MaxDiff == 2
MaxTerm == 1

Constrain(i) == 
    LET 
        values == {term[s] : s \in Servers}
        max_v == CHOOSE x \in values : \A y \in values : x >= y
        min_v == CHOOSE x \in values : \A y \in values : x <= y
    IN 
        \/ \/ term[i] # max_v
        \/ /\ term[i] = max_v 
           /\ term[i] - min_v < MaxDiff

Follower(i) == 
    /\ state[i] = "Follower"
    /\ Timeout(i)

    /\ term[i] < MaxTerm
    /\ Constrain(i)

Normalize == 
    LET 
        values == {term[s] : s \in Servers}
        max_v == CHOOSE x \in values : \A y \in values : x >= y
        min_v == CHOOSE x \in values : \A y \in values : x <= y
    IN 
        /\ max_v = MaxTerm
        /\ term' = [s \in Servers |-> term[s] - min_v]
        /\ UNCHANGED <<state, messages, voted_for, vote_granted, vote_received>>

Next == 
    \/ \E i \in Servers : Leader(i)
    \/ \E i \in Servers : Candidate(i)
    \/ \E i \in Servers : Follower(i)
    \/ \E msg \in DOMAIN messages : Receive(msg)
    \/ Normalize

\* 
\* Multiple leaders are permitted but only if they are on different terms 
\* this can happen due to unfavourable network condition
\*
LeaderUniqueTerm ==
    \A s1, s2 \in Servers :
        (state[s1] = "Leader" /\ state[s2] = "Leader" /\ s1 /= s2) => (term[s1] # term[s2])

Converge ==
    /\ term["s0"] = 0 ~> term["s0"] = 3

\* WF_vars(Next) ==
\*     WF_vars(\E i \in Servers : Leader(i)) \/
\*     WF_vars(\E i \in Servers : Candidate(i)) \/
\*     WF_vars(\E i \in Servers : Follower(i)) \/
\*     WF_vars(\E msg \in DOMAIN messages : Receive(msg))

\* Liveness description to ensure no server is stuttering
Liveness == 
    \A i \in Servers : 
        /\ WF_vars(Leader(i))
        /\ WF_vars(Candidate(i))
        /\ WF_vars(Follower(i))

Spec ==
  /\ Init
  /\ [][Next]_vars
\*   /\ WF_vars(Next)
  /\ Liveness
=============================================================================