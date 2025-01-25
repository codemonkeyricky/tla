--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers, FiniteSets, TLC, Sequences
CONSTANTS Servers
VARIABLES state, messages, voted_for, vote_granted, term, vote_requested, establish_leadership
vars == <<state, messages, voted_for, term, vote_granted, vote_requested, establish_leadership>>

\* Follower == 0 
\* Candidate == 1
\* Leader == 2


Perms == Permutations(Servers)

MaxOutstanding == 1
MaxDiff == 1
MaxTerm == 2

Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ messages = {} 
    /\ voted_for = [s \in Servers |-> ""]
    /\ vote_granted = [s \in Servers |-> {}]
    /\ vote_requested = [s \in Servers |-> 0]
    /\ term = [s \in Servers |-> 0]
    /\ establish_leadership = [s \in Servers |-> 0]

AddMessage(to_add, msgs) == 
    LET 
        pruned == {msg \in msgs : 
                    ~(msg.fDst = to_add.fDst /\ msg.fTerm < to_add.fTerm) }
    IN
        pruned \cup {to_add}

RemoveMessage(to_remove, msgs) ==
    msgs \ {to_remove}

KeepAlive(i, j) == 
    /\ messages' = AddMessage([ fSrc |-> i,
                                fDst |-> j,
                                fType |-> "AppendEntryReq",
                                fTerm |-> term[i]], 
                    messages)

\* TLC Constrain
LimitDivergence(i) == 
    LET 
        values == {term[s] : s \in Servers}
        max_v == CHOOSE x \in values : \A y \in values : x >= y
        min_v == CHOOSE x \in values : \A y \in values : x <= y
    IN 
        \/ /\ term[i] # max_v
        \/ /\ term[i] = max_v 
           /\ term[i] - min_v < MaxDiff

Timeout(i) == 
    /\ LimitDivergence(i)
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ voted_for' = [voted_for EXCEPT ![i] = i]             \* voted for myself
    /\ vote_granted' = [vote_granted EXCEPT ![i] = {i}]
    /\ vote_requested' = [vote_requested EXCEPT ![i] = 0]
    /\ term' = [term EXCEPT ![i] = @ + 1]                   \* bump term
    /\ establish_leadership' = [establish_leadership EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages>>
    \* /\ PrintT(state')

RequestVoteSet(i) == {
    [fSrc |-> i, fDst |-> s, fType |-> "RequestVoteReq", fTerm |-> term[i]] 
        : s \in Servers \ {i}
}

Campaign(i) == 
    /\ vote_requested[i] = 0
    /\ vote_requested' = [vote_requested EXCEPT ![i] = 1]
    /\ messages' = messages \cup RequestVoteSet(i) 
    /\ UNCHANGED <<state, term, vote_granted, voted_for, establish_leadership>>

RequestVoteReq(msg) == 
    LET 
        i == msg.fDst
        j == msg.fSrc
        type == msg.fType
        t == msg.fTerm
    IN 
        \* haven't voted, or whom we voted re-requested
        \/ /\ t = term[i]
           /\ \/ voted_for[i] = j 
              \/ voted_for[i] = ""
           /\ voted_for' = [voted_for EXCEPT ![i] = j]
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 1],
                                        RemoveMessage(msg, messages))
           /\ UNCHANGED <<state, term, vote_granted, vote_requested, establish_leadership >>
        \* already voted someone else
        \/ /\ t = term[i]
           /\ voted_for[i] # j 
           /\ voted_for[i] # ""
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 0],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_requested, establish_leadership>>
        \/  /\ t < term[i]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> term[i], 
                                        fSuccess |-> 0],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_requested, establish_leadership>>
        \* revert back to follower
        \/  /\ t > term[i]
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ term' = [term EXCEPT ![i] = t]
            /\ voted_for' = [voted_for EXCEPT ![i] = j]
            /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
            /\ vote_requested' = [vote_requested EXCEPT ![i] = 0]
            /\ establish_leadership' = [establish_leadership EXCEPT ![i] = 0]
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
           /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
           /\ vote_requested' = [vote_requested EXCEPT ![i] = 0]
           /\ establish_leadership' = [term EXCEPT ![i] = 0]
           /\ term' = [term EXCEPT ![i] = t]
        \* discard 
        \/ /\ t <= term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_requested, establish_leadership>>

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
           /\ messages' = RemoveMessage(msg, messages)
           /\ vote_granted' = [vote_granted EXCEPT ![i] = @ \cup {j}]
           /\ UNCHANGED <<state, voted_for, term, vote_requested, establish_leadership>> 
        \* same term unsuccess 
        \/ /\ t = term[i]
           /\ s = 0
           /\ messages' = RemoveMessage(msg, messages)
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_requested, establish_leadership>> 
        \* response has smaller term - ignore
        \/ /\ t < term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_requested, establish_leadership>>
        \* response has higher term - become follower
        \/ /\ t > term[i]
           /\ messages' = RemoveMessage(msg, messages)
           /\ state' = [state EXCEPT ![i] = "Follower"]
           /\ voted_for' = [voted_for EXCEPT ![i] = ""]
           /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
           /\ vote_requested' = [vote_requested EXCEPT ![i] = 0]
           /\ establish_leadership' = [establish_leadership EXCEPT ![i] = 0]
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
           /\ vote_granted' = [vote_granted EXCEPT ![i] = {}]
           /\ vote_requested' = [vote_requested EXCEPT ![i] = 0]
           /\ establish_leadership' = [establish_leadership EXCEPT ![i] = 0]
           /\ voted_for' = [voted_for EXCEPT ![i] = j]
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> t, 
                                        fSuccess |-> 1],
                                        RemoveMessage(msg, messages))
           /\ term' = [term EXCEPT ![i] = t]    \* update term 
        \/ /\ t < term[i]
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> term[i], 
                                        fSuccess |-> 0],
                                        RemoveMessage(msg, messages))
           /\ UNCHANGED <<state, voted_for, vote_granted, term, vote_requested, establish_leadership>> 

Receive(msg) == 
    \/ /\ msg.fType = "AppendEntryReq"
       /\ AppendEntryReq(msg) 
    \/ /\ msg.fType = "AppendEntryResp"
       /\ AppendEntryResp(msg) 
    \/ /\ msg.fType = "RequestVoteReq"
       /\ RequestVoteReq(msg) 
    \/ /\ msg.fType = "RequestVoteResp"
       /\ RequestVoteResp(msg) 

KeepAliveSet(i) == {
    [fSrc |-> i, fDst |-> s, fType |-> "AppendEntryReq", fTerm |-> term[i]] 
        : s \in Servers \ {i}
}

Leader(i) == 
    /\ state[i] = "Leader"
    /\ establish_leadership[i] = 0
    /\ establish_leadership' = [establish_leadership EXCEPT ![i] = 1]
    /\ messages' = messages \cup KeepAliveSet(i) 
    /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_requested>>

BecomeLeader(i) ==
    /\ Cardinality(vote_granted[i]) > Cardinality(Servers) \div 2
    /\ state' = [state EXCEPT ![i] = "Leader"]
    /\ UNCHANGED <<messages, voted_for, term, vote_granted, vote_requested, establish_leadership>>

Candidate(i) == 
    /\ state[i] = "Candidate"
    /\ \/ Campaign(i)
       \/ BecomeLeader(i)
       \/ Timeout(i)

Follower(i) == 
    /\ state[i] = "Follower"
    /\ Timeout(i)

Normalize == 
    LET 
        values == {term[s] : s \in Servers}
        max_v == CHOOSE x \in values : \A y \in values : x >= y
        min_v == CHOOSE x \in values : \A y \in values : x <= y
    IN 
        /\ max_v = MaxTerm
        /\ term' = [s \in Servers |-> term[s] - min_v]
        /\ messages' = {}
        /\ UNCHANGED <<state, voted_for, vote_granted, vote_requested, establish_leadership>>

Next == 
    \/ /\ \A i \in Servers : term[i] # MaxTerm 
       /\ \/ \E i \in Servers : 
                \/ Leader(i) 
                \/ Candidate(i)
                \/ Follower(i)
          \/ \E msg \in messages : Receive(msg)
    \/ /\ \E i \in Servers: term[i] = MaxTerm 
       /\ Normalize

\* 
\* Multiple leaders are permitted but only if they are on different terms 
\* this can happen due to unfavourable network condition
\*
LeaderUniqueTerm ==
    \A s1, s2 \in Servers :
        (state[s1] = "Leader" /\ state[s2] = "Leader" /\ s1 /= s2) => (term[s1] # term[s2])

Converge ==
    \A s \in Servers:
        term[s] = 0 ~> term[s] = MaxTerm - MaxDiff

\* Liveness description to ensure no server is stuttering
Liveness == 
    /\ \A i \in Servers : 
        /\ WF_vars(Leader(i))
        /\ WF_vars(Candidate(i))
        /\ WF_vars(Follower(i))
    /\ WF_vars(\E msg \in messages : Receive(msg))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Liveness
=============================================================================