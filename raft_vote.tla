--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers, FiniteSets, TLC
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
    /\ messages' = AddMessage([fSrc |-> i,
           fDst |-> j,
           fType |-> "AppendEntryReq",
           fTerm |-> term[i]], messages)
    /\ UNCHANGED <<vars>>

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
    /\ voted_for' = [voted_for EXCEPT ![i] = i]
    /\ messages' = AddMessage([fSrc |-> i, 
                                fDst |-> j, 
                                fType |-> "RequestVoteReq", 
                                fTerm |-> term[i]], messages)
    /\ UNCHANGED <<state, term, vote_granted, vote_received>>

RequestVoteReqProc(msg) == 
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
                                        success |-> 1],
                                        RemoveMessage(msg, messages))
           /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \* already voted someone else
        \/ /\ t = term[i]
           /\ voted_for[i] # j
           /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        success |-> 0],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \/  /\ t < term[i]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> term[i], 
                                        success |-> 0],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<state, voted_for, term, vote_granted, vote_received>>
        \* revert back to follower
        \/  /\ t > term[i]
            /\ state' = [state EXCEPT ![i] = "Follower"]
            /\ term' = [term EXCEPT ![i] = t]
            /\ voted_for' = [voted_for EXCEPT ![i] = j]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "RequestVoteResp",
                                        fTerm |-> t, 
                                        success |-> 1],
                                        RemoveMessage(msg, messages))
            /\ UNCHANGED <<vote_granted, vote_received>>

AppendEntryRespProc(msg) ==
    TRUE 

RequestVoteReplyProc(msg) == 
    TRUE

RequestVoteRespProc(msg) == 
    LET 
        i == msg.fDst
        j == msg.fSrc
        type == msg.fType
        t == msg.fTerm
    IN 
        \/ t = term[i]
            /\ Assert(0, "")
        \/ t < term[i]
            /\ Assert(0, "")
        \/ t > term[i]
            /\ Assert(0, "")

Receive(msg) == 
    \* \/ AppendEntryReqProc(msg) 
    \* \/ AppendEntryRespProc(msg) 
    \/ /\ msg.fType = "RequestVoteReq"
       /\ RequestVoteReqProc(msg) 
    \/ /\ msg.fType = "RequestVoteResp"
       /\ RequestVoteRespProc(msg) 

LeaderProc(i) == 
    /\ state[i] = "Leader"
    /\ \E j \in Servers \ {i}: KeepAlive(i, j)
    /\ UNCHANGED vars

BecomeLeader(i) ==
    /\ Cardinality(vote_received[i]) > Cardinality(Servers) \div 2
    /\ state' = [state EXCEPT ![i] = "Leader"]

CandidateProc(i) == 
    \/ /\ state[i] = "Candidate"
       /\ \E j \in Servers: Campaign(i, j)
    \/ /\ state[i] = "Candidate"
       /\ BecomeLeader(i)

FollowerProc(i) == 
    /\ state[i] = "Follower"
    /\ Timeout(i)

Next == 
    \/ \E i \in Servers : LeaderProc(i)
    \/ \E i \in Servers : CandidateProc(i)
    \/ \E i \in Servers : FollowerProc(i)
    \/ \E msg \in DOMAIN messages : Receive(msg)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================