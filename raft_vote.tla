--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers, FiniteSets, TLC
VARIABLES state, messages, voted_for, term
vars == <<state, messages, voted_for, term>>

Follower == 0 
Candidate == 1
Leader == 2

Servers == {"s0", "s1", "s2"}

Init ==
    /\ state = [s \in Servers |-> Follower]
    /\ messages = [m \in {} |-> 0]
    /\ voted_for = [s \in Servers |-> ""]
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

Tx(msg) == messages' = AddMessage(msg, messages)

Rx(msg) == messages' = RemoveMessage(msg, messages)

KeepAlive(i, j) == 
    /\ state[i] = Leader
    /\ Tx([fSrc |-> i,
           fDst |-> j,
           fType |-> "AppendEntryReq",
           fTerm |-> term[i]])
    /\ UNCHANGED <<vars>>

Timeout(i) == 
    /\ state[i] # Leader 
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ UNCHANGED <<messages, voted_for, term>>

CandidateCampaign(i) == 
    /\ state[i] = Candidate 
    /\ voted_for[i] = ""
    /\ voted_for = [voted_for EXCEPT ![i] = i]
    /\ \A j \in Servers : 
        /\ j # i
        /\ Tx([fSrc |-> i, 
               fDst |-> j, 
               fType |-> "RequestVoteReq", 
               fTerm |-> term[i]])

AppendEntryReqProc(msg) == 
    LET 
        i == msg.fDst
        j == msg.fSrc
        type == msg.fType
        t == msg.fTerm
    IN 
        \/ t = term[i]
            \* not yet voted for re-request
            \/ /\ voted_for[i] = j \/ voted_for[i] = ""
               /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> t, 
                                        success |-> 1],
                                        RemoveMessage(msg, messages))
            \* voted for someone else 
            \/ /\ voted_for[i] # j
               /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> t, 
                                        success |-> 0],
                                        RemoveMessage(msg, messages))
        \/ t < term[i]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> term[i], 
                                        success |-> 0],
                                        RemoveMessage(msg, messages))
        \* revert back to follower
        \/  /\ t > term[i]
            /\ state' = [state EXCEPT ![i] = Follower]
            /\ term' = [term EXCEPT ![i] = t]
            /\ voted_for' = [voted_for EXCEPT ![i] = j]
            /\ messages' = AddMessage([fSrc |-> i, 
                                        fDst |-> j, 
                                        fType |-> "AppendEntryResp",
                                        fTerm |-> t, 
                                        success |-> 1],
                                        RemoveMessage(msg, messages))

AppendEntryRespProc(msg) ==
    TRUE 

RequestVoteReqProc(msg) == 
    TRUE 

RequestVoteReplyProc(msg) == 
    TRUE

Receive(msg) == 
    \/ AppendEntryReqProc(msg) 
    \/ AppendEntryRespProc(msg) 
    \/ RequestVoteReqProc(msg) 
    \/ RequestVoteReplyProc(msg) 
        \* \/ t = term[i] 
        \*     \/  /\ type = "AppendEntryReq"
        \*         /\ Tx([ fSrc |-> i,
        \*                 fDst |-> j, 
        \*                 fType |-> "AppendEntryResp",
        \*                 fTerm |-> t, 
        \*                 fSuccess |-> 1])
        \*         /\ Remove(msg)
            \* \/ type = "AppendEntryResp"
            \*     /\ TRUE
            \* \/ type = "RequestVoteReq"
            \*     /\ TRUE
            \* \/ type = "RequestVoteResp"
            \*     /\ TRUE
LeaderProc(i) == 
    /\ state[i] = Leader
        \/ \E j \in Servers \ {i}: KeepAlive(i, j)

CandidateProc(i) == 
    /\ state[i] = Candidate
        \/ \A j \in Servers \ {i}: Campaign(i, j)

FollowerProc(i) == 
    /\ state[i] = Follower
        \/ Timeout(i)

Next == 
    \/ \E i \in Servers : LeaderProc(i)
    \/ \E i \in Servers : CandidateProc(i)
    \/ \E i \in Servers : FollowerProc(i)
    \* \/ \E msg \in DOMAIN messages : Receive(msg)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================