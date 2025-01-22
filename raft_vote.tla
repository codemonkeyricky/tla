--------------------------- MODULE raft_vote ----------------------------
EXTENDS Integers, FiniteSets, TLC
VARIABLES state, messages, voted_for, term
vars == <<state, messages, voted_for>>

Follower == 0 
Candidate == 1
Leader == 2

Servers == {"s0", "s1", "s2"}

Init ==
    /\ state = [s \in Servers |-> Follower]
    /\ messages = [m \in {} |-> 0]
    /\ voted_for = [s \in Servers |-> ""]
    /\ term = [s \in Servers |-> 0]

AddMessage(to_add) == 
    IF to_add \in DOMAIN messages THEN 
        [messages EXCEPT ![to_add] = @ + 1]
    ELSE 
        messages @@ (to_add :> 1)

Tx(msg) == messages' = AddMessage(msg)

LeaderKeepAlive(i, j) == 
    /\ state[i] = Leader
    /\ Tx([fSrc |-> i,
           fDst |-> j,
           fType |-> "AppendEntryReq",
           fTerm |-> term[i]])
    /\ UNCHANGED <<vars>>

Timeout(i) == 
    /\ state[i] # Leader 
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ voted_for[i] = i

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

Receive(msg) == 
    LET 
        i == msg.fSrc
        j == msg.fDst
        type == msg.fType
    IN 
        CASE type = "AppendEntryReq" -> TRUE
        [] type = "AppendEntryResp" -> TRUE
        [] type = "RequestVoteReq" -> TRUE
        [] type = "RequestVoteResp" -> TRUE

Next == 
    \/ \E i, j \in Servers : LeaderKeepAlive(i, j)
    \/ \E i \in Servers : Timeout(i)
    \/ \E i \in Servers : CandidateCampaign(i)
    \/ \E msg \in DOMAIN messages : Receive(msg)

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================