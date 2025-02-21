---- MODULE dynamo_TTrace_1740154949 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, dynamo

_expression ==
    LET dynamo_TEExpression == INSTANCE dynamo_TEExpression
    IN dynamo_TEExpression!expression
----

_trace ==
    LET dynamo_TETrace == INSTANCE dynamo_TETrace
    IN dynamo_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        local_ring = ()
        /\
        cluster = ({"n0"})
        /\
        debug = ({})
        /\
        local_kv = ([n0 |-> {}, n1 |-> {}, n2 |-> {}])
        /\
        global_kv = ({})
        /\
        global_ring = ((0 :> "n0"))
    )
----

_init ==
    /\ cluster = _TETrace[1].cluster
    /\ local_ring = _TETrace[1].local_ring
    /\ global_kv = _TETrace[1].global_kv
    /\ global_ring = _TETrace[1].global_ring
    /\ local_kv = _TETrace[1].local_kv
    /\ debug = _TETrace[1].debug
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ cluster  = _TETrace[i].cluster
        /\ cluster' = _TETrace[j].cluster
        /\ local_ring  = _TETrace[i].local_ring
        /\ local_ring' = _TETrace[j].local_ring
        /\ global_kv  = _TETrace[i].global_kv
        /\ global_kv' = _TETrace[j].global_kv
        /\ global_ring  = _TETrace[i].global_ring
        /\ global_ring' = _TETrace[j].global_ring
        /\ local_kv  = _TETrace[i].local_kv
        /\ local_kv' = _TETrace[j].local_kv
        /\ debug  = _TETrace[i].debug
        /\ debug' = _TETrace[j].debug

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("dynamo_TTrace_1740154949.json", _TETrace)

=============================================================================

 Note that you can extract this module `dynamo_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `dynamo_TEExpression.tla` file takes precedence 
  over the module `dynamo_TEExpression` below).

---- MODULE dynamo_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, dynamo

expression == 
    [
        \* To hide variables of the `dynamo` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        cluster |-> cluster
        ,local_ring |-> local_ring
        ,global_kv |-> global_kv
        ,global_ring |-> global_ring
        ,local_kv |-> local_kv
        ,debug |-> debug
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_clusterUnchanged |-> cluster = cluster'
        
        \* Format the `cluster` variable as Json value.
        \* ,_clusterJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(cluster)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_clusterModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].cluster # _TETrace[s-1].cluster
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE dynamo_TETrace ----
\*EXTENDS IOUtils, TLC, dynamo
\*
\*trace == IODeserialize("dynamo_TTrace_1740154949.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE dynamo_TETrace ----
EXTENDS TLC, dynamo

trace == 
    <<
    ([local_ring |-> [n0 |-> <<>>, n1 |-> <<>>, n2 |-> <<>>],cluster |-> {},debug |-> {},local_kv |-> [n0 |-> {}, n1 |-> {}, n2 |-> {}],global_kv |-> {},global_ring |-> <<>>]),
    ([local_ring |-> ,cluster |-> {"n0"},debug |-> {},local_kv |-> [n0 |-> {}, n1 |-> {}, n2 |-> {}],global_kv |-> {},global_ring |-> (0 :> "n0")])
    >>
----


=============================================================================

---- CONFIG dynamo_TTrace_1740154949 ----

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Fri Feb 21 08:22:29 PST 2025