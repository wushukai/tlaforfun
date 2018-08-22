------------------------------- MODULE Store -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT Val, Proc, Clock

VARIABLES gotval, store, cctl, cbuf

NoVal == CHOOSE x: x \notin Val

StoreValSet == [clock: Clock, val: Val \cup {NoVal}]
GotValSet == [oldval: StoreValSet \cup {NoVal}, newval: StoreValSet \cup {NoVal}]

TypeInvariant == 
    /\ store \in StoreValSet
    /\ cctl \in [Proc -> {"rdy", "wait", "done", "exit"}]
    /\ cbuf \in [Proc ->  StoreValSet \cup {NoVal}]
    /\ gotval \in [Proc -> GotValSet]
    
PrintVal(id, exp) == Print(<<id, exp>>, TRUE)


SInit == 
    /\ TypeInvariant
    /\ store.clock = 1 /\ store.val = NoVal
    /\ cctl = [p \in Proc |-> "rdy"]
    /\ cbuf = [p \in Proc |-> NoVal]
    /\ gotval = [p \in Proc |-> [oldval |-> NoVal, newval |-> NoVal]]
    
SReadReq(p) == 
    /\ cctl[p] = "rdy"
    /\ cctl' = [cctl EXCEPT ![p] = "wait"]
    /\ UNCHANGED << store, cbuf, gotval >>
    
SDoRead(p) ==
    /\ cctl[p] = "wait"
    /\ cctl' = [cctl EXCEPT ![p] = "done"]
    /\ cbuf' = [cbuf EXCEPT ![p] = store]
    /\ UNCHANGED << store, gotval >>
    
SReadRsp(p) == 
    /\ cctl[p] = "done"
    /\ cctl' = [cctl EXCEPT ![p] = "rdy"]
    /\ gotval' = [gotval EXCEPT ![p] = [gotval[p] EXCEPT !.oldval = gotval[p].newval, !.newval = cbuf[p]]]
    /\ PrintVal("wr", gotval) 
    /\ UNCHANGED << store, cbuf >>
    
SRd(p) == SReadReq(p) \/ SDoRead(p) \/ SReadRsp(p)


SWr == 
    /\ LET newclk == store.clock + 1
       IN \E val \in Val: store' = IF newclk \in Clock 
                                    THEN [store EXCEPT !.clock = newclk, !.val = val]
                                    ELSE store
    /\ UNCHANGED << cctl, cbuf, gotval >>
    
SNext == 
    \/ (\E p \in Proc: SRd(p) /\ PrintVal("rsp", gotval))
    \/ SWr
    
SSpec == SInit /\ [][SNext]_<<gotval, store, cctl, cbuf>>

Inv == \A p \in Proc: (LET gv == gotval[p] IN gv.newval # NoVal /\ gv.oldval # NoVal => gv.newval.clock >= gv.oldval.clock)
=============================================================================
\* Modification History
\* Last modified Wed Aug 22 10:05:07 CST 2018 by UCloud
\* Created Mon Aug 20 22:35:56 CST 2018 by UCloud
