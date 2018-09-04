------------------------------- MODULE Store -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT Val, Proc, Clock

VARIABLES store
VARIABLES gotval, cctl, cbuf
  

NoVal == CHOOSE x: x \notin Val

StoreValSet == [clock: Clock, val: Val \cup {NoVal}]
GotValSet == Seq(StoreValSet)

STypeInvariant == 
    /\ store \in StoreValSet
    /\ cctl \in [Proc -> {"rdy", "wait", "done", "exit"}]
    /\ cbuf \in [Proc ->  StoreValSet \cup {NoVal}]
    /\ gotval \in [Proc -> GotValSet]
   



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
    /\ gotval' = [gotval EXCEPT ![p] = Append(@, cbuf[p])]
    /\ UNCHANGED << store, cbuf>>
    
    
    
SRd(p) == SReadReq(p) \/ SDoRead(p) \/ SReadRsp(p)


SWr == 
    /\ store' = [store EXCEPT !.clock = @+1, !.val = CHOOSE val \in Val: TRUE ]
    /\ UNCHANGED << cctl, cbuf, gotval >>


SInit == 
    /\ store = [clock |->  1, val |-> NoVal]
    /\ cctl = [p \in Proc |-> "rdy"]
    /\ cbuf = [p \in Proc |-> NoVal]
    /\ gotval = [p \in Proc |-> << >>]
        

SNext == 
    \/ \E p \in Proc: SRd(p) 
    \/ SWr
    
SSpec == SInit /\ [][SNext]_<<gotval, store, cctl, cbuf>>

Inv == \A p \in Proc: 
    LET f[i \in 0 .. Len(gotval[p]), n \in Nat] ==
        IF i = 0 THEN
            TRUE
        ELSE
            IF gotval[p][i].clock > n THEN
                FALSE
            ELSE
                f[i-1, gotval[p][i].clock]
    IN IF Len(gotval[p]) = 0 THEN
         f[0, 0]
       ELSE
         f[Len(gotval[p])-1, gotval[p][Len(gotval[p])].clock]
=============================================================================
\* Modification History
\* Last modified Mon Sep 03 17:24:43 CST 2018 by UCloud
\* Created Mon Aug 20 22:35:56 CST 2018 by UCloud
