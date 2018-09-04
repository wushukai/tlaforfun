--------------------------- MODULE LookAsideCache ---------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT Val, Proc, Clock

VARIABLES store
VARIABLES gotval, cctl, cbuf
VARIABLES cache
  
M == INSTANCE Store

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

TypeInvariant == 
    /\ store \in M!StoreValSet
    /\ cctl \in [Proc -> {"rdy", "wait", "cachemiss", "write_cache", "done"}]
    /\ cbuf \in [Proc ->  M!StoreValSet \cup {M!NoVal}]
    /\ gotval \in [Proc -> M!GotValSet]
    /\ cache \in M!StoreValSet \cup {M!NoVal}



ProcStartRead(p) ==
    /\ M!SReadReq(p)
    /\ UNCHANGED << cache >>
    
ProcReadCache(p) ==
    /\ cctl[p] = "wait"
    /\ IF cache # M!NoVal THEN
         /\ cbuf' = [cbuf EXCEPT ![p] = cache]
         /\ cctl' = [cctl EXCEPT ![p] = "done"]
         /\ UNCHANGED << store, gotval, cache>>
       ELSE
         /\ cctl' = [cctl EXCEPT ![p] = "cachemiss"]
         /\ UNCHANGED << store, gotval, cbuf, cache >>
         
ProcCacheMiss(p) == 
    /\ cctl[p] = "cachemiss"
    /\ cbuf' = [cbuf EXCEPT ![p] = store]
    /\ cctl' = [cctl EXCEPT ![p] = "write_cache"]
    /\ UNCHANGED << store, gotval, cache >>
    
ProcWriteCache(p) == 
    /\ cctl[p] = "write_cache"
    /\ cache' = cbuf[p]
    /\ cctl' = [cctl EXCEPT ![p] = "done"]
    /\ UNCHANGED << gotval, store, cbuf >>

ProcReadDone(p) == 
    /\ M!SReadRsp(p)
    /\ PrintVal("gotval", gotval[p]) 
    /\ UNCHANGED << cache >>
    
ProcRead(p) == ProcStartRead(p) \/ ProcReadCache(p) \/ ProcCacheMiss(p) \/ ProcWriteCache(p) \/ ProcReadDone(p)

Write ==
    /\ M!SWr
    /\ cache' = M!NoVal
    

Init ==  M!SInit /\ cache = M!NoVal

Next ==  Write \/  (\E p \in Proc: ProcRead(p))

Spec == Init /\ [][Next]_<<gotval, store, cctl, cbuf, cache>>



=============================================================================
\* Modification History
\* Last modified Tue Sep 04 10:20:24 CST 2018 by UCloud
\* Created Wed Aug 15 18:53:32 CST 2018 by UCloud
