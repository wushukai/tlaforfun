--------------------------- MODULE LookAsideCache ---------------------------

EXTENDS Naturals, Sequences, Store
(*
VARIABLES cliCtlRead, cliReadBuf, cliReadHistory, cliCacheCtl, cliCacheBuf, cliCtlWrite
VARIABLES cache, truth



TypeInvariant == 
    /\ cliCtlRead \in [Proc -> {"rdy", "busy", "wait", "done"}]
    /\ cliReadBuf \in [Proc -> Nat \cup NoVal]
    /\ cliReadHistory \in [Proc -> Seq(Nat)]
    /\ cliCtlWrite \in {"rdy", "wrtrue", "invalidcache"}
    /\ cache \in Nat
    /\ truth \in Nat
    /\ cacheCtl  \in [Proc -> {"rdy", "busy", "done"}]
    
CliReadReq(p) == 
    /\ cliCtlRead[p] = "rdy"
    /\ cliCtlRead' = [cliCtlRead' EXCEPT ![p] = "busy"]
    /\ UNCHANGED << cliReadBuf, cliReadHistory, cliCtlWrite, cache, truth, cliCacheCtl, cliCacheBuf>>


CliDoRead(p) ==
    /\ cliCtlRead[p] = "busy"
    /\ cache # NoVal /\ cliReadBuf' = [ cliReadBuf EXCEPT ![p]=cache ] /\ cliCtlRead' = "done"
    /\ UNCHANGED << cliReadHistory, cliCtlWrite, cache, truth >>
    
cliReadMiss(p) == 
    /\ cliCtlRead[p] = "busy" /\ cache = NoVal
    /\ cliCtlRead' = [cliCtlRead EXCEPT ![p] = "wait"]  
    /\ cliCacheCtl' = [cliCacheCtl EXCEPT ![p] = "busy"]
    /\ UNCHANGED << cliReadBuf, cliReadHi >>
    
 
*)

 

=============================================================================
\* Modification History
\* Last modified Tue Aug 21 20:54:39 CST 2018 by UCloud
\* Created Wed Aug 15 18:53:32 CST 2018 by UCloud
