---------------------------- MODULE Synchronizer ----------------------------
VARIABLES threadAWaiting, threadBWaiting

SyncThreadInit == 
  /\ threadAWaiting = FALSE
  /\ threadBWaiting = FALSE
  
(* In a synchronized behavior, as long as thread A needs to wait, 
   its variables must not change. *)
waitingForB(threadAVars) == 
  threadAWaiting
    => UNCHANGED threadAVars

waitingForA(threadBVars) ==
  threadBWaiting
    => UNCHANGED threadBVars
  
(* When the action needing synchronization on thread A occurs in a behavior, 
   either A needs to wait or B becomes ready depending on whether B was waiting. *)
threadA(threadAAction) ==
  threadAAction => 
    IF threadBWaiting 
    THEN
      /\ threadBWaiting' = FALSE 
      /\ UNCHANGED threadAWaiting
    ELSE 
      /\ threadAWaiting' = TRUE 
      /\ UNCHANGED threadBWaiting
    
threadB(threadBAction) ==
  threadBAction => 
    IF threadAWaiting 
    THEN 
      /\ threadAWaiting' = FALSE 
      /\ UNCHANGED threadBWaiting
    ELSE
      /\ threadBWaiting' = TRUE 
      /\ UNCHANGED threadAWaiting
  
SyncThreadActions(threadAVars, threadBVars, threadAAction, threadBAction) ==
  /\ waitingForA (threadBVars)
  /\ waitingForB(threadAVars)
  /\ threadA(threadAAction)
  /\ threadB(threadBAction)

SyncThreadNext(threadAVars, threadBVars, threadAAction, threadBAction)
  == SyncThreadActions(threadAVars, threadBVars, threadAAction, threadBAction)

Spec(threadAVars, threadBVars, threadAAction, threadBAction) == 
  /\ SyncThreadInit 
  /\ [][SyncThreadNext(threadAVars, threadBVars, threadAAction, threadBAction)]_<<threadAVars, threadBVars, threadAWaiting, threadBWaiting>>

=============================================================================
\* Modification History
\* Last modified Thu Jun 13 10:14:25 AST 2019 by marko
\* Created Mon Jun 10 09:52:33 AST 2019 by marko
