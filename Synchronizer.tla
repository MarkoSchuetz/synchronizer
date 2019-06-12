---------------------------- MODULE Synchronizer ----------------------------
VARIABLES threadAWaiting, threadBWaiting

Init == 
  /\ threadAWaiting = FALSE
  /\ threadBWaiting = FALSE
  
waitingForB(threadAVars) == 
  threadAWaiting
    => UNCHANGED threadAVars

waitingForA(threadBVars) ==
  threadBWaiting
    => UNCHANGED threadBVars
  
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
  /\ waitingForA(threadBVars) 
  /\ waitingForB(threadAVars)
  /\ threadA(threadAAction)
  /\ threadB(threadBAction)

=============================================================================
\* Modification History
\* Last modified Mon Jun 10 14:02:08 AST 2019 by marko
\* Created Mon Jun 10 09:52:33 AST 2019 by marko
