---------------------------- MODULE Test ----------------------------
CONSTANT Message
VARIABLES received, chan, pcThreadA, pcThreadB, threadAWaiting, threadBWaiting

vars == <<received, pcThreadA, pcThreadB, chan, threadAWaiting, threadBWaiting>>

threadALabels == {"send", "other"}
threadBLabels == {"receive", "other"}
threadAVars == <<pcThreadA>> \* All the variables of thread A
threadBVars == <<pcThreadB>> \* ...

CH == INSTANCE Channel WITH Data <- Message
SYNC == INSTANCE Synchronizer

TypeInvariant ==
  /\ CH!TypeInvariant
  /\ received \in Message
  /\ pcThreadA \in threadALabels
  /\ pcThreadB \in threadBLabels

Init ==
  /\ CH!Init
  /\ SYNC!SyncThreadInit
  /\ TypeInvariant
  
threadASend ==
  /\ pcThreadA = "send"
  /\ \E d \in Message: CH!Send(d)
  /\ pcThreadA' = "other"
  /\ UNCHANGED <<received, pcThreadB>>
  
threadAOther ==
  /\ pcThreadA = "other" 
     \* represents the work thread A does other than sending
  /\ pcThreadA' = "send"
  /\ UNCHANGED <<received, threadAWaiting, threadBWaiting, chan, pcThreadB>>
  
threadA == 
  \/ threadASend 
  \/ threadAOther 

threadBReceive ==
  /\ pcThreadB = "receive"
  /\ CH!Rcv
  /\ received' = chan.value
  /\ pcThreadB' = "other"
  /\ UNCHANGED <<pcThreadA>>
   
threadBOther ==
  /\ pcThreadB = "other"
     \* represents the work thread B does other than receiving
  /\ pcThreadB' = "receive"
  /\ UNCHANGED <<received, threadAWaiting, threadBWaiting, chan, pcThreadA>>
  
threadB == threadBReceive \/ threadBOther

Next == 
  /\ \/ threadA
     \/ threadB
  /\ SYNC!SyncThreadActions(threadAVars, threadBVars, \E d \in Message: CH!Send(d), CH!Rcv)

Spec == 
  /\ Init  
  /\ [][Next]_vars
-----------------------------------------------------------------------------
ThreadAWaitsCorrectly == 
  [][\E d \in Message: CH!Send(d) 
       => \/ /\ threadBWaiting 
             /\ \neg threadBWaiting' 
             /\ UNCHANGED threadAWaiting 
          \/ /\ \neg threadBWaiting 
             /\ threadAWaiting' 
             /\ UNCHANGED threadBWaiting]_vars  

ThreadBWaitsCorrectly == 
  [][CH!Rcv
       => \/ /\ threadAWaiting 
             /\ \neg threadAWaiting' 
             /\ UNCHANGED threadBWaiting 
          \/ /\ \neg threadAWaiting 
             /\ threadBWaiting' 
             /\ UNCHANGED threadAWaiting]_vars  
=============================================================================
\* Modification History
\* Last modified Thu Jun 13 11:01:20 AST 2019 by marko
\* Created Mon Jun 10 10:41:14 AST 2019 by marko
