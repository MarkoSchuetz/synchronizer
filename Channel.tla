------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE chan

TypeInvariant ==
  chan \in [value : Data, rdy: {0,1}, ack: {0,1}]
-----------------------------------------------------------------------------  
Init ==
  /\ TypeInvariant
  /\ chan.ack = chan.rdy
  
Send(d) ==
  /\ chan.rdy = chan.ack
  /\ chan' = [chan EXCEPT !.value = d, !.rdy = 1 - @]
  
Rcv == 
  /\ chan.rdy /= chan.ack
  /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
  (\E d \in Data: Send(d)) \/ Rcv
  
Spec ==
  Init /\ [][Next]_chan
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Jun 10 11:32:42 AST 2019 by marko
\* Created Mon Jun 10 10:28:13 AST 2019 by marko
