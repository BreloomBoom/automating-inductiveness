------------------------------- MODULE Bracha -------------------------------

\* Copy of Randomization.tla is in repository
EXTENDS FiniteSets, Integers, Randomization

CONSTANTS
  \* Number of processes
  N,
  \* Max number of faulty
  T,
  \* Actual number of faulty
  F,
  \* Set of rounds
  Rounds

\* Set of currect processes
Correct == 1..(N - F)
\* Set of faulty processes
Faulty == (N - F + 1)..N
\* Set of all processes
All == Correct \cup Faulty

\* Set of values to decide
Values == { 0, 1 }
\* Value to denote no decision
NoDecision == -1
\* Values and no decision
AllV == { -1, 0, 1 }
\* Set of steps
Steps == 1..3

MessageType == [ src : All, v : Values, d : BOOLEAN ]
FaultyMsgType == [ src : Faulty, v : Values, d : BOOLEAN ]

-----------------------------------------------------------------------------

VARIABLES
  \* Current value for each process (x_P)
  value,
  \* Whether a d-message has to be broadcasted next or not
  dvalue,
  \* Decision by a process
  decision,
  \* The round each process is on
  round,
  \* The step each process is on
  step,
  \* Whether a process should broadcast or not
  broadcast,
  \* Messages that have been broadcast
  messages,
  \* Messages that have been validated
  valid
  
-----------------------------------------------------------------------------

Step1(p) ==
  /\ step[p] = 1
  /\ broadcast[p] = FALSE
  /\ \E received \in SUBSET valid[round[p]][1]:
        /\ Cardinality(received) = N - T
        /\ LET weights == [ v \in Values |-> Cardinality({ m \in received : m.v = v }) ]
            IN \/ weights[0] >= weights[1] /\ value' = [ value EXCEPT ![p] = 0 ]
               \/ weights[1] >= weights[0] /\ value' = [ value EXCEPT ![p] = 1 ]
  /\ broadcast' = [ broadcast EXCEPT ![p] = TRUE ]
  /\ step' = [ step EXCEPT ![p] = 2 ]
  /\ UNCHANGED << dvalue, decision, round, messages, valid >>

Step2(p) ==
  /\ step[p] = 2
  /\ broadcast[p] = FALSE
  /\ \E received \in SUBSET valid[round[p]][2]:
        /\ Cardinality(received) = N - T
        /\ LET weights == [ v \in Values |-> Cardinality({ m \in received : m.v = v }) ]
            IN \/ \E v \in Values:
                     /\ 2 * weights[v] >= N
                     /\ value' = [ value EXCEPT ![p] = v ]
                     /\ dvalue' = [ dvalue EXCEPT ![p] = TRUE ]
               \/ /\ (\A v \in Values: 2 * weights[v] < N) 
                  /\ /\ UNCHANGED << value, dvalue >>
  /\ broadcast' = [ broadcast EXCEPT ![p] = TRUE ]
  /\ step' = [ step EXCEPT ![p] = 3 ]
  /\ UNCHANGED << decision, round, messages, valid >>

Step3(p) ==
  /\ step[p] = 3
  /\ broadcast[p] = FALSE
  /\ \E received \in SUBSET valid[round[p]][2]:
        /\ Cardinality(received) = N - T
        /\ LET weights == [ v \in Values |-> Cardinality({ m \in received : m.v = v /\ m.d = TRUE }) ]
            IN \/ \E v \in Values:
                     /\ weights[v] >= T + 1
                     /\ value' = [ value EXCEPT ![p] = v ]
                     /\ IF weights[v] >= 2 * T + 1
                        THEN decision' = decision \cup {p}
                        ELSE UNCHANGED << decision >>
               \/ /\ (\A v \in Values: weights[v] < T + 1)
                  /\ (\E v \in Values: value' = [ value EXCEPT ![p] = v ])
                  /\ UNCHANGED << decision >>
  /\ broadcast' = [ broadcast EXCEPT ![p] = TRUE ]
  /\ dvalue' = [ dvalue EXCEPT ![p] = FALSE ]
  /\ step' = [ step EXCEPT ![p] = 1 ]
  /\ round' = [ round EXCEPT ![p] = round[p] + 1 ]
  /\ UNCHANGED << messages, valid >>

Broadcast(p) ==
  /\ round[p] \in Rounds 
  /\ broadcast[p] = TRUE
  /\ LET r == round[p]
         s == step[p]
         v == value[p]
         b == dvalue[p]
      IN messages' = [ messages EXCEPT ![r][s] = messages[r][s] \cup [ src : {p}, v : {v}, d : {b} ]  ]
  /\ broadcast' = [ broadcast EXCEPT ![p] = FALSE ]
  /\ UNCHANGED << value, dvalue, decision, round, step, valid >>

\* Conditions required to validate messages
ValidateInitial(r, s) == r = 1 /\ s = 1

ValidateStep1(r, s, m) ==
  /\ s = 1
  /\ r # 1
  /\ \E received \in SUBSET valid[r - 1][3]:
        /\ Cardinality(received) = N - T
        /\ \/ Cardinality({ msg \in received : msg.v = m.v /\ msg.d = TRUE }) >= T + 1
           \/ (\A v \in Values: Cardinality({ msg \in received : msg.v = v /\ msg.d = TRUE }) < T + 1)

ValidateStep2(r, s, m) ==
  /\ s = 2
  /\ \E received \in SUBSET valid[r][1]:
        /\ Cardinality(received) = N - T
        /\ 2 * Cardinality({ msg \in received : msg.v = m.v }) >= N - T

ValidateStep3(r, s, m) ==
  /\ s = 3
  /\ \E received \in SUBSET valid[r][2]:
        /\ Cardinality(received) = N - T
        /\ \/ m.d = TRUE /\ (\E v \in Values: 2 * Cardinality({ msg \in received : msg.v = m.v }) >= N)
           \/ m.d = FALSE /\ (\A v \in Values:  2 * Cardinality({ msg \in received : msg.v = m.v }) < N)

\* Validation can be done recursively in one step or message by message
\* Message by message was the chosen approach since IVy cannot use recursion
Validate(r, s) == 
  /\ \E m \in messages[r][s]:
        /\ \/ ValidateInitial(r, s)
           \/ ValidateStep1(r, s, m)
           \/ ValidateStep2(r, s, m)
           \/ ValidateStep3(r, s, m)
        /\ messages' = [ messages EXCEPT ![r][s] = messages[r][s] \ {m} ]
       /\ valid' = [ valid EXCEPT ![r][s] = valid[r][s] \cup {m} ]
  /\ UNCHANGED << value, dvalue, decision, round, step, broadcast >>

-----------------------------------------------------------------------------  

Init ==
  /\ N > 3 * T
  /\ T >= F
  \* /\ value \in [ Correct -> Values ]

  \* Optisation accounting for symmetries of starting values
  /\ value \in { [ p \in Correct |-> 0 ], 
                 [ p \in Correct |-> IF p = 1 THEN 1 ELSE 0 ] }
  
  /\ dvalue = [ p \in Correct |-> FALSE ]
  /\ broadcast = [ p \in Correct |-> TRUE ]
  /\ decision = {}
  /\ round = [ r \in Correct |-> 1 ]
  /\ step = [ r \in Correct |-> 1 ]

  \* All Possible Combinations
  \*  /\ messages \in [ Rounds -> [ Steps -> MessageType ] ]
  \*  /\ \A r \in Rounds, s \in Steps: \E v \in Values:
  \*        messages[r][s] \in SUBSET [ src : Faulty, v : {v} ]
  
  \* Optimisation for model checking on TLC
  /\ \E v1, v2, v3 \in Values, b\in BOOLEAN:
        messages = [ r \in Rounds |-> [ s \in Steps |-> 
                     IF s = 1
                     THEN [ src : Faulty, v : {v1}, d : {FALSE} ]
                     ELSE IF s = 2
                     THEN [ src : Faulty, v : {v2}, d : {b} ]
                     ELSE [ src : Faulty, v : {v3}, d : {FALSE} ] ] ]
        
  /\ valid = [ r \in Rounds |-> [ s \in Steps |-> {} ]]
        
Step1Action == \E p \in Correct: Step1(p)
Step2Action == \E p \in Correct: Step2(p)
Step3Action == \E p \in Correct: Step3(p)
BroadcastAction == \E p \in Correct: Broadcast(p)
ValidateAction == \E r \in Rounds, s \in Steps: Validate(r, s)

Next ==
  \/ Step1Action
  \/ Step2Action
  \/ Step3Action
  \/ BroadcastAction
  \/ ValidateAction
  
  
-----------------------------------------------------------------------------

TypeOK ==
  /\ N > 3 * T
  /\ T >= F
  /\ value \in [ Correct -> Values ]
  /\ dvalue \in [ Correct -> BOOLEAN ]
  /\ decision \in SUBSET Correct
  /\ round \in [ Correct -> Rounds ]
  /\ step \in [ Correct -> Steps ]
  /\ broadcast \in [ Correct -> BOOLEAN ]
  /\ messages \in [ Rounds -> [ Steps -> MessageType ] ]
  /\ valid \in [ Rounds -> [ Steps -> MessageType ] ]
  /\ \A r \in Rounds, s \in Steps: 
        messages[r][s] \cap valid[r][s] = {}
        
AgreementInv ==
    \A p1, p2 \in Correct: 
        p1 \in decision /\ p2 \in decision
     => value[p1] = value[p2]

=============================================================================
\* Modification History
\* Last modified Thu Feb 06 16:37:27 AEDT 2025 by breloom
\* Created Wed Feb 05 12:42:42 AEDT 2025 by breloom
