------------------------------ MODULE Ben_Or83 -----------------------------

EXTENDS FiniteSets, Integers, Randomization

CONSTANTS
  \* Number of processes
  N,
  \* Max number of faulty
  T,
  \* Actual number of faulty
  F,
  \* Set of rounds (note that endive does not take 1..3)
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
\* Possible steps
Steps == 1..3

-----------------------------------------------------------------------------

VARIABLES
  \* Current value for each process (x_P)
  \* @type: Int -> Int;
  value,
  \* Decision by a process
  \* @type: Set(Int);
  decision,
  \* The round each process is on
  \* @type: Int -> Int;
  round,
  \* The step each process is on
  \* @type: Int -> Int;
  step,
  \* Set of type 1 messages by round
  \* @type: Int -> (Int -> Int);
  type1,
  \* Set of type 2 D messages by round
  \* @type: Int -> (Int -> Int);
  type2D,
  \* Set of type 2 ? messages by round
  \* @type: Int -> (Int -> Bool);
  type2Q

-----------------------------------------------------------------------------

Step1(p) ==
  /\ step[p] = 1
  /\ type1' = [ type1 EXCEPT ![round[p]][p] = value[p] ]
  /\ step' = [ step EXCEPT ![p] = 2 ]
  /\ UNCHANGED << value, decision, round, type2D, type2Q >>
  
Step2(p) ==
  /\ step[p] = 2
  /\ \E received \in SUBSET { pr \in All : type1[round[p]][pr] # NoDecision }:
        /\ Cardinality(received) = N - T
        /\ \/ \E v \in Values:
                 /\ 2 * Cardinality({ pr \in received : type1[round[p]][pr] = v }) > N + T
                 /\ type2D' = [ type2D EXCEPT ![round[p]][p] = v ]
                 /\ type2Q' = type2Q
           \/ /\ \A v \in Values: 2 * Cardinality({ pr \in received : type1[round[p]][pr] = v }) <= N + T
              /\ type2Q' = [ type2Q EXCEPT ![round[p]][p] = TRUE ]   
              /\ type2D' = type2D   
  /\ step' = [ step EXCEPT ![p] = 3 ]
  /\ UNCHANGED << value, decision, round, type1 >>
  
Step3(p) ==
  /\ step[p] = 3
  /\ \E received \in SUBSET { pr \in All : type2D[round[p]][pr] # NoDecision \/
                                           type2Q[round[p]][pr] = TRUE }:
        /\ Cardinality(received) = N - T
        /\ LET weights == [ v \in Values |-> Cardinality({ pr \in received : type2D[round[p]][pr] = v })]
            IN
            \/ (\E v \in Values:
                 /\ weights[v] >= T + 1
                 /\ value' = [ value EXCEPT ![p] = v ]
                 /\ IF 2 * weights[v] > N + T
                    THEN decision' = decision \cup {p}
                    ELSE decision' = decision)
             \/ /\ (\A v \in Values: weights[v] < T + 1)
                /\ (\E nextV \in Values: value' = [ value EXCEPT ![p] = nextV ])
                /\ decision' = decision
  /\ round[p] + 1 \in Rounds
  /\ round' = [ round EXCEPT ![p] = round[p] + 1 ]
  /\ step' = [ step EXCEPT ![p] = 1 ]
  /\ UNCHANGED << type1, type2D, type2Q >>

-----------------------------------------------------------------------------

\* Faults can either be injected at the start or as a faulty step
\* Note that the step allows for more possible steps than injecting at the start
    
\* FaultyStep ==
\*   /\ \E r \in Rounds, f \in Faulty:
\*         /\ (\E v \in AllV: type1' = [type1 EXCEPT ![r][f] = v])
\*         /\ (\E v \in AllV: type2D' = [type2D EXCEPT ![r][f] = v])
\*         /\ (\E b \in BOOLEAN: type2Q' = [type2Q EXCEPT ![r][f] = b])
\*   /\ UNCHANGED << value, decision, round, step >>

-------------------------------------------------------------------------------

Init == 
  /\ N > 5 * T
  /\ T >= F
  /\ value \in [ Correct -> Values ] 
  /\ decision = {}
  /\ round = [ r \in Correct |-> 1 ]
  /\ step = [ r \in Correct |-> 1 ]
    
  \* Injects faulty messages considering one combination
  /\ type1 = [ r \in Rounds |-> [ p \in All |-> IF p \in Correct THEN NoDecision ELSE CHOOSE v \in AllV : TRUE ] ]
  /\ type2D = [ r \in Rounds |-> [ p \in All |-> IF p \in Correct THEN NoDecision ELSE CHOOSE v \in AllV : TRUE ] ]
  /\ type2Q = [ r \in Rounds |-> [ p \in All |-> IF p \in Correct THEN FALSE ELSE CHOOSE v \in BOOLEAN : TRUE ] ]

  \* Injects faulty messages at the start in all possible combinations
  \* /\ \E m1 \in [ Rounds -> [ All -> AllV ] ]:
  \*       /\ type1 = m1
  \*       /\ (\A p \in Correct, r \in Rounds: type1[r][p] = NoDecision)
  \* /\ \E m2D \in [ Rounds -> [ All -> AllV ] ]:
  \*       /\ type2D = m2D
  \*       /\ (\A p \in Correct, r \in Rounds: type2D[r][p] = NoDecision)
  \* /\ \E m2Q \in [ Rounds -> [ All -> BOOLEAN ] ]:
  \*       /\ type2Q = m2Q
  \*       /\ (\A p \in Correct, r \in Rounds: type2Q[r][p] = FALSE)

CorrectStep ==
  \E p \in Correct:
    \/ Step1(p)
    \/ Step2(p)
    \/ Step3(p)

Next == CorrectStep \* \/ FaultyStep

NextUnchanged == UNCHANGED << value, decision, round, step, type1, type2D, type2Q >>

-----------------------------------------------------------------------------

TypeOK ==
  /\ N > 5 * T
  /\ T >= F
  /\ value \in [ Correct -> Values ] \* 2^N
  /\ decision \in SUBSET Correct \* 2^(N - T)
  /\ round \in [ Correct -> Rounds ] \* R^(N - T)
  /\ step \in [ Correct -> Steps ] \* R^(N - T)
  /\ type1 \in [ Rounds -> [ All -> AllV ] ] \* 3^(RN)
  /\ type2D \in [ Rounds -> [ All -> AllV ] ] \* 3^(RN)
  /\ type2Q \in [ Rounds -> [ All -> BOOLEAN ] ] \* 2^(RN)
  
  \* /\ \A r \in Rounds: 
  \*       { p \in All : type2D[r][p] # NoDecision 
  \*                  /\ type2Q[r][p] = TRUE 
  \*                  /\ p \in Correct } = {}
       
Num == 8

TypeOKRandom ==
  /\ value \in RandomSubset(Num, [ Correct -> Values ])
  /\ decision \in RandomSubset(Num, SUBSET Correct)
  /\ round \in RandomSubset(Num, [ Correct -> Rounds ])
  /\ step \in RandomSubset(Num, [ Correct -> Steps ])
  /\ type1 \in RandomSubset(Num, [ Rounds -> [ All -> AllV ] ])
  /\ type2D \in RandomSubset(Num, [ Rounds -> [ All -> AllV ] ])
  /\ type2Q \in RandomSubset(Num, [ Rounds -> [ All -> BOOLEAN ] ])

\* Safety condition
AgreementInv ==
    \A p1, p2 \in Correct: 
        p1 \in decision /\ p2 \in decision
     => value[p1] = value[p2]

\* Possible predicate in generation
ExistsQuorum(r, v) ==
    LET nv == Cardinality({ p \in All : type2D[r][p] = v })
        n == Cardinality({ p \in All : type2D[r][p] # NoDecision })
    IN 
    /\ n >= N - T
    /\ nv >= T + 1
    /\ 2 * nv > N + T

\* Used in scimitar, the successor of endive
CTICost == 0

=============================================================================
\* Modification History
\* Last modified Thu Jan 16 21:00:57 AEDT 2025 by breloom
\* Created Mon Jan 13 09:53:05 AEDT 2025 by breloom
