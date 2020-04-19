---------------------------- MODULE benor_final ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, F, MAXROUND, INPUT

PROCS == 1..N
valueSet == {0,1}
(*
--algorithm benor_4
 { variable p1Msg={},p2Msg={};
    
    define{
        \*\* check for p1 msg majority if > n/2 move to phase 2
        sentPhase1(r) == {m \in p1Msg: m.round = r}
        \*\* Check for values in p1msg board
        SentP1Msg(r, val) == {m \in p1Msg: (m.round = r) /\ (m.value = val)}
        \*\* check for majority in phase 2
        sentPhase2(r) == {m \in p2Msg: m.round = r}
        \*\* check for values in p2 msg board
        SentP2Msg(r, val) == {m \in p2Msg: (m.round = r) /\ (m.value = val)}
        Checkneg1(r) == {m \in p2Msg: (m.round = r) /\ (m.value = -1)}
    }
        
  
  macro SendP1Msg(node, r, z){
    p1Msg:=p1Msg \union {[nodeid |-> node,round |-> r,value |-> z]};  
  } 
  
  macro SendP2Msg(node, r, z){
    p2Msg:=p2Msg \union {[nodeid |-> node,round |-> r,value |-> z]};  
  } 
    
  fair process (p \in PROCS)
  variable p1v = INPUT[self],p2v = -1,k=1,
           decided = -1, decision = FALSE;
  { \* \* Ben Or Start
   START:
        while(k < MAXROUND){
            \*\*k:= k + 1;
            SendP1Msg(self, k, p1v);
           \*\* Phase 1 of benor begins
     PHASE1:        await(Cardinality(sentPhase1(k)) \geq N-F);
                    if(Cardinality(SentP1Msg(k, 0)) > N \div 2){
                        \*\* checks if 0 is greater
                        p2v:= 0;
                    }
                    else if(Cardinality(SentP1Msg(k,1)) > N \div 2){
                        \*\* checks if 1 is greater
                        p2v:= 1;
                    }
                    else{
                        \*\* sets -1 as p2v and sends msg
                        p2v:= -1;    
                    };   
                    SendP2Msg(self, k, p2v);
     PHASE2:        await(Cardinality(sentPhase2(k)) \geq N-F);
                    if(Cardinality(SentP2Msg(k, 0)) > F){
                        \*\* decided is 0 because 0 is majority
                        decided:= 0;
                        decision:= TRUE; \* \* implies values is decided and consensus can be reached
                    }
                    else if(Cardinality(SentP2Msg(k, 1)) > F){
                        \*\* decided is 1 because 1 is majority
                        decided:= 1;
                        decision:= TRUE; \* \* implies values is decided and consensus can be reached
                    };
                    if(Cardinality(SentP2Msg(k, 0)) > 0){
                        \*\* p1v value is 0 for next round, consensus not achieved here
                        p1v:= 0;
                    }
                    else if(Cardinality(SentP2Msg(k, 1)) > 0){
                        \*\* p1v value is 1 for next round, consensus not achieved here
                        p1v:= 1;
                    }
                    else{
                        \*\* p1v value is randomized for next round, consensus not achieved here
                        p1v:= RandomElement(valueSet)
                    };
            k:= k+1;
        }\* \* while loop ends
  }  
   
  
  } \* \* algorithm ends
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
sentPhase1(r) == {m \in p1Msg: m.round = r}

SentP1Msg(r, val) == {m \in p1Msg: (m.round = r) /\ (m.value = val)}

sentPhase2(r) == {m \in p2Msg: m.round = r}

SentP2Msg(r, val) == {m \in p2Msg: (m.round = r) /\ (m.value = val)}
Checkneg1(r) == {m \in p2Msg: (m.round = r) /\ (m.value = -1)}

VARIABLES p1v, p2v, k, decided, decision

vars == << p1Msg, p2Msg, pc, p1v, p2v, k, decided, decision >>

ProcSet == (PROCS)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ p1v = [self \in PROCS |-> INPUT[self]]
        /\ p2v = [self \in PROCS |-> -1]
        /\ k = [self \in PROCS |-> 1]
        /\ decided = [self \in PROCS |-> -1]
        /\ decision = [self \in PROCS |-> FALSE]
        /\ pc = [self \in ProcSet |-> "START"]

START(self) == /\ pc[self] = "START"
               /\ IF k[self] < MAXROUND
                     THEN /\ p1Msg' = (p1Msg \union {[nodeid |-> self,round |-> k[self],value |-> p1v[self]]})
                          /\ pc' = [pc EXCEPT ![self] = "PHASE1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ p1Msg' = p1Msg
               /\ UNCHANGED << p2Msg, p1v, p2v, k, decided, decision >>

PHASE1(self) == /\ pc[self] = "PHASE1"
                /\ (Cardinality(sentPhase1(k[self])) \geq N-F)
                /\ IF Cardinality(SentP1Msg(k[self], 0)) > N \div 2
                      THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                      ELSE /\ IF Cardinality(SentP1Msg(k[self],1)) > N \div 2
                                 THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                                 ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
                /\ p2Msg' = (p2Msg \union {[nodeid |-> self,round |-> k[self],value |-> p2v'[self]]})
                /\ pc' = [pc EXCEPT ![self] = "PHASE2"]
                /\ UNCHANGED << p1Msg, p1v, k, decided, decision >>

PHASE2(self) == /\ pc[self] = "PHASE2"
                /\ (Cardinality(sentPhase2(k[self])) \geq N-F)
                /\ IF Cardinality(SentP2Msg(k[self], 0)) > F
                      THEN /\ decided' = [decided EXCEPT ![self] = 0]
                           /\ decision' = [decision EXCEPT ![self] = TRUE]
                      ELSE /\ IF Cardinality(SentP2Msg(k[self], 1)) > F
                                 THEN /\ decided' = [decided EXCEPT ![self] = 1]
                                      /\ decision' = [decision EXCEPT ![self] = TRUE]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << decided, decision >>
                /\ IF Cardinality(SentP2Msg(k[self], 0)) > 0
                      THEN /\ p1v' = [p1v EXCEPT ![self] = 0]
                      ELSE /\ IF Cardinality(SentP2Msg(k[self], 1)) > 0
                                 THEN /\ p1v' = [p1v EXCEPT ![self] = 1]
                                 ELSE /\ p1v' = [p1v EXCEPT ![self] = RandomElement(valueSet)]
                /\ k' = [k EXCEPT ![self] = k[self]+1]
                /\ pc' = [pc EXCEPT ![self] = "START"]
                /\ UNCHANGED << p1Msg, p2Msg, p2v >>

p(self) == START(self) \/ PHASE1(self) \/ PHASE2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PROCS: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCS : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Agreement == \A p1,p2 \in PROCS: decided[p1] # -1 /\ decided[p2] # -1 => decided[p1] = decided[p2]
MinorityReport == \E i \in PROCS: decided[i] # 0
BaitProgress == \E i \in PROCS: decision[i] = TRUE => decided[i] # 0 /\ decided[i] # 1
Progress == <>(\A i \in PROCS: pc[i] = "Done" => decided[i] # -1)


=============================================================================
\* Modification History
\* Last modified Sun Apr 19 19:38:16 EDT 2020 by yashf
\* Created Sun Apr 19 19:36:37 EDT 2020 by yashf
