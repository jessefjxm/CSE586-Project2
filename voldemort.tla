-------------------------------- MODULE voldemort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, ReadQ, WriteQ, FAILNUM
ASSUME N=5 /\ C=1 /\ STOP<10 /\ 1<=ReadQ /\ ReadQ<=3 /\ 1<=WriteQ /\ WriteQ<=3 /\ 0<=FAILNUM /\ FAILNUM<=2
Nodes == 1..N
Clients == N+1 .. N+C
(*
--algorithm voldemort
{
    variable    
        FailNum = FAILNUM,
        up = [n \in Nodes |-> TRUE],                        \* initially all nodes are up
        db = [n \in Nodes |-> {[ver |-> 0, val |->0]}];     \* all nodes have db
    define
    {
        getDBNode(x) == CHOOSE i \in db[x]:TRUE                             \* to get element from set db
        HighestVersionNumber(S) == CHOOSE x \in S:\A y \in S: getDBNode(x).ver >= getDBNode(y).ver    \* find HVN in set db by array S
        UpNodes == {u \in Nodes: up[u]=TRUE}                                \* Choose the true node from up
        ReturnReadQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=ReadQ   \* highest version number
        ReturnWriteQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=WriteQ \* return first WriteQ-th elements from UpNodes
    }
    
    fair process(c \in Clients)
    variable cntr=0, hver=0, Q={};
    {
    CL: while(cntr<=STOP){
        cntr:= cntr + 1;
        \* get highest version number from ReturnReadQ
        hver:= HighestVersionNumber(ReturnReadQ);
        Q:= ReturnWriteQ;
        \* write val=cntr to WriteQ with HVN
        with (j \in Q){ 
            db[j]:= {[ver |-> hver+1, val |-> cntr]};
        };
        print <<"Clients end.">>; 
      }
    }
    
    fair process(n \in Nodes)
    { 
    NODE: while( TRUE ){
        if( FailNum > 0 /\ up[self]=TRUE ){ \* can fail -> fail it
            up[self]:= FALSE;
            FailNum:= FailNum - 1;     
            print <<"Node Fail:", self>>;       
        }else if( up[self]=FALSE ){ \* failed -> recover it
            up[self]:= TRUE;
            FailNum:= FailNum + 1;
            print <<"Node Recover:", self>>;    
        }
      }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, db, pc

(* define statement *)
getDBNode(x) == CHOOSE i \in db[x]:TRUE
HighestVersionNumber(S) == CHOOSE x \in S:\A y \in S: getDBNode(x).ver >= getDBNode(y).ver
UpNodes == {u \in Nodes: up[u]=TRUE}
ReturnReadQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=ReadQ
ReturnWriteQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=WriteQ

VARIABLES cntr, hver, Q

vars == << FailNum, up, db, pc, cntr, hver, Q >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> {[ver |-> 0, val |->0]}]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> 0]
        /\ Q = [self \in Clients |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "CL"
                                        [] self \in Nodes -> "NODE"]

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self]<=STOP
                  THEN /\ cntr' = [cntr EXCEPT ![self] = cntr[self] + 1]
                       /\ PrintT(<<"Current cntr:", cntr'[self]>>)
                       /\ PrintT(<<"UpNodes:", UpNodes>>)
                       /\ PrintT(<<"ReturnReadQ:", ReturnReadQ>>)
                       /\ PrintT(<<"ReturnWriteQ:", ReturnWriteQ>>)
                       /\ hver' = [hver EXCEPT ![self] = HighestVersionNumber(ReturnReadQ)]
                       /\ PrintT(<<"Get hver:", hver'[self]>>)
                       /\ Q' = [Q EXCEPT ![self] = ReturnWriteQ]
                       /\ PrintT(<<"Get WriteQ:", Q'[self]>>)
                       /\ \E j \in Q'[self]:
                            db' = [db EXCEPT ![j] = {[ver |-> hver'[self]+1, val |-> cntr'[self]]}]
                       /\ PrintT(<<"Clients end.">>)
                       /\ pc' = [pc EXCEPT ![self] = "CL"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << db, cntr, hver, Q >>
            /\ UNCHANGED << FailNum, up >>

c(self) == CL(self)

NODE(self) == /\ pc[self] = "NODE"
              /\ IF FailNum > 0 /\ up[self]=TRUE
                    THEN /\ up' = [up EXCEPT ![self] = FALSE]
                         /\ FailNum' = FailNum - 1
                         /\ PrintT(<<"Node Fail:", self>>)
                    ELSE /\ IF up[self]=FALSE
                               THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                    /\ FailNum' = FailNum + 1
                                    /\ PrintT(<<"Node Recover:", self>>)
                               ELSE /\ TRUE
                                    /\ UNCHANGED << FailNum, up >>
              /\ pc' = [pc EXCEPT ![self] = "NODE"]
              /\ UNCHANGED << db, cntr, hver, Q >>

n(self) == NODE(self)

Next == (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))

\* END TRANSLATION
consistentProperty == /\ C=1 /\ N=5 /\ ReadQ=2 /\ WriteQ=2 /\ STOP=0 /\ FAILNUM=2
=============================================================================
\* Observation & thoughts:
\* 1. Grammer is quite hard and different from other language. Keep grammer right solves most of the bug.
\* 2. Data structures like set, array, record have quite different behavior and operator. 
\*    Multiple data structures & corresponding have been used in this project, and cause many misunderstanding when developing.
\* 3. The core logic is not that hard, compare to the difficulty of successfully write down code with correct TLA+ format.
\* teamMember_1: (Hongyu Wang, 50206502)
\* teamMember_2: (Libing Wu, 50042948)
