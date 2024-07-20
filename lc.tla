--------------------------------- MODULE lc ---------------------------------
EXTENDS Integers

CONSTANT N, STOP
ASSUME (N \in Nat)

Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i \in j

(*
--algorithm lc {
    variable msg = [n \in Procs |-> 0];
    fair process (p \in Procs)
    variable lc = 0; {
        J0: while (lc < STOP) {
            either
                LRec: lc := SetMax({ lc + 1, msg[self] + 1 });
            or
            Send: {
                lc := lc + 1;
                with (k \in Procs \ {self}) {
                    msg[k] := lc
                }
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ba96006" /\ chksum(tla) = "73a30268")
VARIABLES pc, msg, lc

vars == << pc, msg, lc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ msg = [n \in Procs |-> 0]
        (* Process p *)
        /\ lc = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF lc[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "LRec"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << msg, lc >>

LRec(self) == /\ pc[self] = "LRec"
              /\ lc' = [lc EXCEPT ![self] = SetMax({ lc[self] + 1, msg[self] + 1 })]
              /\ pc' = [pc EXCEPT ![self] = "J0"]
              /\ msg' = msg

Send(self) == /\ pc[self] = "Send"
              /\ lc' = [lc EXCEPT ![self] = lc[self] + 1]
              /\ \E k \in Procs \ {self}:
                   msg' = [msg EXCEPT ![k] = lc'[self]]
              /\ pc' = [pc EXCEPT ![self] = "J0"]

p(self) == J0(self) \/ LRec(self) \/ Send(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Jul 20 10:36:41 BRT 2024 by noghartt
\* Created Sat Jul 20 02:15:13 BRT 2024 by noghartt
