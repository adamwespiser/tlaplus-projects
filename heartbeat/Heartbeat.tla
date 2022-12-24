----------------------------- MODULE Heartbeat -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS N, NULL, Data

ASSUME NULL \notin Data
ASSUME N \in Nat \ {0}
ASSUME N > 2

Procs == 1..N

(*--algorithm heartbeat_reliable

variables
  procs = {i: i \in 1..N};
  all_procs = {i: i \in 0..N};
  queue = [x \in procs |-> <<>>];
  seq = [x \in all_procs |-> 0];
  deliver = [x \in all_procs |-> {}];
  init_message = CHOOSE x \in Data: TRUE;
  broadcast = [x \in all_procs |-> {}];

  
define
  Neighbors(s_arg) == procs \ {s_arg}
  (* Invariants *)
  AllDelivered == \A p \in procs: init_message \in deliver[p]
  AllDone == \A t \in procs: pc[t] = "Done"
  DeliveredAtEnd == <>AllDelivered
  (* Section 5.2 Reliable Broadcast *)
  Validity == \E p \in Procs: init_message \in broadcast[p] => <>(init_message \in deliver[p])
  Agreement == \E p \in Procs: init_message \in deliver[p] => <>(\A y \in Procs: init_message \in deliver[y])
  UniformIntegrity == (\E x \in Procs: init_message \in broadcast[x]) ~> (\A y \in Procs: init_message \in deliver[y])
end define;

macro send(p_arg, q_arg, m_arg) begin \* send_p,q(m), send m on p -> q
  broadcast[p_arg] := broadcast[p_arg] \union {m_arg} ||
  queue[q_arg] := Append(queue[q_arg], [from |-> p_arg, seq |-> seq[p_arg], data |-> m_arg]) ||
  seq[p_arg] := seq[p_arg] + 1;
end macro;

fair+ process sender \in {0}
variable q_s = 1;
begin
  Send:
   q_s := 1;
   SenderIT:
     while q_s <= N do
       send(self, q_s, init_message);
       q_s := q_s + 1;
     end while;
     \* deliver(p, m);
     deliver[self] := deliver[self] \union {init_message};
   SenderTerminal:
     skip;
end process;


fair+ process proc \in Procs
variables local = NULL,
          q = 1;
begin 
  ReadWait:
    await queue[self] /= <<>>;
  ReadProcess:
    while queue[self] /= <<>> do
      local := Head(queue[self]);
      queue[self] := Tail(queue[self]);
      Recieve:
        if local.data \notin deliver[self] then
          deliver[self] := deliver[self] \union {local.data} ||
          q := 1;
          SendAfterRec:
            while q <= N do
              if q # self then
                send(self, q, local.data);
              end if;
              q := q + 1;
            end while;
        end if;
     end while;
end process;
 
 
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2153317c" /\ chksum(tla) = "3ba10f73")
VARIABLES procs, all_procs, queue, seq, deliver, init_message, broadcast, pc

(* define statement *)
Neighbors(s_arg) == procs \ {s_arg}

AllDelivered == \A p \in procs: init_message \in deliver[p]
AllDone == \A t \in procs: pc[t] = "Done"
DeliveredAtEnd == <>AllDelivered

Validity == \E p \in Procs: init_message \in broadcast[p] => <>(init_message \in deliver[p])
Agreement == \E p \in Procs: init_message \in deliver[p] => <>(\A y \in Procs: init_message \in deliver[y])
UniformIntegrity == (\E x \in Procs: init_message \in broadcast[x]) ~> (\A y \in Procs: init_message \in deliver[y])

VARIABLES q_s, local, q

vars == << procs, all_procs, queue, seq, deliver, init_message, broadcast, pc, 
           q_s, local, q >>

ProcSet == ({0}) \cup (Procs)

Init == (* Global variables *)
        /\ procs = {i: i \in 1..N}
        /\ all_procs = {i: i \in 0..N}
        /\ queue = [x \in procs |-> <<>>]
        /\ seq = [x \in all_procs |-> 0]
        /\ deliver = [x \in all_procs |-> {}]
        /\ init_message = (CHOOSE x \in Data: TRUE)
        /\ broadcast = [x \in all_procs |-> {}]
        (* Process sender *)
        /\ q_s = [self \in {0} |-> 1]
        (* Process proc *)
        /\ local = [self \in Procs |-> NULL]
        /\ q = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in {0} -> "Send"
                                        [] self \in Procs -> "ReadWait"]

Send(self) == /\ pc[self] = "Send"
              /\ q_s' = [q_s EXCEPT ![self] = 1]
              /\ pc' = [pc EXCEPT ![self] = "SenderIT"]
              /\ UNCHANGED << procs, all_procs, queue, seq, deliver, 
                              init_message, broadcast, local, q >>

SenderIT(self) == /\ pc[self] = "SenderIT"
                  /\ IF q_s[self] <= N
                        THEN /\ /\ broadcast' = [broadcast EXCEPT ![self] = broadcast[self] \union {init_message}]
                                /\ queue' = [queue EXCEPT ![q_s[self]] = Append(queue[q_s[self]], [from |-> self, seq |-> seq[self], data |-> init_message])]
                                /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
                             /\ q_s' = [q_s EXCEPT ![self] = q_s[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "SenderIT"]
                             /\ UNCHANGED deliver
                        ELSE /\ deliver' = [deliver EXCEPT ![self] = deliver[self] \union {init_message}]
                             /\ pc' = [pc EXCEPT ![self] = "SenderTerminal"]
                             /\ UNCHANGED << queue, seq, broadcast, q_s >>
                  /\ UNCHANGED << procs, all_procs, init_message, local, q >>

SenderTerminal(self) == /\ pc[self] = "SenderTerminal"
                        /\ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << procs, all_procs, queue, seq, deliver, 
                                        init_message, broadcast, q_s, local, q >>

sender(self) == Send(self) \/ SenderIT(self) \/ SenderTerminal(self)

ReadWait(self) == /\ pc[self] = "ReadWait"
                  /\ queue[self] /= <<>>
                  /\ pc' = [pc EXCEPT ![self] = "ReadProcess"]
                  /\ UNCHANGED << procs, all_procs, queue, seq, deliver, 
                                  init_message, broadcast, q_s, local, q >>

ReadProcess(self) == /\ pc[self] = "ReadProcess"
                     /\ IF queue[self] /= <<>>
                           THEN /\ local' = [local EXCEPT ![self] = Head(queue[self])]
                                /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                                /\ pc' = [pc EXCEPT ![self] = "Recieve"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << queue, local >>
                     /\ UNCHANGED << procs, all_procs, seq, deliver, 
                                     init_message, broadcast, q_s, q >>

Recieve(self) == /\ pc[self] = "Recieve"
                 /\ IF local[self].data \notin deliver[self]
                       THEN /\ /\ deliver' = [deliver EXCEPT ![self] = deliver[self] \union {local[self].data}]
                               /\ q' = [q EXCEPT ![self] = 1]
                            /\ pc' = [pc EXCEPT ![self] = "SendAfterRec"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "ReadProcess"]
                            /\ UNCHANGED << deliver, q >>
                 /\ UNCHANGED << procs, all_procs, queue, seq, init_message, 
                                 broadcast, q_s, local >>

SendAfterRec(self) == /\ pc[self] = "SendAfterRec"
                      /\ IF q[self] <= N
                            THEN /\ IF q[self] # self
                                       THEN /\ /\ broadcast' = [broadcast EXCEPT ![self] = broadcast[self] \union {(local[self].data)}]
                                               /\ queue' = [queue EXCEPT ![q[self]] = Append(queue[q[self]], [from |-> self, seq |-> seq[self], data |-> (local[self].data)])]
                                               /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << queue, seq, 
                                                            broadcast >>
                                 /\ q' = [q EXCEPT ![self] = q[self] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "SendAfterRec"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ReadProcess"]
                                 /\ UNCHANGED << queue, seq, broadcast, q >>
                      /\ UNCHANGED << procs, all_procs, deliver, init_message, 
                                      q_s, local >>

proc(self) == ReadWait(self) \/ ReadProcess(self) \/ Recieve(self)
                 \/ SendAfterRec(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0}: sender(self))
           \/ (\E self \in Procs: proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0} : SF_vars(sender(self))
        /\ \A self \in Procs : SF_vars(proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Thu Sep 29 23:59:22 EDT 2022 by adamwespiser
\* Created Wed Sep 28 23:14:35 EDT 2022 by adamwespiser
