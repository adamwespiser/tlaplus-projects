------------------------------- MODULE SEDB_1 -------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS N, KEYS

ASSUME N \in Nat \ {0}
ASSUME N > 1

ASSUME KEYS \in Nat \{0}
ASSUME KEYS > 1


(*--algorithm simple_db

variables
  \* processes for database writers
  procs = {i: i \in 1..N},
  \* three tiered locking strategy
  shared_lock = [t \in N |-> FALSE],
  update_lock = [t \in N |-> FALSE],
  exclusive_lock = [t \in N |-> FALSE],
  \* our state
  wal = <<>>,
  version = 0,
  memory = {},
  file_system = [version |-> {}],
  tick = 0;

define
  \* defines the set of operations
  Keys == 1..KEYS
  UpdateSet == {"inc", "dec"}
  WriteOps == [op: {"write"}, key: Keys, value: 1..6]
  UpdateOps == [op: {"update"}, key: Keys, value: {"inc", "dec"}]
  ReadOps == [op: {"read"}, key: Keys, value: {"none"}]
  Ops ==  ReadOps \union UpdateOps \union WriteOps
  LockEmpty(lock) == \A x \in lock: ~lock[x]
end define;


macro write_to_wal(cmd) begin
  wal := Append(wal, cmd);
end macro;

macro eval_cmd_in_mem(cmd) begin
   if cmd.op = "update" /\ cmd.key \in memory then
     if cmd.value = "dec" then
        memory[cmd.key] := memory[cmd.key] - 1;
     elsif cmd.value = "inc" then
        memory[cmd.key] := memory[cmd.key] + 1;
     end if;
   elsif cmd.op = "write" then
       memory[cmd.key] := cmd.value;
   end if;
end macro;

process db_process \in Keys
variables current_cmd = "";
begin
  GetCommand:
    with c \in Ops do
        current_cmd := c;
    end with;        
    if current_cmd.op = "read" then
        Read:
            shared_lock[self] := TRUE;
    else 
        UpdateLock:
            await LockEmpty(update_lock) /\ LockEmpty(exclusive_lock);
            update_lock[self] := TRUE;
        Write:
            tick := tick + 1;
            eval_cmd_in_mem(current_cmd);
            write_to_wal(current_cmd);
    end if;
    DropLocks:
       shared_lock[self] := FALSE;
       update_lock[self] := FALSE;
end process;




end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "63c8c623" /\ chksum(tla) = "a34a7caa")
VARIABLES procs, shared_lock, update_lock, exclusive_lock, wal, version, 
          memory, file_system, tick, pc

(* define statement *)
Keys == 1..KEYS
UpdateSet == {"inc", "dec"}
WriteOps == [op: {"write"}, key: Keys, value: 1..6]
UpdateOps == [op: {"update"}, key: Keys, value: {"inc", "dec"}]
ReadOps == [op: {"read"}, key: Keys, value: {"none"}]
Ops ==  ReadOps \union UpdateOps \union WriteOps
LockEmpty(lock) == \A x \in lock: ~lock[x]

VARIABLE current_cmd

vars == << procs, shared_lock, update_lock, exclusive_lock, wal, version, 
           memory, file_system, tick, pc, current_cmd >>

ProcSet == (Keys)

Init == (* Global variables *)
        /\ procs = {i: i \in 1..N}
        /\ shared_lock = [t \in N |-> FALSE]
        /\ update_lock = [t \in N |-> FALSE]
        /\ exclusive_lock = [t \in N |-> FALSE]
        /\ wal = <<>>
        /\ version = 0
        /\ memory = {}
        /\ file_system = [version |-> {}]
        /\ tick = 0
        (* Process db_process *)
        /\ current_cmd = [self \in Keys |-> ""]
        /\ pc = [self \in ProcSet |-> "GetCommand"]

GetCommand(self) == /\ pc[self] = "GetCommand"
                    /\ \E c \in Ops:
                         current_cmd' = [current_cmd EXCEPT ![self] = c]
                    /\ IF current_cmd'[self].op = "read"
                          THEN /\ pc' = [pc EXCEPT ![self] = "Read"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateLock"]
                    /\ UNCHANGED << procs, shared_lock, update_lock, 
                                    exclusive_lock, wal, version, memory, 
                                    file_system, tick >>

Read(self) == /\ pc[self] = "Read"
              /\ shared_lock' = [shared_lock EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "DropLocks"]
              /\ UNCHANGED << procs, update_lock, exclusive_lock, wal, version, 
                              memory, file_system, tick, current_cmd >>

UpdateLock(self) == /\ pc[self] = "UpdateLock"
                    /\ LockEmpty(update_lock) /\ LockEmpty(exclusive_lock)
                    /\ update_lock' = [update_lock EXCEPT ![self] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "Write"]
                    /\ UNCHANGED << procs, shared_lock, exclusive_lock, wal, 
                                    version, memory, file_system, tick, 
                                    current_cmd >>

Write(self) == /\ pc[self] = "Write"
               /\ tick' = tick + 1
               /\ IF current_cmd[self].op = "update" /\ current_cmd[self].key \in memory
                     THEN /\ IF current_cmd[self].value = "dec"
                                THEN /\ memory' = [memory EXCEPT ![current_cmd[self].key] = memory[current_cmd[self].key] - 1]
                                ELSE /\ IF current_cmd[self].value = "inc"
                                           THEN /\ memory' = [memory EXCEPT ![current_cmd[self].key] = memory[current_cmd[self].key] + 1]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED memory
                     ELSE /\ IF current_cmd[self].op = "write"
                                THEN /\ memory' = [memory EXCEPT ![current_cmd[self].key] = current_cmd[self].value]
                                ELSE /\ TRUE
                                     /\ UNCHANGED memory
               /\ wal' = Append(wal, current_cmd[self])
               /\ pc' = [pc EXCEPT ![self] = "DropLocks"]
               /\ UNCHANGED << procs, shared_lock, update_lock, exclusive_lock, 
                               version, file_system, current_cmd >>

DropLocks(self) == /\ pc[self] = "DropLocks"
                   /\ shared_lock' = [shared_lock EXCEPT ![self] = FALSE]
                   /\ update_lock' = [update_lock EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << procs, exclusive_lock, wal, version, memory, 
                                   file_system, tick, current_cmd >>

db_process(self) == GetCommand(self) \/ Read(self) \/ UpdateLock(self)
                       \/ Write(self) \/ DropLocks(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Keys: db_process(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jan 01 01:32:57 EST 2023 by adamwespiser
\* Created Sat Dec 24 14:05:49 EST 2022 by adamwespiser
