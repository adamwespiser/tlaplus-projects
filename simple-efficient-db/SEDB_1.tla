------------------------------- MODULE SEDB_1 -------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS N, KEYS, NULL

ASSUME N \in Nat \ {0}
ASSUME N > 0

ASSUME KEYS \in Nat \{0}
ASSUME KEYS > 0


(*--algorithm simple_db

variables
  \* processes for database writers
  procs = {i: i \in 0..N},
  keys = 0..KEYS,
  \* three tiered locking strategy
  shared_lock = [i \in procs|-> FALSE],
  update_lock = [i \in procs |-> FALSE],
  exclusive_lock = [i \in procs |-> FALSE],
  \* our state
  wal = <<>>,
  version = 0,
  memory = [m \in keys |-> 0],
  file_system = [k \in procs |-> memory],
  tick = 0;

define
  \* defines the set of operations
  Keys == 0..KEYS
  UpdateSet == {"inc", "dec"}
  WriteOps == [op: {"write"}, key: Keys, value: 1..3]
  UpdateOps == [op: {"update"}, key: Keys, value: {"inc", "dec"}]
  ReadOps == [op: {"read"}, key: Keys, value: {"none"}]
  Ops ==  ReadOps \union UpdateOps \union WriteOps
  LockEmpty(lock) == \A x \in DOMAIN lock: ~lock[x]
  SelfHasLock(lock, s) == \A x \in DOMAIN lock: ~lock[x] /\ (x = s)
end define;


macro write_to_wal(cmd) begin
  wal := Append(wal, cmd);
end macro;

macro eval_cmd_in_mem(cmd) begin
   if cmd.op = "update" /\ cmd.key \in DOMAIN memory then
     if cmd.value = "dec" then
        memory[cmd.key] := memory[cmd.key] - 1;
     elsif cmd.value = "inc" then
        memory[cmd.key] := memory[cmd.key] + 1;
     end if;
   elsif cmd.op = "write" then
       memory[cmd.key] := cmd.value;
   end if;
end macro;

macro flush_to_disk() begin
    version := version + 1 ||
    file_system[version] := memory ||
    wal := <<>>;
end macro;

macro rebuild_from_disk() begin
  memory := file_system[version];
  while Len(wal) > 0 do
    replay_message := Head(wal) ||
    wal := Tail(wal);
    eval_cmd_in_mem(replay_message);
  end while;
end macro;


fair+ process db_process \in 0..N
variables current_cmd = "";
begin
  GetCommand:
    with c \in Ops do
        current_cmd := c;
    end with;        
    if current_cmd.op = "read" then
        Read:
            await LockEmpty(exclusive_lock);
            shared_lock[self] := TRUE;
    else
        UpdateLock:
            await LockEmpty(update_lock) /\ LockEmpty(exclusive_lock);
            update_lock[self] := TRUE;
        WriteMemory:
            tick := tick + 1;
            eval_cmd_in_mem(current_cmd);
        WriteFS:
            tick := tick +1;
            write_to_wal(current_cmd);
 \*       ExclusiveLock:
 \*           await LockEmpty(shared_lock) /\ SelfHasLock(update_lock, self) /\ LockEmpty(exclusive_lock);
 \*           exclusive_lock[self] := TRUE;
        ExecuteFlush:
            flush_to_disk();
    end if;
    DropLocks:
       shared_lock[self] := FALSE ||
       update_lock[self] := FALSE ||
       exclusive_lock[self] := FALSE;
end process;




end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9e2069dd" /\ chksum(tla) = "5e7ec91f")
VARIABLES procs, keys, shared_lock, update_lock, exclusive_lock, wal, version, 
          memory, file_system, tick, pc

(* define statement *)
Keys == 0..KEYS
UpdateSet == {"inc", "dec"}
WriteOps == [op: {"write"}, key: Keys, value: 1..3]
UpdateOps == [op: {"update"}, key: Keys, value: {"inc", "dec"}]
ReadOps == [op: {"read"}, key: Keys, value: {"none"}]
Ops ==  ReadOps \union UpdateOps \union WriteOps
LockEmpty(lock) == \A x \in DOMAIN lock: ~lock[x]
SelfHasLock(lock, s) == \A x \in DOMAIN lock: ~lock[x] /\ (x = s)

VARIABLE current_cmd

vars == << procs, keys, shared_lock, update_lock, exclusive_lock, wal, 
           version, memory, file_system, tick, pc, current_cmd >>

ProcSet == (0..N)

Init == (* Global variables *)
        /\ procs = {i: i \in 0..N}
        /\ keys = 0..KEYS
        /\ shared_lock = [i \in procs|-> FALSE]
        /\ update_lock = [i \in procs |-> FALSE]
        /\ exclusive_lock = [i \in procs |-> FALSE]
        /\ wal = <<>>
        /\ version = 0
        /\ memory = [m \in keys |-> 0]
        /\ file_system = [k \in procs |-> memory]
        /\ tick = 0
        (* Process db_process *)
        /\ current_cmd = [self \in 0..N |-> ""]
        /\ pc = [self \in ProcSet |-> "GetCommand"]

GetCommand(self) == /\ pc[self] = "GetCommand"
                    /\ \E c \in Ops:
                         current_cmd' = [current_cmd EXCEPT ![self] = c]
                    /\ IF current_cmd'[self].op = "read"
                          THEN /\ pc' = [pc EXCEPT ![self] = "Read"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateLock"]
                    /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                    exclusive_lock, wal, version, memory, 
                                    file_system, tick >>

Read(self) == /\ pc[self] = "Read"
              /\ LockEmpty(exclusive_lock)
              /\ shared_lock' = [shared_lock EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "DropLocks"]
              /\ UNCHANGED << procs, keys, update_lock, exclusive_lock, wal, 
                              version, memory, file_system, tick, current_cmd >>

UpdateLock(self) == /\ pc[self] = "UpdateLock"
                    /\ LockEmpty(update_lock) /\ LockEmpty(exclusive_lock)
                    /\ update_lock' = [update_lock EXCEPT ![self] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "WriteMemory"]
                    /\ UNCHANGED << procs, keys, shared_lock, exclusive_lock, 
                                    wal, version, memory, file_system, tick, 
                                    current_cmd >>

WriteMemory(self) == /\ pc[self] = "WriteMemory"
                     /\ tick' = tick + 1
                     /\ IF current_cmd[self].op = "update" /\ current_cmd[self].key \in DOMAIN memory
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
                     /\ pc' = [pc EXCEPT ![self] = "WriteFS"]
                     /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                     exclusive_lock, wal, version, file_system, 
                                     current_cmd >>

WriteFS(self) == /\ pc[self] = "WriteFS"
                 /\ tick' = tick +1
                 /\ wal' = Append(wal, current_cmd[self])
                 /\ pc' = [pc EXCEPT ![self] = "ExecuteFlush"]
                 /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                 exclusive_lock, version, memory, file_system, 
                                 current_cmd >>

ExecuteFlush(self) == /\ pc[self] = "ExecuteFlush"
                      /\ /\ file_system' = [file_system EXCEPT ![version] = memory]
                         /\ version' = version + 1
                         /\ wal' = <<>>
                      /\ pc' = [pc EXCEPT ![self] = "DropLocks"]
                      /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                      exclusive_lock, memory, tick, 
                                      current_cmd >>

DropLocks(self) == /\ pc[self] = "DropLocks"
                   /\ /\ exclusive_lock' = [exclusive_lock EXCEPT ![self] = FALSE]
                      /\ shared_lock' = [shared_lock EXCEPT ![self] = FALSE]
                      /\ update_lock' = [update_lock EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << procs, keys, wal, version, memory, 
                                   file_system, tick, current_cmd >>

db_process(self) == GetCommand(self) \/ Read(self) \/ UpdateLock(self)
                       \/ WriteMemory(self) \/ WriteFS(self)
                       \/ ExecuteFlush(self) \/ DropLocks(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N: db_process(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..N : SF_vars(db_process(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Jan 06 00:29:25 EST 2023 by adamwespiser
\* Created Sat Dec 24 14:05:49 EST 2022 by adamwespiser
