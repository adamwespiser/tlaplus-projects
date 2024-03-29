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
  eternal_memory = [m \in keys |-> 0],
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
  SelfHasLock(lock, s) == \A x \in DOMAIN lock: (x /= s /\ ~lock[x]) \/ (x = s /\ lock[x])

  \* temporal invariant
  AlwaysConsistency == \E k \in Keys: k \in memory /\ [](memory[k] = eternal_memory[k])
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
    replay_message := Head(wal);
    wal := Tail(wal);
    eval_cmd_in_mem(replay_message);
  end while;
end macro;


fair+ process memory_wipe \in {"wipe"}
variables replay_message = "";
begin
  MemoryProces:
    either
     PowerOffThenOn:
       \*rebuild_from_disk();
       memory := file_system[version];
       ReplayOnStartUp:
         while Len(wal) > 0 do
            replay_message := Head(wal);
            wal := Tail(wal);
            eval_cmd_in_mem(replay_message);
         end while;
     or
       skip;
    end either;
end process;

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
            \* tick := tick + 1;
            eval_cmd_in_mem(current_cmd);
        WriteFS:
            \* tick := tick +1;
            write_to_wal(current_cmd);
        \* "no steal & force" style
        ExclusiveLock:
            await LockEmpty(shared_lock) /\ SelfHasLock(update_lock, self) /\ LockEmpty(exclusive_lock);
            exclusive_lock[self] := TRUE;
        ExecuteFlush:
            flush_to_disk();
    end if;
    DropLocks:
       shared_lock[self] := FALSE ||
       update_lock[self] := FALSE ||
       exclusive_lock[self] := FALSE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3c3a4ccd" /\ chksum(tla) = "28e327f7")
VARIABLES procs, keys, shared_lock, update_lock, exclusive_lock, wal, version, 
          memory, eternal_memory, file_system, tick, pc

(* define statement *)
Keys == 0..KEYS
UpdateSet == {"inc", "dec"}
WriteOps == [op: {"write"}, key: Keys, value: 1..3]
UpdateOps == [op: {"update"}, key: Keys, value: {"inc", "dec"}]
ReadOps == [op: {"read"}, key: Keys, value: {"none"}]
Ops ==  ReadOps \union UpdateOps \union WriteOps
LockEmpty(lock) == \A x \in DOMAIN lock: ~lock[x]
SelfHasLock(lock, s) == \A x \in DOMAIN lock: (x /= s /\ ~lock[x]) \/ (x = s /\ lock[x])


AlwaysConsistency == \E k \in Keys: k \in memory /\ [](memory[k] = eternal_memory[k])

VARIABLES replay_message, current_cmd

vars == << procs, keys, shared_lock, update_lock, exclusive_lock, wal, 
           version, memory, eternal_memory, file_system, tick, pc, 
           replay_message, current_cmd >>

ProcSet == ({"wipe"}) \cup (0..N)

Init == (* Global variables *)
        /\ procs = {i: i \in 0..N}
        /\ keys = 0..KEYS
        /\ shared_lock = [i \in procs|-> FALSE]
        /\ update_lock = [i \in procs |-> FALSE]
        /\ exclusive_lock = [i \in procs |-> FALSE]
        /\ wal = <<>>
        /\ version = 0
        /\ memory = [m \in keys |-> 0]
        /\ eternal_memory = [m \in keys |-> 0]
        /\ file_system = [k \in procs |-> memory]
        /\ tick = 0
        (* Process memory_wipe *)
        /\ replay_message = [self \in {"wipe"} |-> ""]
        (* Process db_process *)
        /\ current_cmd = [self \in 0..N |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self \in {"wipe"} -> "MemoryProces"
                                        [] self \in 0..N -> "GetCommand"]

MemoryProces(self) == /\ pc[self] = "MemoryProces"
                      /\ \/ /\ pc' = [pc EXCEPT ![self] = "PowerOffThenOn"]
                         \/ /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                      exclusive_lock, wal, version, memory, 
                                      eternal_memory, file_system, tick, 
                                      replay_message, current_cmd >>

PowerOffThenOn(self) == /\ pc[self] = "PowerOffThenOn"
                        /\ memory' = file_system[version]
                        /\ pc' = [pc EXCEPT ![self] = "ReplayOnStartUp"]
                        /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                        exclusive_lock, wal, version, 
                                        eternal_memory, file_system, tick, 
                                        replay_message, current_cmd >>

ReplayOnStartUp(self) == /\ pc[self] = "ReplayOnStartUp"
                         /\ IF Len(wal) > 0
                               THEN /\ replay_message' = [replay_message EXCEPT ![self] = Head(wal)]
                                    /\ wal' = Tail(wal)
                                    /\ IF replay_message'[self].op = "update" /\ replay_message'[self].key \in DOMAIN memory
                                          THEN /\ IF replay_message'[self].value = "dec"
                                                     THEN /\ memory' = [memory EXCEPT ![replay_message'[self].key] = memory[replay_message'[self].key] - 1]
                                                     ELSE /\ IF replay_message'[self].value = "inc"
                                                                THEN /\ memory' = [memory EXCEPT ![replay_message'[self].key] = memory[replay_message'[self].key] + 1]
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED memory
                                          ELSE /\ IF replay_message'[self].op = "write"
                                                     THEN /\ memory' = [memory EXCEPT ![replay_message'[self].key] = replay_message'[self].value]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED memory
                                    /\ pc' = [pc EXCEPT ![self] = "ReplayOnStartUp"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << wal, memory, 
                                                    replay_message >>
                         /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                         exclusive_lock, version, 
                                         eternal_memory, file_system, tick, 
                                         current_cmd >>

memory_wipe(self) == MemoryProces(self) \/ PowerOffThenOn(self)
                        \/ ReplayOnStartUp(self)

GetCommand(self) == /\ pc[self] = "GetCommand"
                    /\ \E c \in Ops:
                         current_cmd' = [current_cmd EXCEPT ![self] = c]
                    /\ IF current_cmd'[self].op = "read"
                          THEN /\ pc' = [pc EXCEPT ![self] = "Read"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateLock"]
                    /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                    exclusive_lock, wal, version, memory, 
                                    eternal_memory, file_system, tick, 
                                    replay_message >>

Read(self) == /\ pc[self] = "Read"
              /\ LockEmpty(exclusive_lock)
              /\ shared_lock' = [shared_lock EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "DropLocks"]
              /\ UNCHANGED << procs, keys, update_lock, exclusive_lock, wal, 
                              version, memory, eternal_memory, file_system, 
                              tick, replay_message, current_cmd >>

UpdateLock(self) == /\ pc[self] = "UpdateLock"
                    /\ LockEmpty(update_lock) /\ LockEmpty(exclusive_lock)
                    /\ update_lock' = [update_lock EXCEPT ![self] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "WriteMemory"]
                    /\ UNCHANGED << procs, keys, shared_lock, exclusive_lock, 
                                    wal, version, memory, eternal_memory, 
                                    file_system, tick, replay_message, 
                                    current_cmd >>

WriteMemory(self) == /\ pc[self] = "WriteMemory"
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
                                     exclusive_lock, wal, version, 
                                     eternal_memory, file_system, tick, 
                                     replay_message, current_cmd >>

WriteFS(self) == /\ pc[self] = "WriteFS"
                 /\ wal' = Append(wal, current_cmd[self])
                 /\ pc' = [pc EXCEPT ![self] = "ExclusiveLock"]
                 /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                 exclusive_lock, version, memory, 
                                 eternal_memory, file_system, tick, 
                                 replay_message, current_cmd >>

ExclusiveLock(self) == /\ pc[self] = "ExclusiveLock"
                       /\ LockEmpty(shared_lock) /\ SelfHasLock(update_lock, self) /\ LockEmpty(exclusive_lock)
                       /\ exclusive_lock' = [exclusive_lock EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "ExecuteFlush"]
                       /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                       wal, version, memory, eternal_memory, 
                                       file_system, tick, replay_message, 
                                       current_cmd >>

ExecuteFlush(self) == /\ pc[self] = "ExecuteFlush"
                      /\ /\ file_system' = [file_system EXCEPT ![version] = memory]
                         /\ version' = version + 1
                         /\ wal' = <<>>
                      /\ pc' = [pc EXCEPT ![self] = "DropLocks"]
                      /\ UNCHANGED << procs, keys, shared_lock, update_lock, 
                                      exclusive_lock, memory, eternal_memory, 
                                      tick, replay_message, current_cmd >>

DropLocks(self) == /\ pc[self] = "DropLocks"
                   /\ /\ exclusive_lock' = [exclusive_lock EXCEPT ![self] = FALSE]
                      /\ shared_lock' = [shared_lock EXCEPT ![self] = FALSE]
                      /\ update_lock' = [update_lock EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << procs, keys, wal, version, memory, 
                                   eternal_memory, file_system, tick, 
                                   replay_message, current_cmd >>

db_process(self) == GetCommand(self) \/ Read(self) \/ UpdateLock(self)
                       \/ WriteMemory(self) \/ WriteFS(self)
                       \/ ExclusiveLock(self) \/ ExecuteFlush(self)
                       \/ DropLocks(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"wipe"}: memory_wipe(self))
           \/ (\E self \in 0..N: db_process(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {"wipe"} : SF_vars(memory_wipe(self))
        /\ \A self \in 0..N : SF_vars(db_process(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sat Jan 28 23:33:19 EST 2023 by adamwespiser
\* Created Sat Dec 24 14:05:49 EST 2022 by adamwespiser
