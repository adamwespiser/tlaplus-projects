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
end define;


macro write_to_wal(cmd) begin
  wal := Append(wal, cmd);
end macro;

macro eval_cmd_in_mem(cmd, ret="") begin
   if cmd.op = "read" then
    
   end if;
end macro;


end algorithm; *)
=============================================================================
\* Modification History
\* Last modified Sat Dec 24 19:49:46 EST 2022 by adamwespiser
\* Created Sat Dec 24 14:05:49 EST 2022 by adamwespiser


