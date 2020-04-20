
import strformat, strutils, strscans, os, sequtils

# Pointer arithmetic
# https://gist.github.com/oltolm/1738289b5ac866ec6a7e4ef20095178e

template `+`*[T](p: ptr T, off: int): ptr T =
  cast[ptr T](cast[ByteAddress](p) +% off * sizeof(T))
template `+=`*[T](p: var ptr T, off: int) = p = p + off
template `-`*[T](p: ptr T, off: int): ptr T =
  cast[ptr T](cast[ByteAddress](p) -% off * sizeof(T))
template `-=`*[T](p: var ptr T, off: int) = p = p - off
template `-`*[T](p: ptr T, q: ptr T): int =
  (cast[ByteAddress](p) -% cast[ByteAddress](q)) /% sizeof(T)
template `[]`*[T](p: ptr T, off: int): T =
  (p + off)[]
template `[]=`*[T](p: ptr T, off: int, val: T) =
  (p + off)[] = val
template toInt(x: uint): int = cast[int](x)

const END: int32 = -9;
const MARK: int32 = 2;
const IMPLIED: int32 = 6;

type
  Solver* = ref object
    db: ptr int32
    nVars*: int32
    nClauses*: int32
    memUsed*: uint
    memFixed*: uint
    memMax*: uint
    maxLemmas*: uint ## maximum number of learnt clauses
    nLemmas: uint ## The number of learned clauses -- redundant means learned
    buffer: ptr int32 ## A buffer to store a temporary clause
    nConflicts*: uint ## Under of conflicts which is used to updates scores
    model*: seq[bool] ## Full assignment of the (Boolean) variables (init. false)
    reason: seq[int32] ## Array of clauses
    falseStack: ptr int32 ## Stack of falsified literals; this pointer is never changed
    falseVar: ptr int32 ## Labels for variables, non-zero means false
    first: ptr int32 ## Offset of the first watched clause
    forced: ptr int32 ## Points inside *falseStack at first decision (unforced literal)
    processed: ptr int32 ## Points inside *falseStack at first unprocessed literal
    assigned: ptr int32 ## Points inside *falseStack at last unprocessed literal
    next: seq[int32] ## Next variable in the heuristic order
    prev: seq[int32] ## Previous variable in the heuristic order
    head: int32
    res: int32 ## Number of resolutions
    fast: int32 ## moving average
    slow: int32 ## moving average

## Unassign the literal
proc unassign(self: Solver, lit: int32) =
  self.falseVar[lit] = 0

## Perform a restart
proc restart(self: Solver) =
  while self.assigned > self.forced:
    self.assigned -= 1
    self.unassign(self.assigned[])
  self.processed = self.forced

## Assign a literal with the given reason
proc assign(self: var Solver, reason: ptr int32, forced: bool) =
  let lit: int32 = reason[0]; # first literal in the reason
  # mark `lit` as true, and `IMPLIED` if forced
  self.falseVar[-lit] = if forced: IMPLIED else: 1
  self.assigned[] = -lit # push onto assignment stack
  self.assigned += 1
  self.reason[lit.abs] = 1 + cast[int32](reason - self.db) # reason clause for lit
  self.model[lit.abs] = lit>0 # mark literal as true in model

## Add a watch pointer to a clause containing lit
proc addWatch(self: var Solver, lit: int32, mem: int32) =
  self.db[mem] = self.first[lit]
  self.first[lit] = mem

type
  MemoryOverflow* = object of OSError

## Allocate memory of size `mem_size`
proc getMemory(self: var Solver, mem_size: uint): ptr int32
    {. raises: [MemoryOverflow] .}=
  if self.memUsed + mem_size > self.memMax:
    raise newException(MemoryOverflow, "getMemory")
  let store = self.db + cast[int](self.memUsed)
  self.memUsed += mem_size
  store

proc getMemory(self: var Solver, size: int): ptr int32 =
  self.getMemory(cast[uint](size))

proc pC(lits: ptr int32, size: uint): string =
  var s = "(cl"
  for i in 0 ..< size: s.add " "; s.addInt lits[cast[int](i)]
  s.add ")"
  s

## Adds a clause stored in `*lits` of size `size`
proc addClause(self: var Solver, lits: ptr int32, size: uint, irr: bool): ptr int32 =
  echo fmt"addClause {pC(lits, size)} irr={irr}"
  # Store a pointer to the beginning of the clause
  let i = self.memUsed;
  let used = cast[int32](i)
  # Allocate memory for the clause in the database.
  # The clause ends with "0", has `size` literals, and is prefixed
  # by two watchlist pointers.
  var clause: ptr int32 = self.getMemory(size + 3) + 2
  if size > 1:
    # If the clause is not unit, then add two watch pointers to
    # the datastructure
    self.addWatch(lits[0], cast[int32](used))
    self.addWatch(lits[1], used + 1)
  # Copy the clause from the buffer to the database
  for i in 0 ..< size:
    let i = cast[int32](i)
    clause[i] = lits[i]
  clause[cast[int32](size)] = 0
  # Update the statistics
  if irr:
    self.memFixed = self.memUsed;
  else:
    self.nLemmas += 1
  # Return the pointer to the clause in the database
  clause

## Add a clause stored as a slice.
proc addClauseSlice*(self: var Solver, lits: openArray[int32], irr: bool): ptr int32 =
  let p = lits[0].unsafeAddr
  self.addClause(p, cast[uint](lits.len), irr)


## Garbage collect lemmas.
##
## This removes "less useful" lemmas from DB.
proc reduceDB(self: var Solver, k: int) =
  while self.nLemmas > self.maxLemmas:
    self.maxLemmas += 300 # Allow more lemmas in the future
  self.nLemmas = 0 # Reset the number of lemmas

  # Loop over the variables
  block:
    var i = -self.nVars;
    while i <= self.nVars:
      if i == 0:
        i += 1
        continue
      # Get the pointer to the first watched clause
      var watch = self.first + i
      while watch[] != END:
        if cast[uint](watch[]) < self.memFixed:
          # Go to next watch if it's an input clause
          watch = self.db + watch[]
        else:
          # Otherwise, remove the watch if it points to a lemma,
          # we'll re-add it if we re-add the lemma.
          watch[] = self.db[watch[]]

      i += 1;

  # Virtually remove all lemmas (the range `mem_fixed ..< mem_used`) *)
  let oldUsed = self.memUsed
  self.memUsed = self.memFixed;
  ## While the old memory contains lemmas, get the lemma to which
  ## the head is pointing
  var i = self.memFixed + 2
  while i < oldUsed:
    var count = 0 # number of literals satisfied by current model
    let head = i

    # `count` literals satisfied in the current model
    while self.db[i.toInt] != 0:
      let lit = self.db[i.toInt]
      i += 1;
      if (lit > 0) == self.model[cast[uint](lit.abs)]:
        count += 1

    if count < k:
      # If `count` is smaller than k, add it back
      discard self.addClause(self.db + head.toInt, i - head, false)
    i += 3 # jump over trailing 0 and the next clause's header


## Bump the variable as taking part in a conflict.
##
## - move the variable to the front of the decision list
## - `MARK` it if it's not a top-level unit
proc bump(self: var Solver, lit: int32) =
  if self.falseVar[lit] != IMPLIED:
    # MARK the literal as involved if not a top-level unit
    self.falseVar[lit] = MARK;
    let v = cast[int32](lit.abs())
    if v != self.head:
      # In case var is not already the head of the list,
      # update the prev link
      self.prev[self.next[v]] = self.prev[v]
      # update the next link
      self.next[self.prev[v]] = self.next[v]
      # Add a next link to the head
      self.next[self.head] = v
      # Make var the new head
      self.prev[v] = self.head
      self.head = v


## Check if lit(eral) is implied by MARK literals
proc implied(self: var Solver, lit: int32): bool =
  if self.falseVar[lit] > MARK:
    # If checked before, return old result
    return (self.falseVar[lit] and MARK) != 0
  if self.reason[lit.abs()] == 0:
    # In case lit is a decision, it is not implied
    return false
  # Get the reason of lit(eral)
  var p: ptr int32 = self.db + (self.reason[lit.abs()]) - 1

  # Iterate over literals in the reason
  while (p += 1; p[] != 0):
    # Recursively check if non-MARK literals are implied
    if (self.falseVar[p[]] xor MARK) != 0 and not self.implied(p[]):
      # Mark and return not implied (denoted by IMPLIED - 1)
      self.falseVar[lit] = IMPLIED - 1
      return false

  # Mark and return that the literal is implied
  self.falseVar[lit] = IMPLIED
  true


## Compute a resolvent from falsified clause
proc analyze(self: var Solver, clause: var ptr int32): ptr int32 =
  # Bump restarts and update the statistic
  self.res += 1
  self.nConflicts += 1

  # MARK all literals in the falsified clause
  while clause[] != 0:
    self.bump(clause[])
    clause += 1

  # Loop on variables on `false_stack` until the last decision,
  # as all resolution steps are done at current (conflict) level.
  block ext:
    while (
      block:
        self.assigned -= 1;
        self.reason[self.assigned[].abs] != 0
      ):
      # If the tail of the stack is MARK
      if self.falseVar[self.assigned[]] == MARK:
        # Pointer to check if first-UIP is reached
        var check = self.assigned
        # Check for a MARK literal before decision
        while (check -= 1; self.falseVar[check[]] != MARK):
          if self.reason[check[].abs] == 0:
            # Otherwise it is the first-UIP so break
            break ext

        # Get the reason and ignore first literal
        clause = self.db + self.reason[self.assigned[].abs]
        # MARK all literals in reason
        while clause[] != 0:
          self.bump(clause[])
          clause += 1

      # Unassign the tail of the stack
      self.unassign(self.assigned[])

  # Build conflict clause; Empty the clause buffer
  var size = 0
  var lbd: int32 = 0
  var flag: int32 = 0

  # Loop from tail to front; only literals on the stack can be MARKed
  self.processed = self.assigned
  var p = self.assigned;
  while p >= self.forced:
    if self.falseVar[p[]] == MARK and not self.implied(p[]):
      # If MARKed and not implied, add literal to conflict clause buffer
      self.buffer[size] = p[]
      size += 1
      flag = 1
    if self.reason[p[].abs] == 0:
      # Increase LBD for a decision with a true flag
      lbd += flag
      flag = 0
      if size == 1:
        # update the processed pointer
        self.processed = p
    # Reset the MARK flag for all variables on the stack
    self.falseVar[p[]] = 1
    p -= 1

    # Update the fast moving average
    self.fast -= self.fast shr 5
    self.fast += lbd shl 15
    # Update the slow moving average
    self.slow -= self.slow shr 15
    self.slow += lbd shl 5

    # Loop over all unprocessed literals to unassign them.
    while self.assigned > self.processed:
      self.unassign(self.assigned[])
      self.assigned -= 1
    # Assigned now equal to processed
    self.unassign(self.assigned[])
    # TODO: DRAT output here
    # Terminate the buffer (and potentially print clause)
    self.buffer[size] = 0
    # Add new conflict clause to redundant DB
    return self.addClause(self.buffer, cast[uint](size), false)


## Performs unit propagation
proc propagate(self: var Solver): bool =
  # TODO: use a boolean…
  # Initialize forced flag
  var forced = self.reason[self.processed[].abs]

  # Loop while there are unprocessed false literals
  while self.processed < self.assigned:
    # Get first unprocessed literal
    let lit = self.processed[]
    self.processed += 1
    # Obtain the first watch pointer
    var watch = self.first + lit

    # Loop while there are clauses watched by lit
    while watch[] != END:
      # Let's assume that the clause is unit
      var unit = true
      # Get the clause from DB
      var clause: ptr int32 = self.db + watch[] + 1;

      # TODO: explain this part ‽
      # Set the pointer to the first literal in the clause
      if clause[-2] == 0:
        clause += 1
      # Ensure that the other watched literal is in front
      if clause[0] == lit:
        clause[0] = clause[1]

      # Scan the non-watched literals
      var i = 2
      while unit and clause[i] != 0:
        if self.falseVar[clause[i]] == 0:
          # When `clause[i]` is not false, it is either true or
          # unset, so we just have to use `clause[i]` as new watch.

          # Swap literals
          clause[1] = clause[i]
          clause[i] = lit

          # Store the old watch
          let store = watch[]
          # Stop the loop after this iteration
          unit = false
          # Remove the watch from the watchlist of `lit`
          watch[] = self.db[watch[]]
          # Add the watch to the list of `clause[1]`
          self.addWatch(clause[1], store)
        i += 1

      if unit:
        # If the clause is indeed unit,
        # place lit at `clause[1]` and update next watch
        clause[1] = lit
        watch = self.db + watch[]

        if self.falseVar[-clause[0]] != 0:
          # If the other watched literal is satisfied, continue
          continue
        elif self.falseVar[clause[0]] == 0:
          # If the other watched literal is falsified,
          # a unit clause is found, and the reason is set
          self.assign(clause, forced != 0)
        elif forced != 0:
          return false # Found a root level conflict -> UNSAT
        else:
          # Analyze the conflict, to return a conflict clause
          let lemma = self.analyze(clause);
          if lemma[1] == 0:
            # In case a unit clause is found, set `forced` flag
            forced = 1
          # Assign the conflict clause as a unit
          self.assign(lemma, forced != 0)
          break

  if forced != 0:
    # Set S->forced if applicable
    self.forced = self.processed
  true

## Determine satisfiability.
##
## Returns `true` if the set of clauses is SAT, `false` if UNSAT.
proc solve*(self: var Solver): bool =
  var decision = self.head
  self.res = 0

  # main solve loop
  while true:
    # Store n_lemmas to see whether propagate adds lemmas
    let oldNLemmas = self.nLemmas
    if not self.propagate():
      # Propagation returns UNSAT for a root level conflict
      return false

    if self.nLemmas > oldNLemmas:
      # If the last decision caused a conflict
      decision = self.head

      if self.fast > (self.slow /% 100) * 125:
        # If fast average is substantially larger than slow average
        debugEcho fmt"c restarting after {self.res} conflicts ({self.fast} {self.slow})"

        # Restart and update the averages
        self.res = 0;
        self.fast = (self.slow /% 100) * 125;
        self.restart();

        if self.nLemmas > self.maxLemmas:
          # Reduce the DB when it contains too many lemmas
          self.reduceDB(6)

    # As long as the temporay decision is assigned,
    # replace it with the next variable in the decision list
    while self.falseVar[decision] != 0 or self.falseVar[-decision] != 0:
      decision = self.prev[decision]

    if decision == 0:
      # If the end of the list is reached, then a solution is found
      return true
    else:
      # Otherwise, assign the decision variable based
      # on the model (phase saving)
      decision = if self.model[decision]: decision else: -decision
      # Assign the decision literal to true,
      # and push it on the assigned stack
      self.falseVar[-decision] = 1
      self.assigned[] = -decision
      self.assigned += 1
      # Set the reason to 0 (no clause)
      decision = decision.abs
      self.reason[decision] = 0


## Create a new solver
proc newSolver*(nVars: int32, nClauses: int32): Solver =
  new(result)
  let n = max(1, nVars) # assume at least one var
  result.nVars = n
  result.memMax = 1 shl 30
  result.db = cast[ptr int32](alloc(result.memMax))
  result.nClauses = nClauses
  result.memUsed = 0
  result.memFixed = 0
  result.res = 0
  result.nLemmas = 0
  result.nConflicts = 0
  result.maxLemmas = 2000
  result.fast = 1 shl 24
  result.slow = 1 shl 24
  result.model = newSeqWith(n+1, false)
  result.next = newSeqWith(n+1, 0i32)
  result.prev = newSeqWith(n+1, 0i32)
  result.buffer = result.getMemory(n)
  result.reason = newSeqWith(n+1, 0i32)
  result.falseStack = result.getMemory(n+1)
  result.forced = result.falseStack
  result.processed = result.falseStack
  result.assigned = result.falseStack
  result.falseVar = result.getMemory(2*n+1) + n
  result.first = result.getMemory(2*n+1) + n
  result.head = result.nVars
  # Make sure there is a 0 before the clauses are loaded.
  result.db[result.memUsed.toInt] = 0
  result.memUsed += 1

  # Initialize the main datastructures:
  for i in 1 .. n:
    # the double-linked list for variable-move-to-front
    result.prev[i] = i - 1
    result.next[i - 1] = i
    # the false array
    result.falseVar[-i] = 0
    result.falseVar[i] = 0
    #// first (watch pointers).
    result.first[i] = END
    result.first[-i] = END
    # Initialize the head of the double-linked list
    result.head = nVars

proc deleteSolver*(self: var Solver) =
  dealloc(self.db)

# iterate over non-comment, non empty lines
iterator nonCommentLines(f: File): string {.closure.}=
  for x in f.lines:
    let x = x.strip
    if x != "" and not x.startsWith("c"):
      yield x

## Parse the formula and initialize the solver. Returns SAT or UNSAT as well.
proc parse*(filename: string): tuple[s: Solver, sat: bool] =
  # Read the CNF file
  var file: File
  if not open(file, filename, mode=fmRead):
    raise newException(IOError, fmt"could not open file '{filename}'")

  var nVars: int = -1
  var nClauses: int = -1
  var solver: Solver = nil
  var lits: seq[int32] = @[]

  for s in file.nonCommentLines:
    if s.startsWith('p'):
      if not scanf(s, "p cnf $i $i", nVars, nClauses):
        raise newException(IOError, fmt"bad problem description line: {s}")
      echo fmt"c problem has {nVars} vars, {nClauses} clauses"
      solver = newSolver(cast[int32](nVars), cast[int32](nClauses))
    else:
      if nVars < 0 or nClauses < 0 or solver.isNil:
        raise newException(IOError, fmt"not bad problem description line: {s}")
      # parse clauses from the rest of the lines
      lits.setLen(0)
      for w in s.strip().splitWhitespace:
        let n =
          try: cast[int32](w.parseInt)
          except:
            raise newException(IOError, fmt"expected an integer, got {w}")
        if n == 0: break
        else: lits.add n
      # add clause to the database
      debugEcho "c parsed clause ", lits
      let clause = solver.addClauseSlice(lits.toOpenArray(0, lits.len-1), true)
      if lits.len == 0 or (lits.len == 1 and solver.falseVar[lits[0]] != 0):
        # Check for empty clause or conflicting unit, in which case UNSAT
        return (solver, false)
      elif lits.len == 1 and solver.falseVar[-lits[0]] == 0:
        # Check for a new unit and assign it directly as forced
        solver.assign(clause, true)
  (solver, true)

when isMainModule:
  let args = os.commandLineParams()
  if args.len < 1:
    echo "usage: microsat <file>"
    raiseOSError((-1).OSErrorCode)
  let filename = args[0]
  var (s, status) = parse(filename)
  if not status:
    echo "s UNSATISFIABLE"
  elif not s.solve:
    echo "s UNSATISFIABLE"
  else:
    echo "s SATISFIABLE"

  debugEcho (
    fmt"""c statistics of {filename}: conflicts: {s.nConflicts} \
    max_lemmas: {s.maxLemmas}""")
