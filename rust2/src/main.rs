use std::ptr;

const END: i32 = -9;
const MARK: i32 = 2;
const IMPLIED: i32 = 6;

// The variables in the struct are described in the allocate procedure
struct Solver {
    db: *mut i32,
    n_vars: i32,
    n_clauses: i32,
    mem_used: usize, // The number of integers allocated in the DB
    mem_fixed: usize,
    mem_max: usize,
    max_lemmas: usize,     // maximum number of learnt clauses
    n_lemmas: usize,       // The number of learned clauses -- redundant means learned
    buffer: *mut i32,      // A buffer to store a temporary clause
    n_conflicts: usize,    // Under of conflicts which is used to updates scores
    model: *mut i32,       // Full assignment of the (Boolean) variables (initially set to false)
    reason: *mut i32,      // Array of clauses
    false_stack: *mut i32, // Stack of falsified literals -- this pointer is never changed
    false_: *mut i32,      // Labels for variables, non-zero means false
    first: *mut i32,       // Offset of the first watched clause
    forced: *mut i32,      // Points inside *falseStack at first decision (unforced literal)
    processed: *mut i32,   // Points inside *falseStack at first unprocessed literal
    assigned: *mut i32,    // Points inside *falseStack at last unprocessed literal
    next: *mut i32,        // Next variable in the heuristic order
    prev: *mut i32,        // Previous variable in the heuristic order
    head: i32,
    res: i32,  // Number of resolutions
    fast: i32, // moving average
    slow: i32, // moving average
}

impl Solver {
    /// Unassign the literal
    unsafe fn unassign(&mut self, lit: i32) {
        *self.false_.offset(lit as isize) = 0
    }

    /// Unassign the literal
    unsafe fn restart(&mut self) {
        // Remove all unforced false lits from falseStack
        while self.assigned > self.forced {
            self.assigned = self.assigned.offset(-1);
            self.unassign(*self.assigned);
        }
        self.processed = self.forced;
    }

    /// Make the first literal of the reason true
    unsafe fn assign(&mut self, reason: *const i32, forced: bool) {
        // let `lit` be the first literal in the reason
        let lit = *reason;
        // Mark lit as true and `IMPLIED` if forced
        *self.false_.offset(-lit as isize) = if forced { IMPLIED } else { 1 };
        // push it on the assignment stack
        *self.assigned = -lit;
        self.assigned = self.assigned.offset(1);
        // Set the reason clause of lit
        *self.reason.offset(lit.abs() as isize) = 1 + (reason as usize - self.db as usize) as i32;
        // Mark the literal as true in the model
        *self.model.offset(lit.abs() as isize) = (lit > 0) as i32;
    }

    /// Add a watch pointer to a clause containing lit
    unsafe fn add_watch(&mut self, lit: i32, mem: i32) {
        // By updating the database and the pointers
        *self.db.offset(mem as isize) = *self.first.offset(lit as isize);
        *self.first.offset(lit as isize) = mem;
    }

    /// Allocate memory of size mem_size
    unsafe fn get_memory(&mut self, mem_size: usize) -> *mut i32 {
        if self.mem_used + mem_size > self.mem_max {
            // in case the code is used within a code base
            panic!("c out of memory");
        }
        // Compute a pointer to the new memory location
        let store = self.db.add(self.mem_used);
        self.mem_used += mem_size; // Update the size of the used memory
        store
    }

    /// Adds a clause stored in `*lits` of size `size`
    unsafe fn add_clause(&mut self, lits: *const i32, size: usize, irr: bool) -> *mut i32 {
        // Store a pointer to the beginning of the clause
        let i = self.mem_used;
        let used = i as i32;
        // Allocate memory for the clause in the database
        let clause = self.get_memory(size + 3).offset(2);
        if size > 1 {
            // If the clause is not unit, then add two watch pointers to
            // the datastructure
            self.add_watch(*lits, used as i32);
            self.add_watch(*lits.offset(1), used + 1);
        }
        // Copy the clause from the buffer to the database
        for i in 0..size {
            *clause.add(i) = *lits.add(i)
        }
        *clause.add(size) = 0;
        // Update the statistics
        if irr {
            self.mem_fixed = self.mem_used;
        } else {
            self.n_lemmas += 1
        }
        // Return the pointer to the clause in the database
        clause
    }

    /// Add a clause stored as a slice.
    pub fn add_clause_slice(&mut self, lits: &[i32], irr: bool) -> *mut i32 {
        unsafe {
            let ptr = lits.as_ptr();
            self.add_clause(ptr, lits.len(), irr)
        }
    }

    /// Garbage collect lemmas.
    unsafe fn reduce_db(&mut self, k: usize) {
        // Removes "less useful" lemmas from DB
        while self.n_lemmas > self.max_lemmas {
            self.max_lemmas += 300; // Allow more lemmas in the future
        }
        self.n_lemmas = 0; // Reset the number of lemmas

        // Loop over the variables
        let mut i = -self.n_vars;
        while i <= self.n_vars {
            if i == 0 {
                continue;
            }
            // Get the pointer to the first watched clause
            let mut watch = self.first.offset(i as isize);
            while *watch != END {
                if (*watch as usize) < self.mem_fixed {
                    // Remove the watch if it points to a lemma
                    watch = self.db.offset(*watch as isize);
                } else {
                    // Otherwise (meaning an input clause) go to next watch
                    *watch = *self.db.offset(*watch as isize);
                }
            }

            i += 1;
        }

        // Virtually remove all lemmas
        let old_used = self.mem_used;
        self.mem_used = self.mem_fixed;
        // While the old memory contains lemmas
        let mut i = self.mem_fixed + 2;
        while i < old_used {
            // Get the lemma to which the head is pointing
            let mut count = 0;
            let head = i;

            // Count the number of literals that are satisfied by the current model
            while *self.db.add(i) != 0 {
                let lit = *self.db.add(i);
                i += 1;
                if (lit > 0) == (*self.model.offset(lit.abs() as isize) != 0) {
                    count += 1;
                }
            }

            if count < k {
                // If the latter is smaller than k, add it back
                self.add_clause(self.db.add(head), i - head, false);
            }
            i += 3; // next iteration
        }
    }

    // Move the variable to the front of the decision list
    unsafe fn bump(&mut self, lit: i32) {
        if *self.false_.offset(lit as isize) != IMPLIED {
            // MARK the literal as involved if not a top-level unit
            *self.false_.offset(lit as isize) = MARK;
            let var = lit.abs() as isize;
            if var != self.head as isize {
                // In case var is not already the head of the list,
                // Update the prev link
                *self.prev.offset(*self.next.offset(var) as isize) = *self.prev.offset(var);
                // Update the next link
                *self.next.offset(*self.prev.offset(var) as isize) = *self.next.offset(var);
                // Add a next link to the head
                *self.next.offset(self.head as isize) = var as i32;
                // Make var the new head
                *self.prev.offset(var) = self.head;
                self.head = var as i32;
            }
        }
    }

    // Check if lit(eral) is implied by MARK literals
    unsafe fn implied(&mut self, lit: i32) -> bool {
        if *self.false_.offset(lit as isize) > MARK {
            // If checked before, return old result
            return *self.false_.offset(lit as isize) & MARK != 0;
        }
        if *self.reason.offset(lit.abs() as isize) == 0 {
            // In case lit is a decision, it is not implied
            return false;
        }
        // Get the reason of lit(eral)
        let mut p = self
            .db
            .offset(*self.reason.offset(lit.abs() as isize) as isize);

        // Iterate over literals in the reason
        loop {
            if *p == 0 {
                break;
            }

            // Recursively check if non-MARK literals are implied
            if (*self.false_.offset(*p as isize)) & IMPLIED != 0 && !self.implied(*p) {
                // Mark and return not implied (denoted by IMPLIED - 1)
                *self.false_.offset(lit as isize) = IMPLIED - 1;
                return false;
            }

            p = p.add(1);
        }

        // Mark and return that the literal is implied
        *self.false_.offset(lit as isize) = IMPLIED;
        true
    }

    /// Compute a resolvent from falsified clause
    unsafe fn analyze(&mut self, _clause: *mut i32) -> *mut i32 {
        unimplemented!("analyze"); // TODO
    }
    /* TODO
        int* analyze (struct solver* S, int* clause) {         // Compute a resolvent from falsified clause
          S->res++; S->nConflicts++;                           // Bump restarts and update the statistic
          while (*clause) bump (S, *(clause++));               // MARK all literals in the falsified clause
          while (S->reason[abs (*(--S->assigned))]) {          // Loop on variables on falseStack until the last decision
            if (S->false[*S->assigned] == MARK) {              // If the tail of the stack is MARK
              int *check = S->assigned;                        // Pointer to check if first-UIP is reached
              while (S->false[*(--check)] != MARK)             // Check for a MARK literal before decision
                if (!S->reason[abs(*check)]) goto build;       // Otherwise it is the first-UIP so break
              clause = S->DB + S->reason[abs (*S->assigned)];  // Get the reason and ignore first literal
              while (*clause) bump (S, *(clause++)); }         // MARK all literals in reason
            unassign (S, *S->assigned); }                      // Unassign the tail of the stack

          build:; int size = 0, lbd = 0, flag = 0;             // Build conflict clause; Empty the clause buffer
          int* p = S->processed = S->assigned;                 // Loop from tail to front
          while (p >= S->forced) {                             // Only literals on the stack can be MARKed
            if ((S->false[*p] == MARK) && !implied (S, *p)) {  // If MARKed and not implied
              S->buffer[size++] = *p; flag = 1; }              // Add literal to conflict clause buffer
            if (!S->reason[abs (*p)]) { lbd += flag; flag = 0; // Increase LBD for a decision with a true flag
              if (size == 1) S->processed = p; }               // And update the processed pointer
            S->false[*(p--)] = 1; }                            // Reset the MARK flag for all variables on the stack

          S->fast -= S->fast >>  5; S->fast += lbd << 15;      // Update the fast moving average
          S->slow -= S->slow >> 15; S->slow += lbd <<  5;      // Update the slow moving average

          while (S->assigned > S->processed)                   // Loop over all unprocessed literals
            unassign (S, *(S->assigned--));                    // Unassign all lits between tail & head
          unassign (S, *S->assigned);                          // Assigned now equal to processed
          S->buffer[size] = 0;                                 // Terminate the buffer (and potentially print clause)
          return addClause (S, S->buffer, size, 0); }          // Add new conflict clause to redundant DB
    */

    /// Performs unit propagation
    unsafe fn propagate(&mut self) -> bool {
        // TODO: use a boolean…
        // Initialize forced flag
        let mut forced = *self.reason.offset(*self.processed as isize);

        // Loop while there are unprocessed false literals
        while self.processed < self.assigned {
            // Get first unprocessed literal
            let lit = *self.processed;
            self.processed = self.processed.add(1);
            // Obtain the first watch pointer
            let mut watch = self.first.offset(lit as isize);

            // Loop while there are clauses watched by lit
            while (*watch != END) {
                // Let's assume that the clause is unit
                let mut unit = true;
                // Get the clause from DB
                let mut clause = self.db.offset(*watch as isize + 1);

                // TODO: explain this part ‽
                // Set the pointer to the first literal in the clause
                if *clause.offset(-2) == 0 {
                    clause = clause.offset(1);
                }
                // Ensure that the other watched literal is in front
                if *clause == lit {
                    *clause = *clause.offset(1);
                }

                // Scan the non-watched literals
                let mut i = 2;
                while unit && *clause.offset(i) != 0 {
                    let lit_i = *clause.offset(i);
                    if *self.false_.offset(lit_i as isize) == 0 {
                        // When `clause[i]` is not false, it is either true or
                        // unset, so we just have to use `clause[i]` as new watch.

                        // Swap literals
                        *clause.offset(1) = lit_i;
                        *clause.offset(i) = lit;

                        // Store the old watch
                        let store = *watch;
                        // Stop the loop after this iteration
                        unit = false;
                        // Remove the watch from the watchlist of `lit`
                        *watch = *self.db.offset(*watch as isize);
                        // Add the watch to the list of `clause[1]`
                        self.add_watch(lit_i, store);
                    }

                    i += 1;
                }

                if unit {
                    // If the clause is indeed unit, place lit at clause[1] and update next watch
                    *clause.offset(1) = lit;
                    watch = self.db.offset(*watch as isize);

                    if *self.false_.offset(-*clause as isize) != 0 {
                        // If the other watched literal is satisfied, continue
                        continue;
                    } else if *self.false_.offset(*clause as isize) == 0 {
                        // If the other watched literal is falsified, a unit clause is found, and
                        // the reason is set
                        self.assign(clause, forced != 0);
                    } else if forced != 0 {
                        return false; // Found a root level conflict -> UNSAT
                    } else {
                        // Analyze the conflict, to return a conflict clause
                        let lemma = self.analyze(clause);
                        if *lemma.offset(1) == 0 {
                            // In case a unit clause is found, set `forced` flag
                            forced = 1;
                        }
                        // Assign the conflict clause as a unit
                        self.assign(lemma, forced != 0);
                        break;
                    }
                }
            }
        }
        if forced != 0 {
            // Set S->forced if applicable
            self.forced = self.processed;
        }
        true
    }

    unsafe fn solve_(&mut self) -> bool {
        let mut decision = self.head;
        self.res = 0;

        // main solve loop
        loop {
            // Store n_lemmas to see whether propagate adds lemmas
            let old_n_lemmas = self.n_lemmas;
            if !self.propagate() {
                // Propagation returns UNSAT for a root level conflict
                return false;
            }

            if self.n_lemmas > old_n_lemmas {
                // If the last decision caused a conflict
                decision = self.head;

                if self.fast > (self.slow / 100) * 125 {
                    // If fast average is substantially larger than slow average
                    println!(
                        "c restarting after {} conflicts ({} {}) {}",
                        self.res,
                        self.fast,
                        self.slow,
                        self.n_lemmas > self.max_lemmas
                    );

                    // Restart and update the averages
                    self.res = 0;
                    self.fast = (self.slow / 100) * 125;
                    self.restart();
                }

                if self.n_lemmas > self.max_lemmas {
                    // Reduce the DB when it contains too many lemmas
                    self.reduce_db(6);
                }
            }

            // As long as the temporay decision is assigned,
            // replace it with the next variable in the decision list
            while *self.false_.offset(decision as isize) != 0
                || *self.false_.offset(-decision as isize) != 0
            {
                decision = *self.prev.offset(decision as isize);
            }

            if decision == 0 {
                // If the end of the list is reached, then a solution is found
                return true;
            } else {
                // Otherwise, assign the decision variable based on the model (phase saving)
                decision = if *self.model.offset(decision as isize) != 0 {
                    decision
                } else {
                    -decision
                };
                // Assign the decision literal to true, and push it on the assigned stack
                *self.false_.offset(-decision as isize) = 1;
                *self.assigned = -decision;
                self.assigned = self.assigned.add(1);
                // Set the reason to 0
                decision = decision.abs();
                *self.reason.offset(decision as isize) = 0;
            }
        }
    }

    /// Determine satisfiability.
    ///
    /// Returns `true` if the set of clauses is SAT, `false` if UNSAT.
    pub fn solve(&mut self) -> bool {
        unsafe { self.solve_() }
    }

    unsafe fn new_(n_vars: i32, n_clauses: i32) -> Self {
        let n_vars = i32::max(1, n_vars); // The code assumes that there is at least one variable
        let mem_max = 1 << 30;
        let db = {
            let mut v = Vec::with_capacity(mem_max);
            let ptr = v.as_mut_ptr();
            std::mem::forget(v);
            ptr
        };

        let mut s = Solver {
            db,
            n_vars,
            n_clauses,
            mem_max,
            mem_used: 0,
            mem_fixed: 0,
            res: 0,
            n_lemmas: 0,
            n_conflicts: 0,
            max_lemmas: 2000,
            fast: 1 << 24,
            slow: 1 << 24,
            model: ptr::null_mut(),
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
            buffer: ptr::null_mut(),
            reason: ptr::null_mut(),
            false_stack: ptr::null_mut(),
            forced: ptr::null_mut(),
            processed: ptr::null_mut(),
            assigned: ptr::null_mut(),
            false_: ptr::null_mut(),
            first: ptr::null_mut(),
            head: n_vars,
        };
        let n = n_vars as usize;
        s.model = s.get_memory(n + 1);
        s.next = s.get_memory(n + 1);
        s.prev = s.get_memory(n + 1);
        s.buffer = s.get_memory(n);
        s.reason = s.get_memory(n + 1);
        s.false_stack = s.get_memory(n + 1);
        s.forced = s.false_stack;
        s.processed = s.false_stack;
        s.assigned = s.false_stack;
        s.false_ = s.get_memory(2 * n + 1).add(n);
        s.first = s.get_memory(2 * n + 1).add(n);
        // Make sure there is a 0 before the clauses are loaded.
        *s.db.add(s.mem_used) = 0;
        s.mem_used += 1;

        // Initialize the main datastructures:
        for i in 1..=n {
            // the double-linked list for variable-move-to-front
            *s.prev.add(i) = i as i32 - 1;
            *s.next.add(i - 1) = i as i32;
            // the model (phase-saving), the false array
            *s.model.add(i) = 0;
            *s.false_.sub(i) = 0;
            *s.false_.add(i) = 0;
            // first (watch pointers).
            *s.first.add(i) = END;
            *s.first.sub(i) = END;
        }
        // Initialize the head of the double-linked list
        s.head = n_vars;
        s
    }

    pub fn new(n_vars: i32, n_clauses: i32) -> Self {
        unsafe { Self::new_(n_vars, n_clauses) }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe {
            let v = Vec::from_raw_parts(self.db, self.mem_max, self.mem_max);
            drop(v)
        }
    }
}

/// Parse the formula and initialize the solver. Returns SAT or UNSAT as well.
fn parse(filename: &str) -> (Solver, bool) {
    use std::{fs::File, io, io::BufRead};
    // Read the CNF file
    let file = File::open(filename).expect("cannot open file");
    let reader = io::BufReader::new(file);
    // iterate over non-comment, non empty lines
    let mut iter = reader.lines().map(|x| x.unwrap()).filter(|line| {
        let x = line.trim();
        x != "" && !x.starts_with('c')
    });
    // find header line
    let (n_vars, n_clauses) = if let Some(s) = iter.next() {
        if s.starts_with('p') {
            let chunks: Vec<_> = s.trim().split_ascii_whitespace().collect();
            if chunks.len() != 4 || chunks[0] != "p" || chunks[1] != "cnf" {
                panic!("expected `p cnf <n> <n>` line, got {:?}", s);
            }
            let n_vars: i32 = chunks[2].parse().expect("expected int for number of vars");
            let n_clauses: i32 = chunks[3]
                .parse()
                .expect("expected int for number of clauses");
            (n_vars, n_clauses)
        } else {
            panic!("expected `p cnf` line, not {:?}", s);
        }
    } else {
        panic!("did not find the `p cnf` line");
    };
    let mut solver = Solver::new(n_vars, n_clauses);
    println!("c problem has {} vars, {} clauses", n_vars, n_clauses);
    let mut lits = Vec::with_capacity(n_vars as usize);
    // parse clauses from the rest of the lines
    for line in iter {
        lits.clear();
        for w in line.trim().split_ascii_whitespace() {
            match w.parse::<i32>() {
                Ok(0) => break,
                Ok(n) => lits.push(n),
                Err(s) => panic!("expected integer, got {:?}", s),
            }
        }
        //println!("parsed clause {:?}", &lits);
        let clause = solver.add_clause_slice(&lits, true); // Add the clause to the database

        unsafe {
            if lits.len() == 0 || (lits.len() == 1 && *solver.false_.offset(lits[0] as isize) != 0)
            {
                // Check for empty clause or conflicting unit, in which case UNSAT
                return (solver, false);
            } else if lits.len() == 1 && *solver.false_.offset(-lits[0] as isize) == 0 {
                // Check for a new unit and assign it directly as forced
                solver.assign(clause, true);
            }
        }
    }
    drop(lits);
    (solver, true)
}

// The main procedure for a STANDALONE solver
fn main() {
    let filename = std::env::args()
        .skip(1)
        .next()
        .expect("usage: microsat <file>");
    let (mut s, status) = parse(&filename);
    if !status {
        println!("s UNSATISFIABLE");
    } else if !s.solve() {
        println!("s UNSATISFIABLE");
    } else {
        println!("s SATISFIABLE");
    }

    println!(
        "c statistics of {}: mem: {} conflicts: {} max_lemmas: {}",
        filename, s.mem_used, s.n_conflicts, s.max_lemmas
    );
}
