const END: i32 = -9;
const UNSAT: i32 = 0;
const SAT: i32 = 1;
const MARK: i32 = 2;
const IMPLIED: i32 = 6;

// The variables in the struct are described in the allocate procedure
struct Solver {
    db: *mut i32,
    n_vars: i32,
    n_clauses: i32,
    mem_used: usize,
    mem_fixed: usize,
    mem_max: usize,
    max_lemmas: usize,
    n_lemmas: usize,
    buffer: *mut i32,
    n_conflicts: usize,
    model: *mut i32,
    reason: *mut i32,
    false_stack: *mut i32,
    false_: *mut i32,
    first: *mut i32,
    forced: *mut i32,
    processed: *mut i32,
    assigned: *mut i32,
    next: *mut i32,
    prev: *mut i32,
    head: i32,
    res: i32,
    fast: i32,
    slow: i32,
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
    fn add_clause_slice(&mut self, lits: &[i32], irr: bool) {
        unsafe {
            let ptr = lits.as_ptr();
            self.add_clause(ptr, lits.len(), irr);
        }
    }

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

    fn solve(&mut self) -> bool {
        unimplemented!("solve")
    }
    /*

    int solve (struct solver* S) {                                      // Determine satisfiability
      int decision = S->head; S->res = 0;                               // Initialize the solver
      for (;;) {                                                        // Main solve loop
        int old_nLemmas = S->nLemmas;                                   // Store nLemmas to see whether propagate adds lemmas
        if (propagate (S) == UNSAT) return UNSAT;                       // Propagation returns UNSAT for a root level conflict

        if (S->nLemmas > old_nLemmas) {                                 // If the last decision caused a conflict
          decision = S->head;                                           // Reset the decision heuristic to head
          if (S->fast > (S->slow / 100) * 125) {                        // If fast average is substantially larger than slow average
    //        printf("c restarting after %i conflicts (%i %i) %i\n", S->res, S->fast, S->slow, S->nLemmas > S->maxLemmas);
            S->res = 0; S->fast = (S->slow / 100) * 125; restart (S);   // Restart and update the averages
            if (S->nLemmas > S->maxLemmas) reduceDB (S, 6); } }         // Reduce the DB when it contains too many lemmas

        while (S->false[decision] || S->false[-decision]) {             // As long as the temporay decision is assigned
          decision = S->prev[decision]; }                               // Replace it with the next variable in the decision list
        if (decision == 0) return SAT;                                  // If the end of the list is reached, then a solution is found
        decision = S->model[decision] ? decision : -decision;           // Otherwise, assign the decision variable based on the model
        S->false[-decision] = 1;                                        // Assign the decision literal to true (change to IMPLIED-1?)
        *(S->assigned++) = -decision;                                   // And push it on the assigned stack
        decision = abs(decision); S->reason[decision] = 0; } }          // Decisions have no reason clauses
    */

    fn new(n_vars: i32, n_clauses: i32) -> Self {
        unimplemented!(); // TODO
    }

    /*
    void initCDCL (struct solver* S, int n, int m) {
      if (n < 1)      n = 1;                  // The code assumes that there is at least one variable
      S->nVars          = n;                  // Set the number of variables
      S->nClauses       = m;                  // Set the number of clauases
      S->mem_max        = 1 << 30;            // Set the initial maximum memory
      S->mem_used       = 0;                  // The number of integers allocated in the DB
      S->nLemmas        = 0;                  // The number of learned clauses -- redundant means learned
      S->nConflicts     = 0;                  // Under of conflicts which is used to updates scores
      S->maxLemmas      = 2000;               // Initial maximum number of learnt clauses
      S->fast = S->slow = 1 << 24;            // Initialize the fast and slow moving averages

      S->DB = (int *) malloc (sizeof (int) * S->mem_max); // Allocate the initial database
      S->model       = getMemory (S, n+1); // Full assignment of the (Boolean) variables (initially set to false)
      S->next        = getMemory (S, n+1); // Next variable in the heuristic order
      S->prev        = getMemory (S, n+1); // Previous variable in the heuristic order
      S->buffer      = getMemory (S, n  ); // A buffer to store a temporary clause
      S->reason      = getMemory (S, n+1); // Array of clauses
      S->falseStack  = getMemory (S, n+1); // Stack of falsified literals -- this pointer is never changed
      S->forced      = S->falseStack;      // Points inside *falseStack at first decision (unforced literal)
      S->processed   = S->falseStack;      // Points inside *falseStack at first unprocessed literal
      S->assigned    = S->falseStack;      // Points inside *falseStack at last unprocessed literal
      S->false       = getMemory (S, 2*n+1); S->false += n; // Labels for variables, non-zero means false
      S->first       = getMemory (S, 2*n+1); S->first += n; // Offset of the first watched clause
      S->DB[S->mem_used++] = 0;            // Make sure there is a 0 before the clauses are loaded.

      int i; for (i = 1; i <= n; i++) {                        // Initialize the main datastructes:
        S->prev [i] = i - 1; S->next[i-1] = i;                 // the double-linked list for variable-move-to-front,
        S->model[i] = S->false[-i] = S->false[i] = 0;          // the model (phase-saving), the false array,
        S->first[i] = S->first[-i] = END; }                    // and first (watch pointers).
      S->head = n; }                                           // Initialize the head of the double-linked list
            */
}

/// Parse the formula and initialize the solver. Returns SAT or UNSAT as well.
fn parse(filename: &str) -> (Solver, bool) {
    use std::{fs::File, io, io::BufRead};
    // Read the CNF file
    let file = File::open(filename).expect("cannot open file");
    let mut reader = io::BufReader::new(file);
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
        println!("parsed clause {:?}", &lits);
        solver.add_clause_slice(&lits, true); // Add the clause to the database

        // TODO: check for empty clause or conflicting unit, and return UNSAT if that's the case
    }
    drop(lits);

    /* TODO
    initCDCL (S, S->nVars, S->nClauses);                     // Allocate the main datastructures
    int nZeros = S->nClauses, size = 0;                      // Initialize the number of clauses to read
    while (nZeros > 0) {                                     // While there are clauses in the file
      int lit = 0; tmp = fscanf (input, " %i ", &lit);       // Read a literal.
      if (!lit) {                                            // If reaching the end of the clause
        int* clause = addClause (S, S->buffer, size, 1);     // Then add the clause to data_base
        if (!size || ((size == 1) && S->false[clause[0]]))   // Check for empty clause or conflicting unit
          return UNSAT;                                      // If either is found return UNSAT
        if ((size == 1) && !S->false[-clause[0]]) {          // Check for a new unit
          assign (S, clause, 1); }                           // Directly assign new units (forced = 1)
        size = 0; --nZeros; }                                // Reset buffer
      else S->buffer[size++] = lit; }                        // Add literal to buffer
    fclose (input);                                          // Close the formula file
    return SAT; }                                            // Return that no conflict was observed
      */
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

    /* TODO
    if      (parse (&S, argv[1]) == UNSAT) printf("s UNSATISFIABLE\n");  // Parse the DIMACS file in argv[1]
    else if (solve (&S)          == UNSAT) printf("s UNSATISFIABLE\n");  // Solve without limit (number of conflicts)
    else                                   printf("s SATISFIABLE\n")  ;  // And print whether the formula has a solution
    printf ("c statistics of %s: mem: %i conflicts: %i max_lemmas: %i\n", argv[1], S.mem_used, S.nConflicts, S.maxLemmas); }
      */
}
