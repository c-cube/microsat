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
    unsafe fn add_clause(&mut self, lits: *mut i32, size: usize, irr: bool) -> *mut i32 {
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
            return *self.false_.offset(lit as isize) & MARK != 0
        }
        if *self.reason.offset(lit.abs() as isize) == 0 {
            // In case lit is a decision, it is not implied
            return false;
        }
        // Get the reason of lit(eral)
        let p = self.db.offset((*self.reason.offset(lit.abs() as isize) - 1) as isize);

        // TODO

        int* p = (S->DB + S->reason[abs (lit)] - 1);             
        while (*(++p))                                           // While there are literals in the reason
            if ((S->false[*p] ^ MARK) && !implied (S, *p)) {       // Recursively check if non-MARK literals are implied
                S->false[lit] = IMPLIED - 1; return 0; }             // Mark and return not implied (denoted by IMPLIED - 1)
        // Mark and return that the literal is implied
        S->false[lit] = IMPLIED;
        return 1;
    }
}
