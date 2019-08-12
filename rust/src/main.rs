use std::{io, marker::PhantomData, u32, usize, vec::Vec};

#[derive(Debug, Clone, Copy)]
pub enum R {
    Sat,
    Unsat,
}

/// Boolean variable
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Var(u32);

/// Boolean literal
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Lit(u32);

/// Normalize literal from a signed integer (e.g. from dimacs).
fn norm_lit(i: i32) -> usize {
    (i.abs() as usize) << 1 | ((i > 0) as usize)
}

trait AsIdx: Copy {
    fn as_idx(&self) -> usize;
}

impl AsIdx for Var {
    #[inline]
    fn as_idx(&self) -> usize {
        self.0 as usize
    }
}

impl AsIdx for Lit {
    #[inline]
    fn as_idx(&self) -> usize {
        self.0 as usize
    }
}

struct IVec<A: AsIdx, B>(Vec<B>, PhantomData<A>);

impl<A: AsIdx, B: Clone> IVec<A, B> {
    pub fn new() -> Self {
        Self(vec![], PhantomData)
    }

    pub fn with_capacity(i: usize) -> Self {
        Self(Vec::with_capacity(i), PhantomData)
    }

    pub fn resize(&mut self, n: usize, elt: B) {
        self.0.resize(n, elt)
    }
}

impl<A: AsIdx, B> std::ops::Index<A> for IVec<A, B> {
    type Output = B;
    fn index(&self, i: A) -> &B {
        &self.0[i.as_idx()]
    }
}

impl<A: AsIdx, B> std::ops::IndexMut<A> for IVec<A, B> {
    fn index_mut(&mut self, i: A) -> &mut B {
        &mut self.0[i.as_idx()]
    }
}

impl Lit {
    const SENTINEL: Self = Lit(u32::MAX);
    #[inline]
    pub fn new(v: Var, sign: bool) -> Self {
        Lit(v.0 << 1 | (sign as u32))
    }
    #[inline]
    pub fn from_i32(i: i32) -> Self {
        Lit(norm_lit(i) as u32)
    }
    #[inline]
    pub fn sign(self) -> bool {
        (self.0 & 1) != 0
    }
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }
}

impl Var {
    const SENTINEL: Self = Var(u32::MAX);
}

impl Into<i32> for Lit {
    fn into(self) -> i32 {
        self.var().0 as i32 * if self.sign() { 1 } else { -1 }
    }
}

type ClauseIdx = usize;
const CLAUSE_END: ClauseIdx = usize::MAX;

pub struct Solver {
    n_vars: usize,
    n_clauses: usize,
    max_lemmas: usize,
    clauses: Vec<Lit>, // storage for clauses
    buffer: Vec<Lit>,  // A buffer to store a temporary clause
    n_lemmas: usize,
    n_conflicts: usize,
    model: IVec<Var, bool>, // Full assignment of the variables (initially set to false)
    reason: IVec<Var, usize>, // Array of clauses
    false_: IVec<Lit, i32>, // lit assignment (non-zero means false)
    false_stack: Vec<Lit>,  // Stack of falsified literals (trail)
    forced: usize,          // offset in false_stack at first decision
    processed: usize,       // offset in false_stack at first unprocessed lit
    assigned: usize,        // offset in false_stack at last unprocessed lit
    first: IVec<Lit, ClauseIdx>, // watch pointer
    next: IVec<Var, Var>,   // Next variable in the heuristic order
    prev: IVec<Var, Var>,   // Previous variable in the heuristic order
    head: usize,
    n_restarts: usize,
    fast: usize,
    slow: usize,
}

impl Solver {
    fn new() -> Self {
        Solver {
            n_vars: 0,
            n_clauses: 0,
            max_lemmas: 2000,
            clauses: Vec::with_capacity(2000),
            n_lemmas: 0,
            n_conflicts: 0,
            n_restarts: 0,
            fast: 1 << 24,
            slow: 1 << 24,
            false_: IVec::new(),
            false_stack: vec![],
            assigned: 0,
            forced: 0,
            processed: 0,
            model: IVec::new(),
            reason: IVec::new(),
            next: IVec::new(),
            prev: IVec::new(),
            first: IVec::new(),
            buffer: vec![],
            head: 0,
        }
    }

    fn ensure(&mut self, n_vars: usize, n_clauses: usize) {
        let old_n = self.n_vars;
        self.n_vars = usize::max(self.n_vars, n_vars);
        self.n_clauses = usize::max(self.n_clauses, n_clauses);
        self.false_.resize(n_vars * 2, 0);
        self.false_stack.resize(n_vars, Lit::SENTINEL);
        self.first.resize(n_vars * 2, CLAUSE_END);
        self.model.resize(n_vars, false);
        self.next.resize(n_vars, Var::SENTINEL);
        self.prev.resize(n_vars, Var::SENTINEL);

        // initialize main data structure for the new variables
        for i in old_n + 1..=self.n_vars {
            let v = Var(i as u32);
            self.prev[v] = Var(i as u32 - 1);
            self.next[Var(i as u32 - 1)] = v; // TODO: what if list already modified?
            self.false_[Lit::new(v, true)] = 0;
            self.false_[Lit::new(v, false)] = 0;
            // initialize watch list
            self.first[Lit::new(v, true)] = CLAUSE_END;
            self.first[Lit::new(v, false)] = CLAUSE_END;
        }
        // FIXME: what if we've searched already?
        self.head = self.n_vars; // head of double linked list
    }

    #[inline]
    fn unassign(&mut self, lit: Lit) {
        self.false_[lit] = 0
    }

    fn restart(&mut self) {
        while self.assigned > self.forced {
            let lit = self.false_stack[self.assigned];
            self.assigned -= 1;
            self.unassign(lit);
        }
    }

    /// Add `self.buffer` to the list of clauses.
    fn add_clause(&mut self, n: usize, lemma: bool) {
        self.clauses.reserve(n + 2);
        // TODO: push clause
        if lemma {
            self.n_lemmas += 1
        }
    }

    // TODO: resize by creating a new solver and copying into it

    fn solve(&mut self) -> R {
        println!("solve with {} vars, {} clauses", self.n_vars, self.n_clauses);
        unimplemented!()
    }
}

type Res<T> = Result<T, Box<dyn std::error::Error>>;

fn parse(solver: &mut Solver, filename: &str) -> Res<()> {
    use io::BufRead;
    let mut lines = io::BufReader::new(std::fs::File::open(filename)?)
        .lines()
        .filter(|l| match l {
            // remove 'c' lines and empty lines
            Ok(l) => l.len() > 0 && l.as_bytes()[0] != b'c',
            Err(_) => true,
        });
    // get header
    let (n, m) = {
        let head = lines.next().transpose()?;
        let head = head.expect("expected header line");
        let head = head.split_whitespace().collect::<Vec<_>>();
        if head.len() == 4 && head[0] == "p" && head[1] == "cnf" {
            let n: usize = head[2].parse()?;
            let m: usize = head[3].parse()?;
            (n, m)
        } else {
            return Err("expected `p cnf <n> <m>`".into());
        }
    };
    solver.ensure(n, m);
    for line in lines {
        let mut size = 0;
        let line = line?;
        for c in line.trim().split_whitespace() {
            let i = str::parse::<i32>(c).expect("expected integer");
            if i == 0 {
                solver.add_clause(size, false);
            } else {
                solver.buffer[size] = Lit::from_i32(i);
                size += 1;
            }
        }
    }
    Ok(())
}

fn main() -> Res<()> {
    let mut s = Solver::new();
    parse(&mut s, "foo.cnf")?;
    let r = s.solve();
    match r {
        R::Sat => println!("s SATISFIABLE"),
        R::Unsat => println!("s UNSATISFIABLE"),
    }
    Ok(())
}
