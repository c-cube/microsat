use std::{alloc, io, marker::PhantomData, ptr, vec::Vec};

enum R {
    Sat,
    Unsat,
}

#[repr(i32)]
enum Tags {
    End = -9,
    Mark = 2,
    Implied = 6,
}

/// A raw pointer with indexing, for all the delicious unsafety of C
#[derive(Copy, Clone)]
struct RawPtr<'a, T: Copy>(*mut T, PhantomData<&'a T>);

impl<'a, T: Copy> RawPtr<'a, T> {
    #[inline]
    fn copy(&mut self, src: &Self, n: usize) {
        unsafe { ptr::copy(src.0, self.0, n) }
    }
}

impl<'a, T: Copy> std::ops::Index<i32> for RawPtr<'a, T> {
    type Output = T;
    #[inline]
    fn index(&self, i: i32) -> &Self::Output {
        unsafe { &*self.0.offset(i as isize) }
    }
}

impl<'a, T: Copy> std::ops::Add<i32> for RawPtr<'a, T> {
    type Output = RawPtr<'a, T>;
    #[inline]
    fn add(self, i: i32) -> Self::Output {
        self.0 = self.0.offset(i as isize);
        self
    }
}

impl<'a, T: Copy> std::ops::IndexMut<i32> for RawPtr<'a, T> {
    #[inline]
    fn index_mut(&mut self, i: i32) -> &mut Self::Output {
        unsafe { &mut *self.0.offset(i as isize) }
    }
}

struct DB<'a> {
    data: *mut i32,
    mem_max: usize,
    mem_used: usize,
    phantom: PhantomData<&'a ()>,
}

impl<'a> DB<'a> {
    fn new(mem_max: usize) -> Self {
        let data = unsafe {
            alloc::realloc(
                ptr::null_mut(),
                alloc::Layout::new::<i32>(),
                mem_max,
            ) as *mut i32
        };
        Self { mem_max, mem_used: 0, data, phantom: PhantomData }
    }

    fn get_memory(&mut self, mem_size: usize) -> RawPtr<'a, i32> {
        if self.mem_used + mem_size > self.mem_max {
            panic!("c out of memory");
        }
        let store = self.data.offset(self.mem_used as isize);
        self.mem_used += mem_size;
        RawPtr(store, PhantomData)
    }
}

pub struct Solver<'a> {
    db: DB<'a>, // memory arena
    n_vars: usize,
    n_clauses: usize,
    max_lemmas: usize,
    buffer: RawPtr<'a, i32>,
    n_lemmas: usize,
    n_conflicts: usize,
    model: RawPtr<'a, i32>,
    reason: RawPtr<'a, i32>,
    false_: RawPtr<'a, i32>,      // lit assignment
    false_stack: RawPtr<'a, i32>, // Stack of falsified literals — constant ptr
    assigned: RawPtr<'a, i32>,    // offset in false_stack
    forced: RawPtr<'a, i32>,      // offset in false_stack
    processed: RawPtr<'a, i32>,   // offset in false_stack
    first: RawPtr<'a, i32>,
    next: RawPtr<'a, i32>,
    prev: RawPtr<'a, i32>,
    head: usize,
    n_restarts: usize,
    fast: usize,
    slow: usize,
}

impl<'a> Solver<'a> {
    fn new(n_vars: usize, n_clauses: usize) -> Self {
        let db = DB::new(1 << 30);
        let false_stack = db.get_memory(n_vars + 1);
        let mut solver = Solver {
            db,
            n_vars,
            n_clauses,
            max_lemmas: 2000,
            n_lemmas: 0,
            n_conflicts: 0,
            n_restarts: 0,
            fast: 1 << 24,
            slow: 1 << 24,
            false_: db.get_memory(n_vars + 1) + n_vars as i32,
            false_stack,
            assigned: false_stack,
            forced: false_stack,
            processed: false_stack,
            model: db.get_memory(n_vars + 1),
            reason: db.get_memory(n_vars + 1),
            next: db.get_memory(n_vars + 1),
            prev: db.get_memory(n_vars + 1),
            first: db.get_memory(n_vars + 1) + n_vars as i32,
            buffer: db.get_memory(n_vars),
            head: n_vars,
        };
        db.data.offset(db.mem_used as isize).write(0);
        db.mem_used += 1; // Make sure there is a 0 before the clauses are loaded.
        solver
    }

    #[inline]
    fn unassign(&mut self, lit: i32) {
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
    fn add_clause(&mut self, c: RawPtr<'a, i32>, n: usize, lemma: bool) {
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

fn parse(filename: &str) -> Res<Solver> {
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
    let solver = Solver::new(n, m);
    for line in lines {
        let mut size = 0;
        let line = line?;
        for c in line.trim().split_whitespace() {
            let i = str::parse::<i32>(c).expect("expected integer");
            if i == 0 {
                solver.add_clause(solver.buffer, size, false);
            } else {
                solver.buffer[size as i32] = i;
                size += 1;
            }
        }
    }
    Ok(solver)
}

fn main() -> Res<()> {
    let mut s = parse("foo.cnf")?;
    let r = s.solve();
    match r {
        R::Sat => println!("s SATISFIABLE"),
        R::Unsat => println!("s UNSATISFIABLE"),
    }
    Ok(())
}
