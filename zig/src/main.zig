const std = @import("std");
const c = @cImport({
    @cInclude("stdlib.h");
    @cInclude("stdio.h");
});

const END: i32 = -9;
const UNSAT: i32 = 0;
const SAT: i32 = 1;
const MARK: i32 = 2;
const IMPLIED: i32 = 6;

fn abs(i: var) @typeof(-i) {
    return if (i > 0) i else -i;
}

const V32 = struct {
    ptr: [*c]i32,
    const Self = @This();

    fn get(self: *Self, idx: i32) *i32 {
        return @intToPtr(*i32, @intCast(usize, @intCast(isize, @ptrToInt(self.ptr)) + @intCast(isize, idx)));
    }
};

const Solver = struct {
    DB: [*c]i32, // main memory bank
    nVars: i32,
    nClauses: i32,
    mem_used: usize,
    mem_fixed: usize,
    mem_max: usize,
    maxLemmas: usize,
    nLemmas: usize,
    buffer: [*c]i32,
    nConflicts: usize,
    model: [*c]i32,
    reason: V32,
    falseStack: [*c]i32,
    false_: V32,
    first: V32,
    forced: [*c]i32,
    processed: [*c]i32,
    assigned: [*c]i32,
    next: V32,
    prev: V32,
    head: usize,
    res: usize,
    fast: usize,
    slow: usize,
    status: i32,
};

fn unassign(S: *Solver, lit: i32) void {
    S.false_[lit] = 0;
}
fn restart(S: *Solver) void {
    while (S.assigned > S.forced) {
        unassign(S, S.assigned.*);
        S.assigned -= 1;
    }
    S.processed = S.forced;
}
pub fn assign(S: *Solver, reason: [*c]i32, forced: i32) void {
    const lit: i32 = reason[0];
    S.false_.get(-lit).* = if (forced != 0) IMPLIED else 1;
    S.assigned.* = -lit;
    S.assigned += 1;
    S.reason[abs(lit)] = 1 + i32(reason - S.DB);
    S.model[@intCast(usize, abs(lit))] = (lit > 0);
}
pub fn addWatch(S: *Solver, lit: i32, mem: i32) void {
    S.DB[mem] = S.first[lit];
    S.first[lit] = mem;
}
pub fn getMemory(S: *Solver, mem_size: usize) [*c]i32 {
    if ((S.mem_used + mem_size) > S.mem_max) {
        _ = c.printf(c"c out of memory\n");
        c.exit(0);
    }
    var store: [*c]i32 = S.DB + S.mem_used;
    S.mem_used += mem_size;
    return store;
}
pub fn addClause(S: *Solver, in: [*c]i32, size: usize, irr: i32) [*c]i32 {
    var i: usize = undefined;
    var used: i32 = @intCast(i32, S.mem_used);
    var clause: [*c]i32 = getMemory(S, size + 3) + 2;
    if (size > 1) {
        addWatch(S, in[0], used);
        addWatch(S, in[1], used + 1);
    }
    {
        while (i < size) : (i += 1) clause[i] = in[i];
    }
    clause[i] = 0;
    if (irr != 0) {
        S.mem_fixed = S.mem_used;
    } else {
        S.nLemmas += 1;
    }
    return clause;
}
pub fn reduceDB(S: *Solver, k: i32) void {
    while (S.nLemmas > S.maxLemmas) S.maxLemmas += 300;
    S.nLemmas = 0;
    var i: i32 = undefined;
    {
        i = (-S.nVars);
        while (i <= S.nVars) : (i += 1) {
            if (i == 0) continue;
            var watch: [*c]i32 = &S.first[i];
            while (watch.* != END) {
                if (watch.* < S.mem_fixed) {
                    watch = (S.DB +% watch.*);
                } else {
                    watch.* = S.DB[watch.*];
                }
            }
        }
    }
    var old_used: i32 = S.mem_used;
    S.mem_used = S.mem_fixed;
    {
        i = (S.mem_fixed + 2);
        while (i < old_used) : (i += 3) {
            var count: i32 = 0;
            var head: i32 = i;
            while (S.DB[i] != 0) {
                var lit: i32 = S.DB[(x: {
                    const _ref = &i;
                    const _tmp = _ref.*;
                    _ref.* += 1;
                    break :x _tmp;
                })];
                if ((lit > 0) == S.model[abs(lit)]) count += 1;
            }
            if (count < k) {
                _ = addClause(S, S.DB +% head, i - head, 0);
            }
        }
    }
}
pub fn bump(S: *Solver, lit: i32) void {
    if (S.false_[lit] != IMPLIED) {
        S.false_[lit] = MARK;
        var var_: i32 = abs(lit);
        if (var_ != S.head) {
            S.prev[S.next[var_]] = S.prev[var_];
            S.next[S.prev[var_]] = S.next[var_];
            S.next[S.head] = var_;
            S.prev[var_] = S.head;
            S.head = var_;
        }
    }
}
pub fn implied(S: *Solver, lit: i32) i32 {
    if (S.false_[lit] > MARK) return S.false_[lit] & MARK;
    if (!(S.reason[abs(lit)] != 0)) return 0;
    var p: [*c]i32 = (S.DB +% S.reason[abs(lit)]) -% 1;
    while ((x: {
        const _ref = &p;
        _ref.* +%= 1;
        break :x _ref.*;
    }).* != 0) {
    if ((S.false_[p.*] ^ MARK) and (!(implied(S, p.*) != 0))) {
        S.false_[lit] = (IMPLIED - 1);
        return 0;
    }
    };
    S.false_[lit] = IMPLIED;
    return 1;
}
pub fn propagate(S: *Solver) i32 {
    var forced: i32 = S.reason[abs(S.processed.*)];
    while (S.processed < S.assigned) {
        var lit: i32 = (x: {
            const _ref = &S.processed;
            const _tmp = _ref.*;
            _ref.* +%= 1;
            break :x _tmp;
        }).*;
        var watch: [*c]i32 = &S.first[lit];
        while (watch.* != END) {
            var i: i32 = undefined;
            var unit: i32 = 1;
            var clause: [*c]i32 = (S.DB +% watch.*) +% 1;
            if (clause[-2] == 0) clause +%= 1;
            if (clause[0] == lit) clause[0] = clause[1];
            {
                i = 2;
                while ((unit != 0) and (clause[i] != 0)) : (i += 1) if (!(S.false_[clause[i]] != 0)) {
                    clause[1] = clause[i];
                    clause[i] = lit;
                    var store: i32 = watch.*;
                    unit = 0;
                    watch.* = S.DB[watch.*];
                    addWatch(S, clause[1], store);
                };
            }
            if (unit != 0) {
                clause[1] = lit;
                watch = (S.DB +% watch.*);
                if (S.false_[-clause[0]] != 0) continue;
                if (!(S.false_[clause[0]] != 0)) {
                    assign(S, clause, forced);
                } else {
                    if (forced != 0) return UNSAT;
                    var lemma: [*c]i32 = analyze(S, clause);
                    if (!(lemma[1] != 0)) forced = 1;
                    assign(S, lemma, forced);
                    break;
                }
            }
        }
    }
    if (forced != 0) S.forced = S.processed;
    return SAT;
}
pub fn solve(S: *Solver) i32 {
    var decision: i32 = S.head;
    S.res = 0;
    while (true) {
        var old_nLemmas: i32 = S.nLemmas;
        if (propagate(S) == UNSAT) return UNSAT;
        if (S.nLemmas > old_nLemmas) {
            decision = S.head;
            if (S.fast > (@divTrunc(S.slow, 100) * 125)) {
                S.res = 0;
                S.fast = (@divTrunc(S.slow, 100) * 125);
                restart(S);
                if (S.nLemmas > S.maxLemmas) reduceDB(S, 6);
            }
        }
        while ((S.false_[decision] != 0) or (S.false_[-decision] != 0)) {
            decision = S.prev[decision];
        }
        if (decision == 0) return SAT;
        decision = if (S.model[decision]) decision else -decision;
        S.false_[-decision] = 1;
        (x: {
            const _ref = &S.assigned;
            const _tmp = _ref.*;
            _ref.* +%= 1;
            break :x _tmp;
        }).* = (-decision);
        decision = abs(decision);
        S.reason[decision] = 0;
    }
}

fn mkSolver(alloc: *std.mem.Allocator, n_: i32, m: i32) !*Solver {
    const n = if (n_ < 1) 1 else n_;
    const S = try alloc.create(Solver);
    S.nVars = n;
    S.nClauses = m;
    S.mem_max = 1 << 30;
    S.mem_used = 0;
    S.nLemmas = 0;
    S.nConflicts = 0;
    S.maxLemmas = 2000;
    S.slow = 1 << 24;
    S.fast = 1 << 24;
    S.DB = @ptrCast([*c]i32, (try alloc.alloc(i32, S.mem_max)).ptr);
    const nUsize = @intCast(usize, n);
    S.model = getMemory(S, nUsize + 1);
    S.next = V32{ .ptr = getMemory(S, nUsize + 1) };
    S.prev = V32{ .ptr = getMemory(S, nUsize + 1) };
    S.buffer = getMemory(S, nUsize);
    S.reason = V32{ .ptr = getMemory(S, nUsize + 1) };
    S.falseStack = getMemory(S, nUsize + 1);
    S.forced = S.falseStack;
    S.processed = S.falseStack;
    S.assigned = S.falseStack;
    S.false_ = V32{ .ptr = getMemory(S, (2 * nUsize) + 1) + nUsize };
    S.first = V32{ .ptr = getMemory(S, (2 * nUsize) + 1) + nUsize };
    S.status = SAT;
    S.DB[S.mem_used] = 0;
    S.mem_used += 1;
    {
        var i: i32 = 1;
        while (i <= n) : (i += 1) {
            S.prev.get(i).* = (i - 1);
            S.next.get(i - 1).* = i;
            S.false_.get(i).* = 0;
            S.false_.get(-i).* = 0;
            S.model[@intCast(usize, i)] = 0;
            S.first.get(i).* = END;
            S.first.get(-i).* = END;
        }
    }
    S.head = @intCast(usize, n);
    return S;
}

pub fn parse(alloc: *std.mem.Allocator, filename: [*c]u8) !*Solver {
    var tmp: i32 = undefined;
    var input: [*c]c.FILE = c.fopen(filename, c"r");
    var nVars: i32 = undefined;
    var nClauses: i32 = undefined;
    while (true) {
        tmp = c.fscanf(input, c" p cnf %i %i \n", &nVars, &nClauses);
        if (tmp > 0 and tmp != -1) break;
        tmp = c.fscanf(input, c"%*s\n");
        if (!(tmp != 2 and tmp != -1)) break;
    }
    const S: *Solver = try mkSolver(alloc, nVars, nClauses);
    var nZeros: i32 = S.nClauses;
    var size: i32 = 0;
    while (nZeros > 0) {
        var lit: i32 = 0;
        tmp = c.fscanf(input, c" %i ", &lit);
        if (!(lit != 0)) {
            var clause: [*c]i32 = addClause(S, S.buffer, @intCast(usize, size), 1);
            if ((!(size != 0)) or ((size == 1) and (S.false_.get(clause[0]).* != 0))) {
                S.status = UNSAT;
                return S;
            }
            if ((size == 1) and (!(S.false_.get(-clause[0]).* != 0))) {
                assign(S, clause, 1);
            }
            size = 0;
            nZeros -= 1;
        } else {
            S.buffer[@intCast(usize, size)] = lit;
            size += 1;
        }
    }
    _ = c.fclose(input);
    S.status = SAT;
    return S;
}

pub export fn main(argc: i32, argv: [*c][*c]u8) void {
    const S: *Solver = parse(std.heap.c_allocator, argv[1]) catch {
        _ = c.printf(c"error\n");
        c.exit(0);
    };
    if (S.status == UNSAT) {
        _ = c.printf(c"s UNSATISFIABLE\n");
    } else if (solve(S) == UNSAT) {
        _ = c.printf(c"s UNSATISFIABLE\n");
    } else {
        _ = c.printf(c"s SATISFIABLE\n");
    }
    _ = c.printf(c"c statistics of %s: mem: %i conflicts: %i max_lemmas: %i\n", argv[1], S.mem_used, S.nConflicts, S.maxLemmas);
}
