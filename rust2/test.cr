#!/usr/bin/env crystal

class Solver
  def initialize(@name : String, @cmd : String, @sat : Regex, @unsat : Regex)
  end

  def <=>(x : self)
    @name <=> x.@name
  end
  include Comparable(self)

  delegate to_s, inspect, to: @name

  def run(file, timeout = 10, &block : Status -> _)
    cmd = @cmd.gsub("{file}", file)
    cmd = "ulimit -t #{timeout}; exec #{cmd}"
    # run command, capture output in `s`
    s : String = String.build { |io| Process.run(cmd, shell: true, output: io) }
    if s.match(@sat)
      yield Status::SAT
    elsif s.match(@unsat)
      yield Status::UNSAT
    else
      yield Status::UNKNOWN
    end
  end

  def self.all
    [
      Solver.new("minisat", cmd: "minisat {file}", sat: /^SATISFIABLE/m, unsat: /^UNSATISFIABLE/m),
      Solver.new("microsat-rs", cmd: "./microsat-rs {file}", sat: /^s SATISFIABLE/m, unsat: /^s UNSATISFIABLE/m),
      Solver.new("microsat-c", cmd: "./microsat-c {file}", sat: /^s SATISFIABLE/m, unsat: /^s UNSATISFIABLE/m),
    ]
  end
end

enum Status
  SAT, UNSAT, UNKNOWN
end

# result for running a given solver
record Result, solver : Solver, filename : String, status : Status, time : Time::Span

record DirSize, size : Int32, dir : String
alias Message = DirSize | Result

# Run solvers on the given directory
def run_on_dir(dir : String, chan : Channel(Message)) : Nil
  files = Dir.glob "#{dir}/**/*.cnf"
  chan.send(DirSize.new size: files.size, dir: dir)
  files.each do |file|
    Solver.all.each do |solver|
      spawn do
        puts "process file #{file} with solver #{solver}"
        start = Time.monotonic
        solver.run(file) do |status|
          duration = Time.monotonic - start
          puts "file #{file} with solver #{solver}: #{status} in #{duration}"
          chan.send(Result.new solver, filename: file, status: status, time: duration)
        end
      end
    end
  end
end

def start
  chan = Channel(Message).new
  n_dirs = 0 # number of directories

  ARGV.each do |dir|
    n_dirs += 1
    puts "run on dir #{dir}"
    spawn { run_on_dir dir, chan }
  end

  results = Hash(String, Hash(Solver, Status)).new
  results_missing = 0
  loop do
    break if n_dirs == 0 && results_missing == 0 # all done
    case m = chan.receive
    when DirSize
      n_dirs -= 1
      results_missing += m.size * Solver.all.size
      #puts "need #{m.size} more results from #{m.dir}"
    when Result
      # update map
      map = results.fetch(m.filename) { Hash(Solver,Status).new }
      map[m.solver] = m.status
      results[m.filename] = map
      results_missing -= 1
      #puts "result #{m}"
    end
  end

  # find problems with conflicts
  results.each do |file,map|
    if map.values.any?{|r| r == Status::SAT} && map.values.any?{|r| r == Status::UNSAT}
      puts "conflict on #{file}: #{map.to_a.sort}"
    end
  end
end

start
