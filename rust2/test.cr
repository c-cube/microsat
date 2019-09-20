#!/usr/bin/env crystal
require "option_parser"
require "json"

class Solver
  include JSON::Serializable

  def initialize(@name : String, @cmd : String, @sat : Regex, @unsat : Regex)
  end

  def <=>(x : self)
    @name <=> x.@name
  end

  include Comparable(self)

  delegate to_s, inspect, to: @name

  def run(file, timeout : Int32? = nil, &block : Status -> _)
    timeout = timeout || 10
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

  def to_json(b)
    b.string @name
  end
end

class Semaphore
  def initialize(n : Int32)
    raise Exception.new "semaphore needs positive argument, not #{n}" unless n > 0
    @wait = Channel(Nil).new n
    n.times { @wait.send(nil) }
  end

  def acquire(&block)
    @wait.receive
    begin
      yield
    ensure
      @wait.send nil
    end
  end
end

enum Status
  SAT; UNSAT; UNKNOWN

  def to_json(b)
    b.string(to_s)
  end

  def from_json(p)
    p.string(from_s)
  end
end

struct Time::Span
  include JSON::Serializable # make timespan serializable
end

# result for running a given solver
record Result, solver : Solver, filename : String, status : Status, time : Time::Span do
  include JSON::Serializable
end

record DirSize, size : Int32, dir : String
alias Message = DirSize | Result

# Run solvers on the given directory
def run_on_dir(dir : String, chan : Channel(Message), semaphore, timeout : Int32? = nil) : Nil
  files = Dir.glob "#{dir}/**/*.cnf"
  chan.send(DirSize.new size: files.size, dir: dir)
  files.each do |file|
    Solver.all.each do |solver|
      spawn do
        semaphore.acquire do
          puts "process file #{file} with solver #{solver} (timeout #{timeout})"
          start = Time.monotonic
          solver.run(file, timeout: timeout) do |status|
            duration = Time.monotonic - start
            puts "file #{file} with solver #{solver}: #{status} in #{duration}"
            chan.send(Result.new solver, filename: file, status: status, time: duration)
          end
        end
      end
    end
  end
end

record AllResult, all : Array(Result)

def start
  timeout = nil
  dirs = [] of String # directories to process
  j = 4
  res_file = nil
  OptionParser.parse! do |p|
    p.banner = "Usage: test.cr <dir> [option*]"
    p.on("-t TIME", "--timeout=TIME", "timeout in seconds") { |x| timeout = x.to_i32 }
    p.on("-j JOBS", "number of jobs") { |x| j = x.to_i32 }
    p.on("--json=FILE", "save into given json file") { |x| res_file = x}
    p.on("-h", "--help", "Show this help") { puts p; exit 0 }
    p.unknown_args { |a, b| dirs.concat(a).concat(b) }
  end

  semaphore = Semaphore.new j
  chan = Channel(Message).new

  dirs.each do |dir|
    puts "run on dir #{dir}"
    spawn { run_on_dir dir, chan, semaphore, timeout: timeout }
  end

  all_res = [] of Result
  n_dirs = dirs.size # remaining dirs to process
  results = Hash(String, Hash(Solver, Status)).new
  results_missing = 0
  loop do
    break if n_dirs == 0 && results_missing == 0 # all done
    case m = chan.receive
    when DirSize
      n_dirs -= 1
      results_missing += m.size * Solver.all.size
      # puts "need #{m.size} more results from #{m.dir}"
    when Result
      all_res << m
      # update map
      map = results.fetch(m.filename) { Hash(Solver, Status).new }
      map[m.solver] = m.status
      results[m.filename] = map
      results_missing -= 1
      # puts "result #{m}"
    end
  end

  # find problems with conflicts
  results.each do |file, map|
    if map.values.any? { |r| r == Status::SAT } && map.values.any? { |r| r == Status::UNSAT }
      puts "conflict on #{file}: #{map.to_a.sort}"
    end
  end

  if x=res_file
    puts "write results into #{x}"
    File.open(x, "w") { |io| all_res.to_json(io) }
  end
end

start
