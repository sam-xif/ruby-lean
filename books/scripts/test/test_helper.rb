# frozen_string_literal: true

# Loaded first by every test file. Measures line and branch coverage of the
# derivation emitter and the signature reader (`make emitter-unit` compares it
# with coverage-baseline.json).
require "simplecov"

ROOT = File.expand_path("../../..", __dir__)

SimpleCov.start do
  root ROOT
  coverage_dir ".make/coverage/emitter"
  command_name "emitter-unit"
  enable_coverage :branch
  cover "books/scripts/emit_deriv.rb", "books/scripts/read_sigs.rb"
  formatter SimpleCov::Formatter::SimpleFormatter
end

$LOAD_PATH.unshift File.join(ROOT, "desugar/lib")
require "minitest/autorun"
require "json"
require "stringio"
require "tmpdir"
require "desugar"
require "export"
require_relative "../read_sigs"
require_relative "../emit_deriv"

module EmitterTestHelper
  # The strippers, in the order `build_corpus.py` runs them.
  STRIPPERS = %w[sig_strip visibility_strip freeze_strip require_strip const_inline class_sugar_strip]
              .map { |s| File.join(ROOT, "difftest/ruby/#{s}.rb") }.freeze

  module_function

  # The front end of `bin/ruby-lean-check`, in this process: the signatures
  # read off the annotated source, the program stripped and desugared, and the
  # emitter's answer. Returns the emitter's result, or [:stripper, name, status]
  # or [:desugar, reason] when an earlier stage declines.
  def pipeline(src)
    sigs, = read_sigs(src)
    stripped = src
    STRIPPERS.each do |path|
      status, stripped = run_stripper(path, stripped)
      return [:stripper, File.basename(path, ".rb"), status] unless status.zero?
    end
    begin
      core, = Desugar.program(stripped)
    rescue Desugar::Unsupported => e
      return [:desugar, e.message]
    end
    emit(JSON.parse(Export.json(core)), sigs)
  end

  # The strippers are scripts that read stdin and write stdout, and share
  # top-level names with one another, so each runs in a fork of its own: the
  # cost of a fork and none of the cost of starting Ruby.
  def run_stripper(path, src)
    in_r, in_w = IO.pipe
    out_r, out_w = IO.pipe
    pid = fork do
      in_w.close
      out_r.close
      $stdin = in_r
      $stdout = out_w
      $stderr.reopen(File::NULL)
      begin
        load path
        status = 0
      rescue SystemExit => e
        status = e.status
      end
      $stdout.flush
      exit!(status)
    end
    in_r.close
    out_w.close
    in_w.write(src)
    in_w.close
    out = out_r.read
    out_r.close
    _, status = Process.wait2(pid)
    [status.exitstatus, out]
  end

  # The emitter on a program with no signatures to read.
  def emit_src(src) = emit(JSON.parse(Export.json(Desugar.program(src).first)), { "sigs" => [], "dropped" => [] })
end
