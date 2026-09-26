# frozen_string_literal: true

require "open3"
require "json"
require "tempfile"

# obs+ : run a Ruby program in a fresh CRuby subprocess and record a normalized
# observation = (stdout, value, exc). stdout is the ordered side-effect trace
# (implementation-choices.md C5). Value/exc are written by a wrapper to a side file so
# they don't pollute the program's own stdout.
module Observe
  # Path to the CRuby oracle. Overridable via RUBY_ORACLE.
  ORACLE = ENV.fetch("RUBY_ORACLE") do
    prefix = `brew --prefix ruby 2>/dev/null`.strip
    prefix.empty? ? "ruby" : File.join(prefix, "bin", "ruby")
  end

  Obs = Struct.new(:stdout, :value, :exc, :error, keyword_init: true) do
    def ok?  = error.nil?
    def ==(o) = o.is_a?(Obs) && stdout == o.stdout && value == o.value && exc == o.exc && error == o.error
    def to_h = { stdout: stdout, value: value, exc: exc, error: error }
  end

  module_function

  # RubyCore's **runtime support layer** (C38). The desugaring of string interpolation
  # needs CRuby's `rb_obj_as_string`, whose third step — "if `to_s` did not answer a
  # String, use `rb_any_to_s`" — has no Ruby-level name. The Lean model supplies this in
  # its prelude; here it is written with the C function's own semantics so that both
  # sides of the round-trip, `obs+(P)` and `obs+(render(desugar(P)))`, see one rule.
  #
  # It is in the *wrapper*, so **both** sides get it and neither can be advantaged by it
  # — the same reason the difftest harness owns its stub set rather than the prelude
  # (L112). `Object.instance_method(:to_s)` is exactly `rb_any_to_s`: the default
  # `Object#to_s` *is* that C function, and binding it skips every override.
  SUPPORT = <<~'RUBY'
    class Object
      def __as_string
        return self if String === self

        s = to_s
        String === s ? s : Object.instance_method(:to_s).bind(self).call
      end
    end
  RUBY

  WRAPPER = <<~'RUBY'
    $__obs_out = ENV["OBS_OUT"]
    srand(0)
    %<support>s
    __exc = nil
    __val =
      begin
    %<program>s
      rescue Exception => e
        __exc = e
        nil
      end
    require "json"
    def __safe_inspect(v); v.inspect; rescue Exception; "<uninspectable>"; end
    File.write($__obs_out, JSON.generate(
      "value" => (__exc ? nil : __safe_inspect(__val)),
      "exc"   => (__exc ? [__exc.class.name, __exc.message.to_s] : nil)
    ))
  RUBY

  # Run `src` and return an Obs. `timeout` in seconds.
  def run(src, timeout: 10)
    indented = src.each_line.map { |l| "    #{l}" }.join
    indented += "\n" unless indented.end_with?("\n")
    wrapper = format(WRAPPER, program: indented, support: SUPPORT)

    Tempfile.create(["dt_prog", ".rb"]) do |prog_f|
      prog_f.write(wrapper)
      prog_f.flush
      Tempfile.create(["dt_obs", ".json"]) do |obs_f|
        out, err, status = capture(prog_f.path, obs_f.path, timeout)
        return Obs.new(error: "timeout") if status == :timeout

        meta =
          begin
            raw = File.read(obs_f.path)
            raw.empty? ? nil : JSON.parse(raw)
          rescue StandardError
            nil
          end

        # No meta written => the wrapper itself failed to load/parse (e.g. a program
        # that broke the begin/end inlining). Treat as a harness-level error.
        if meta.nil?
          return Obs.new(error: "no-observation", stdout: normalize(out),
                         exc: (err.empty? ? nil : ["<child-stderr>", normalize(err)[0, 200]]))
        end

        Obs.new(stdout: normalize(out), value: normalize_s(meta["value"]), exc: normalize_exc(meta["exc"]))
      end
    end
  end

  def capture(prog_path, obs_path, timeout)
    out = +""
    err = +""
    status = nil
    Open3.popen3({ "OBS_OUT" => obs_path }, ORACLE, "--disable-gems", prog_path) do |stdin, stdout, stderr, wait|
      stdin.close
      begin
        Timeout.timeout(timeout) do
          out << stdout.read
          err << stderr.read
          wait.value
        end
      rescue Timeout::Error
        Process.kill("KILL", wait.pid) rescue nil
        status = :timeout
      end
    end
    [out, err, status]
  end

  # --- normalization (implementation-choices.md C6) ---

  ADDR = /0x[0-9a-f]+/.freeze

  def normalize(str)
    return str if str.nil?
    str.gsub(ADDR, "0xXXXX")
  end

  def normalize_s(str)
    str.nil? ? nil : normalize(str)
  end

  def normalize_exc(exc)
    return nil if exc.nil?
    [exc[0], normalize(exc[1].to_s)]
  end
end

require "timeout"
