# frozen_string_literal: true

require_relative "desugar"
require_relative "render"
require_relative "rubycore"
require_relative "observe"
require_relative "linearize"

# The round-trip check for a single program (artifact 06 §1-§6):
#
#   obs+( P )  ≟  obs+( render_core(desugar(parse(P))) )
#
# plus the pure checks is_core and normal-form. Returns a Result describing the outcome
# and, on disagreement, which triage bucket it falls into (artifact 06 §6).
module Roundtrip
  Result = Struct.new(
    :status,        # :agree | :disagree | :out_of_fragment | :parse_error | :harness_error
    :bucket,        # for :disagree — :trace | :value_exc | :obs_normalizer | :render (nil otherwise)
    :reason, :coverage, :core, :rendered, :obs_src, :obs_core, :normal_form, :ast_idempotent,
    keyword_init: true
  )

  module_function

  def check(src, inject_bug: false)
    # 1. parse + desugar (fragment gate)
    begin
      core, coverage = Desugar.program(src, inject_bug: inject_bug)
    rescue Desugar::Unsupported => e
      return Result.new(status: :out_of_fragment, reason: e.message)
    rescue StandardError => e
      return Result.new(status: :parse_error, reason: "#{e.class}: #{e.message}")
    end

    # 2. pure check: is_core
    if (wf = RubyCore.explain(core))
      return Result.new(status: :disagree, bucket: :render, reason: "is_core failed: #{wf}",
                        coverage: coverage, core: core)
    end

    rendered = Render.core(core)

    # 3. pure check: normal-form / idempotence through a render round-trip
    #    (warning, not a disagreement — C9). This composes render + parse + desugar,
    #    so it also trips on render↔parse artifacts that are NOT desugar bugs (e.g.
    #    a `name=` writer send re-parsing as an attribute assignment — see C21/C9).
    normal_form =
      begin
        core2, = Desugar.program(rendered, inject_bug: inject_bug)
        RubyCore.eq?(core, core2)
      rescue StandardError
        false
      end

    # 3b. pure check: AST-space idempotence (critical — C22). Re-apply our
    #     RubyCore→RubyCore pass(es) to the already-core AST, with NO render/parse
    #     in the loop. A failure here is a genuine non-idempotence of our own
    #     transformations; passing while `normal_form` fails isolates the cause as a
    #     render↔parse artifact rather than a desugar bug. (The Prism→core step
    #     cannot be self-composed — its input is a Prism AST — so `render` is the
    #     only bridge back into it; that bridge is exactly what this check omits.)
    ast_idempotent =
      begin
        RubyCore.eq?(core, Linearize.run(core))
      rescue StandardError
        false
      end

    # 4. observational round-trip
    obs_src  = Observe.run(src)
    obs_core = Observe.run(rendered)

    # Equality is checked FIRST — including the error field (Obs#==). Two *identical*
    # observations are agreement even when both are error-observations: the desugaring is
    # faithful, producing behavior the harness cannot distinguish from the original,
    # including identical un-observability. This covers a program that redefines a core
    # method the observation wrapper itself relies on (e.g. `String#==`), which crashes the
    # in-process wrapper (C7) the SAME way on both sides. See C20.
    if obs_src == obs_core
      return Result.new(status: :agree, coverage: coverage, core: core, rendered: rendered,
                        obs_src: obs_src, obs_core: obs_core, normal_form: normal_form,
                        ast_idempotent: ast_idempotent)
    end

    # Not equal, and at least one side failed to produce an observation => a genuine
    # harness-level problem (asymmetric: one ran, one broke, or they broke differently).
    if !obs_src.ok? || !obs_core.ok?
      return Result.new(status: :harness_error, coverage: coverage, core: core, rendered: rendered,
                        reason: "obs error: src=#{obs_src.error.inspect} core=#{obs_core.error.inspect}",
                        obs_src: obs_src, obs_core: obs_core, normal_form: normal_form,
                        ast_idempotent: ast_idempotent)
    end

    Result.new(status: :disagree, bucket: bucket_for(obs_src, obs_core), coverage: coverage,
               core: core, rendered: rendered, obs_src: obs_src, obs_core: obs_core,
               normal_form: normal_form, ast_idempotent: ast_idempotent,
               reason: diff(obs_src, obs_core))
  end

  # Triage bucket (artifact 06 §6). No "model bug" bucket exists yet — the point of
  # doing desugar first.
  def bucket_for(a, b)
    return :trace if a.stdout != b.stdout
    :value_exc
  end

  def diff(a, b)
    parts = []
    parts << "stdout: #{a.stdout.inspect} vs #{b.stdout.inspect}" if a.stdout != b.stdout
    parts << "value: #{a.value.inspect} vs #{b.value.inspect}"    if a.value != b.value
    parts << "exc: #{a.exc.inspect} vs #{b.exc.inspect}"          if a.exc != b.exc
    parts.join(" | ")
  end
end
