# frozen_string_literal: true

require_relative "test_helper"
require "open3"
require "tmpdir"

# `srb_sigs.py --which-sorbet`: `find_sorbet()` is the one place that decides
# which Sorbet binary the pipeline reads signatures with, and
# `scripts/check-prereqs.sh` must report that same binary (issue #41). The
# binary decides which programs reach the validator, so an explicit `$SORBET`
# that does not name an executable file is an error, never a silent fallback.
class TestSrbSigs < Minitest::Test
  SCRIPT = File.join(ROOT, "books/scripts/srb_sigs.py")
  PREREQS = File.join(ROOT, "scripts/check-prereqs.sh")

  def which_sorbet(env = {})
    Open3.capture3({ "SORBET" => nil }.merge(env), "python3", SCRIPT, "--which-sorbet")
  end

  # The installed `sorbet-static` gem is enough: `srb` need not be on PATH.
  def test_names_the_gem_binary_when_sorbet_is_unset
    out, err, status = which_sorbet
    assert status.success?, err
    assert_path_exists out.strip
    assert File.executable?(out.strip), "#{out.strip} is not executable"
  end

  def test_honours_an_executable_sorbet
    gem_sorbet = which_sorbet.first.strip
    out, err, status = which_sorbet("SORBET" => gem_sorbet)
    assert status.success?, err
    assert_equal gem_sorbet, out.strip
  end

  # A bare name keeps working the way it did before there was one definition:
  # `$SORBET=sorbet` means "the one on PATH", resolved to its full path.
  def test_resolves_a_sorbet_named_on_path
    gem_sorbet = which_sorbet.first.strip
    out, err, status = which_sorbet("SORBET" => File.basename(gem_sorbet),
                                    "PATH" => "#{File.dirname(gem_sorbet)}:#{ENV.fetch("PATH", "")}")
    assert status.success?, err
    assert_equal gem_sorbet, out.strip
  end

  def test_refuses_a_sorbet_that_does_not_exist
    out, err, status = which_sorbet("SORBET" => "/nonexistent/sorbet")
    refute status.success?
    assert_empty out.strip
    assert_includes err, "$SORBET is '/nonexistent/sorbet', which is not an executable file"
  end

  def test_refuses_a_sorbet_that_is_not_executable
    Dir.mktmpdir do |dir|
      path = File.join(dir, "sorbet")
      File.write(path, "")
      File.chmod(0o644, path)
      _, err, status = which_sorbet("SORBET" => path)
      refute status.success?
      assert_includes err, "$SORBET is '#{path}', which is not an executable file"
    end
  end

  # The precedent #41 is about: a second copy of the lookup drifts. The
  # prerequisite check reports the binary it finds, so `make prereqs` and the
  # gate cannot disagree about which Sorbet graded the corpus.
  def test_check_prereqs_reports_the_same_binary
    expected, err, status = which_sorbet
    assert status.success?, err
    out, err, = Open3.capture3({ "SORBET" => nil }, PREREQS)
    reported = out[/^\s+sorbet\s+(.*)$/, 1]
    assert_equal expected.strip, reported, err
  end
end
