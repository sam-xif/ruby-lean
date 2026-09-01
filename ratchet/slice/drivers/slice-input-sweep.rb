# Driver for the whole linked slice over a **sweep of generated inputs** — the
# ratchet's copy of `homebrew/slice-driver/probes/input-sweep.rb`, with the sweep
# narrowed from 64 versions to 16.
#
# Why narrowed: the corpus's agreement gate (`scripts/run_agreement.sh`, i.e. the
# real difftest engine) gives each program a 10-second budget in the model, and
# the 64-input sweep spends ~12s of it — the boot heap is ~2.5s and each further
# `range_status` is ~0.15s. That cost is the probe's own finding and is recorded
# where it was measured (`homebrew/slice-driver/probes/README.md`); a corpus rung
# only needs enough inputs to show the verdict is a *function* of them, and 16
# spanning both ranges does that.
V = Homebrew::Vulns::Vulnerability

ADV = {
  "id" => "GHSA-probe",
  "affected" => [
    { "package" => { "ecosystem" => "Homebrew", "name" => "libexample" },
      "ranges" => [{ "type" => "SEMVER",
                     "events" => [{ "introduced" => "1.0.0" }, { "fixed" => "2.0.0" }] }] },
    { "package" => { "ecosystem" => "Homebrew", "name" => "libexample" },
      "ranges" => [{ "type" => "ECOSYSTEM",
                     "events" => [{ "introduced" => "1.5" }, { "fixed" => "2.5" }] }] },
  ],
}.freeze

record = V.new(ADV)
tally = { affected: 0, fixed: 0, not_applicable: 0, none: 0, raised: 0 }

(0..3).each do |a|
  (0..1).each do |b|
    (0..1).each do |c|
      version = "#{a}.#{b}.#{c}"
      begin
        st = record.range_status("Homebrew", "libexample", version)
        tally[st ? st.state : :none] += 1
      rescue StandardError
        tally[:raised] += 1
      end
    end
  end
end

puts("16 inputs => #{tally.inspect}")
