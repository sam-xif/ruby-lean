# frozen_string_literal: true
# Half of a circular require_relative pair (with cyc_b.rb): while this file is
# still loading, cyc_b requires it back and must get `false`, not a re-run.
$cyc ||= []
$cyc << :a_start
require_relative "cyc_b"
$cyc << :a_end
