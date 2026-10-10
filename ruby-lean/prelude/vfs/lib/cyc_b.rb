# frozen_string_literal: true
$cyc << :b_start
$cyc << [:b_sees_a, require_relative("cyc_a")]
$cyc << :b_end
