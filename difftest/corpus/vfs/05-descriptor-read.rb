# Descriptors are step 2 of issue #7 and are not modeled yet, so the model is
# expected to *gate* this program, not answer it. The case is here to record
# the gate: if a later step models the block form wrongly, the verdict becomes a
# disagreement instead of a gate, which is the signal this corpus exists for.
File.open("/tmp/readme.txt", "r") do |f|
  print f.read
end
