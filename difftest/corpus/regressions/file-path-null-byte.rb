# A null byte in a File/Dir path argument raises ArgumentError in CRuby.
# The model answered a value or `false` before reaching the filesystem, which
# is a wrong answer rather than a gate.

def show
  p yield
rescue => e
  p [e.class, e.message]
end

show { File.exist?("/tmp/a\0b") }
show { File.file?("/tmp/a\0b") }
show { File.directory?("/tmp/a\0b") }
show { Dir.exist?("/tmp/a\0b") }

show { File.basename("/tmp/a\0b") }
show { File.dirname("/tmp/a\0b") }
show { File.extname("/tmp/a\0b") }
show { File.join("/tmp/a\0b", "z") }
show { File.basename("abc", "b\0c") }
nil
