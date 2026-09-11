s = "  Foo_Bar  "
s.strip.downcase.tr("_", "-").delete_prefix("f")
