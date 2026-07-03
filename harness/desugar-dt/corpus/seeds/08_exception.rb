# desugar must preserve a deterministic raise (exc class + message observed)
print("before")
raise("boom")
print("after")
