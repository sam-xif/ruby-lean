# L289: object inspect result raises.

# inspect-result-hook-raise
o=Object.new;def o.instance_variables_to_inspect;raise "final_hook";end;o
