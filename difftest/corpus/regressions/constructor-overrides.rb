# new-user-hash-block
def Hash.new(*a,&b);p [a,b.call];:override;end;p Hash.new{2}

# new-user-proc-block
def Proc.new(*a,&b);p [a,b.call];:override;end;p Proc.new{2}

# new-user-class-block
def Class.new(*a,&b);p [a,b.call];:override;end;p Class.new{2}

# new-user-module-block
def Module.new(*a,&b);p [a,b.call];:override;end;p Module.new{2}

nil
