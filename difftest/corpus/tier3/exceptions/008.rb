log = []
def risky(log)
  begin
    log << :try
    raise TypeError, "t"
  rescue ArgumentError => e
    log << :arg
  ensure
    log << :ens
  end
end
begin
  risky(log)
rescue TypeError => e
  log << :outer
end
puts log.inspect
