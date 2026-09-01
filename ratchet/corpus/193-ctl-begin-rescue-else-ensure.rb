log = []
begin
  v = 1
rescue StandardError
  log << "rescue"
else
  log << "else"
ensure
  log << "ensure"
end
log.length
