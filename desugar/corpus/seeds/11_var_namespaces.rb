# instance / global / constant variable namespaces (top level)
# (class variables @@x need a class body — exercised once M3 lands)
$counter = 0
LIMIT = 3
@acc = 0
i = 0
while i < LIMIT do
  @acc = @acc + i
  $counter = $counter + 1
  i = i + 1
end
print([@acc, $counter, LIMIT].inspect)
