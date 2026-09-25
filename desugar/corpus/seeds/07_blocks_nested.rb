# blocks + arrays + rule interaction (interp inside a block inside a conditional)
acc = 0
[1, 2, 3].each { |z| acc = acc + z }
label = "sum=#{acc}" unless acc == 0
print(label)
acc
