# all:
# 	# pcal spsc.tla && tlc spsc
# 	pcal spmc.tla && tlc spmc

tla: 
	java -cp /home/richard/dev/tla2tex/tla2tools.jar  tla2tex.TeX  book.tex 
