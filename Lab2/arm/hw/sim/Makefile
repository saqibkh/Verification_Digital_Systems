#run "make clean" to remove all temp files
clean:
	rm -rf work tests.log transcript
	rm -rf wlf* *.txt *.wlf *.log *.trn *.vcd *.dsn
	rm -rf amber.dis

#run "make ethmac_tx" to run the ethmac_tx test
ethmac_tx:
	make clean
	../tools/run.sh -5 -g -z ethmac_tx

