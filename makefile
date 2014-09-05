
clean:
	cp origin.m4 bigadd.m4
	$(RM) *.png
	$(RM) *.dot
	$(RM) *.log*
	$(RM) *assert_out*
	$(RM) components
	$(RM) connections
	$(RM) bar
	$(RM) foo.smt2
	$(RM) assert_oracle*
	$(RM) oracle*
	$(RM) sed*
	$(RM) *~
