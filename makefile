MKDIR_P = mkdir -p
MV = mv

sort:
	${MKDIR_P} synth
	${MKDIR_P} dist
	${MV} *s[[:digit:]] synth/
	${MV} *d[[:digit:]] dist/

clean:
	$(RM) *_b*
	$(RM) *_d*
	$(RM) bar*
	$(RM) *.png
	$(RM) *.dot
	$(RM) *.log*
	$(RM) *assert_out*
	$(RM) components
	$(RM) connections*
	$(RM) bar
	$(RM) foo*
	$(RM) assert_oracle*
	$(RM) oracle*
	$(RM) sed*
	$(RM) *~
