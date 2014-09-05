; This is similar to bigadd, except that it also tries to be smart in
; designing the control part of the circuitry. 
;
; The main problem with bigadd was that it had too many possibilities
; to try for generating control input (defined here as the carry in
; bits). Thus, it worked when restricted to 2 nand gates, but not when
; 4 nand gates were allowed. 
;
; To solve this, we attempt to use the most refined version of an
; output net that is possible. For example, if N1=f(N2,N3), we attempt
; to use only N1. Note that it is simple to determine that N1=f(N2,N3)
; since there will be other constraints that ensure that
; loc(N1)<loc(N2) and loc(N1)<loc(N3) where loc(N) is the location of
; the functional unit producing net N. 
; 
; The implementation here is flawed, since it basically disallows
; using N2 unless N1 is also used (in the above example). Its OK for
; testing, but to be fair we can do one of the following eventually:
; - Add more constant gates with [ignored] inputs
; - Add more NAND gates (these can be used to essentially ignore N1) 
; - Use a staged approach that first attempts to synthesize using only
;   N1, then only N2, then N1 and N2, etc. 
; 
; The rest is identical to bigadd.m4 (see docs there). 
; 
; RESULTS (, stands for concat, @ stands for nand)
; WITH CVC DEFAULT OPTIONS
; Circ-1 Circ-alt     Inputs      Synthesized
;                     4,1   3,6   C1: see below
;                     1,14  8,9
;                     0,7   10,8
;                     6,0   4,11
;                     11,1  8,14
; Ca     C*           8,10  7,3   C*
; unsat
;
; Times for distinguishing input SMT calls
; 0.369u 0.019s 0:00.39 94.8%
; 0.565u 0.024s 0:00.59 98.3%
; 0.660u 0.028s 0:00.68 100.0%
; 0.785u 0.024s 0:00.81 98.7%
; 1.156u 0.036s 0:01.20 98.3%
; 2.612u 0.043s 0:02.66 99.6%
;
; CIRCUITS BEING GENERATED (all mod 16)
; C1 = (xl+yl+I19,xl+yl+I19) = (xl+yl+cout(xl+xh+xl_3),xl+yl+cout(xl+xh+xl_3)) 
;    in: 1  5  5 20 21 20 22  0  0  0  0  0  0  0  0 20  0 15  2
; Ca = (xl+yl+I18,xl+yl+I19) = (xl+yl+xl_3,xl+yl) 
;    in: 1  5  3 21 23 20 22  0  0  0  0  0  0  0  0 20  0 15  6
; C* = (xl+yl+I18,xl+yl+I19) = (xl+yl+cout(lo),xl+yl+0)
;    in: 1  5  3 21 23 20 22  0  0  0  0  0  0  0  0  0  0  4  6

; WITH CVC bitblast-eager OPTION
; Does not work (all but in1 disconnected, and in1 connected to out1):
; I think its a cvc bug  
; 
; CONCLUSIONS
; Results seem promising. However, it might be unfair to only allow 4
; NAND gates under the 'most refined' constraint (see comments
; above). Its a start, but a fairer version is needed.
;
; IDEAS:  
; 
;-----------------------------------------------------------------------------
; Definitions used by m4 to enable proper expansion 
;   ITER    iteration number
;   DIST    defined iff generating distinguishing input 
;   DEBUG   defined to generate extra output (commented, edit smt) 
;   INFO    defined to generate descriptive info
; The following are defined depending on which SMT solver we are
; using: 
;   CVC  BOOLECTOR
; The M4 comment delimiter is also changed, since SMTLIB needs the
; default pound delimiter to represent binary constants. 
; Note that a line is commented out by ;; to work with both m4 and
; smtlib (but that line wont appear in the SMTLIB file
; then). Alternatively, we could use just ; but avoid using commas in 
; the body of the comment (if its in a macro). 
;----------------------------------------------------------------------------
changecom(`;;')
define(`ITER',2)
define(`NEXT',eval(ITER+1))
;;define(`DIST',`')   
define(`INFO',`')
;;define(`DEBUG',`')
;;define(`BOOLECTOR',`')
define(`CVC',`')

include(`forloop.m4')

;----------------------------------------------------------------------------
; Useful macros for writing the code.
; Be careful - its easy to generate huge smtlib files.
;----------------------------------------------------------------------------
define(`NUMIN',19)
define(`NUMINLOG',5)
define(`NUMINBIN',#b10011)
define(`NUMOUT',23)
define(`NUMOUTLOG',5)
define(`NUMOUTBIN',#b10111)
define(`NUMCOMP',11)
define(`NUMCOMPLOG',4)
define(`GETBIT',(_ extract $1 $1))

;
; This attempts to synthesize an 8-bit adder (excluding overflow/etc) 
; from two 4-bit adders (with assorted minor components).  
; The regular version (dist not defined) synthesizes a circuit 
; satisfying the I/O oracle, while the distinguishing version
;generates 
; two circuits with the 2nd circuit indicated by an a appended to its
; parameters, and distinguishing values indicated by a d appended. 
;
; PROBLEMS:
; - It will not work if you are trying to synthesize the always-0
;   function. This restriction simplifies the constraints. 
;
; VARIABLES (19 input nets, 23 output nets, 11 components total)
;   A in-k      output net connected to input net k        
;   C valin*-n  values of in* for iteration n
;   D valout*-n values of out* for iteration n
;   E sysin*-n  values of circuit inputs for iteration n
;   F sysout-n  value of circuit output for iteration n
;   G loc*      linear ordering imposed on functional units
;   *a          alternate circuit (A/G)
;   *a-n        iteration n values on alternate circuit (C/D)
;   *d          distinguishing IO values (E/F)
;   *d          distinguishing values for original circuit (C/D)
;   *da         distinguishing values for alternate circuit (C/D/F)
;

; Produce unsatisfiable core (not supported by cvc)
ifdef(`CVC',`; ')(set-option :produce-unsat-cores true)

; Produce satisfying values for constants (boolector does this using
; flags) 
ifdef(`BOOLECTOR',`; ')(set-option :produce-models true)

; Produce satisfying assignments for functions 
; (set-option :produce-assignments true)

;(set-logic QF_BV)
(set-logic QF_ABV)

;
; Functional Units
;   2      Joiner (4X4-->8)
;   3,5    4-bit adders (with sum and carry out)
;   6,7    always 0 and always 1 circuits (1-bit)
;   8..11  2:1 nand gates
;   12,16  4-->1X1X1X1 splitters 
; Input Nets 
;   1      System output
;   2,3    Joiner inputs
;   4,5,18 Adder 1 inputs (18 is cin)
;   6,7,19 Adder 2 inputs (19 is cin)
;   8..15  Nand 1..4 inputs
;   16..17 Splitter 1,2 inputs
; Output Nets
;   1      Joiner output
;   2,3    Adder 1 output (3 is carryout)
;   4,5    Adder 2 output (5 is carryout)
;   6,7    Always 0, 1 respectively
;   8..11  Nand gate outputs
;   12..15 Splitter 1 output (15 is high bit)
;   16..19 Splitter 2 output (19 is high bit)
;   20,21  X input (21 is high bit)
;   22,23  Y input (23 is high bit)
;

;----------------------------------------------------------------------------
; Declarations of variables, and their ranges
;----------------------------------------------------------------------------
;
; The output net that each input net is connected to (0 if
; disconnected). Note that there is no net 0 (either input or
; output), leading to a slight inefficiency. 
;
forloop(`I',1,NUMIN,dnl 
(declare-fun in-I () (_ BitVec NUMOUTLOG))
(assert (not (bvult NUMOUTBIN in-I)))
)

; Copy of above with in-->ina
ifdef(`DIST',dnl
forloop(`I',1,NUMIN,dnl 
(declare-fun ina-I () (_ BitVec NUMOUTLOG))
(assert (not (bvult NUMOUTBIN ina-I)))
))
;----------------------------------------------------------------------------
; DO NOT UNCOMMENT THIS SECTION
; This is an actual working circuit, manually determined. It is there
; only for debug purposes. 
;(assert (= in-4 #b10100))    ; out3 <-- xl+yl (out2 is cout)
;(assert (= in-5 #b10110))  
;(assert (= in-18 #b00110)) 
;(assert (= in-19 #b00010))   ; out5 <-- out2+xh+yh
;(assert (= in-6 #b10101))
;(assert (= in-7 #b10111))
;(assert (= in-2 #b00011))    ; out1 <-- out5 ++ out3
;(assert (= in-3 #b00101))
;(assert (= in-1 #b00001))    ; in1 <-- out1 
;----------------------------------------------------------------------------
;
; Each input is connected to at most one output. Axioms for this are
; not needed since the connections are represented as a function. 
;

;
; Values on each net  
;
; (declare-fun valin-k-n () (_ BitVec ?))
;   Value of input net k on iteration n
; (declare-fun valout-k-n () (_ BitVec ?))
;   Value of output net k on iteration n
; (declare-fun sysinxl () (_ BitVec 4))
;                   ,sysinh,sysinyl,sysinyh
; (declare-fun sysout () (_ BitVec 8))
; 
; Distinguishing inputs are represented as the NEXT iteration. 
;
forloop(`I',1,ITER,dnl 
`(declare-fun valin-1-'`I'` () (_ BitVec 8))'
`(declare-fun valin-2-'`I'` () (_ BitVec 4))'
`(declare-fun valin-3-'`I'` () (_ BitVec 4))'
`(declare-fun valin-4-'`I'` () (_ BitVec 4))'
`(declare-fun valin-5-'`I'` () (_ BitVec 4))'
`(declare-fun valin-6-'`I'` () (_ BitVec 4))'
`(declare-fun valin-7-'`I'` () (_ BitVec 4))'
`(declare-fun valin-8-'`I'` () (_ BitVec 1))'
`(declare-fun valin-9-'`I'` () (_ BitVec 1))'
`(declare-fun valin-10-'`I'` () (_ BitVec 1))'
`(declare-fun valin-11-'`I'` () (_ BitVec 1))'
`(declare-fun valin-12-'`I'` () (_ BitVec 1))'
`(declare-fun valin-13-'`I'` () (_ BitVec 1))'
`(declare-fun valin-14-'`I'` () (_ BitVec 1))'
`(declare-fun valin-15-'`I'` () (_ BitVec 1))'
`(declare-fun valin-16-'`I'` () (_ BitVec 4))'
`(declare-fun valin-17-'`I'` () (_ BitVec 4))'
`(declare-fun valin-18-'`I'` () (_ BitVec 1))'
`(declare-fun valin-19-'`I'` () (_ BitVec 1))'
)

forloop(`I',1,ITER,dnl
`(declare-fun valout-1-'`I'` () (_ BitVec 8))'
`(declare-fun valout-2-'`I'` () (_ BitVec 1))'
`(declare-fun valout-3-'`I'` () (_ BitVec 4))'
`(declare-fun valout-4-'`I'` () (_ BitVec 1))'
`(declare-fun valout-5-'`I'` () (_ BitVec 4))'
`(declare-fun valout-6-'`I'` () (_ BitVec 1))'
`(declare-fun valout-7-'`I'` () (_ BitVec 1))'
`(declare-fun valout-8-'`I'` () (_ BitVec 1))'
`(declare-fun valout-9-'`I'` () (_ BitVec 1))'
`(declare-fun valout-10-'`I'` () (_ BitVec 1))'
`(declare-fun valout-11-'`I'` () (_ BitVec 1))'
`(declare-fun valout-12-'`I'` () (_ BitVec 1))'
`(declare-fun valout-13-'`I'` () (_ BitVec 1))'
`(declare-fun valout-14-'`I'` () (_ BitVec 1))'
`(declare-fun valout-15-'`I'` () (_ BitVec 1))'
`(declare-fun valout-16-'`I'` () (_ BitVec 1))'
`(declare-fun valout-17-'`I'` () (_ BitVec 1))'
`(declare-fun valout-18-'`I'` () (_ BitVec 1))'
`(declare-fun valout-19-'`I'` () (_ BitVec 1))'
`(declare-fun valout-20-'`I'` () (_ BitVec 4))'
`(declare-fun valout-21-'`I'` () (_ BitVec 4))'
`(declare-fun valout-22-'`I'` () (_ BitVec 4))'
`(declare-fun valout-23-'`I'` () (_ BitVec 4))'
)

forloop(`I',1,ITER,dnl
`(declare-fun sysinxl-'`I'` () (_ BitVec 4))'
`(declare-fun sysinxh-'`I'` () (_ BitVec 4))'
`(declare-fun sysinyl-'`I'` () (_ BitVec 4))'
`(declare-fun sysinyh-'`I'` () (_ BitVec 4))'
`(declare-fun sysout-'`I'` () (_ BitVec 8))'
)

ifdef(`DIST',dnl
forloop(`I',1,NEXT,dnl 
`(declare-fun valina-1-'`I'` () (_ BitVec 8))'
`(declare-fun valina-2-'`I'` () (_ BitVec 4))'
`(declare-fun valina-3-'`I'` () (_ BitVec 4))'
`(declare-fun valina-4-'`I'` () (_ BitVec 4))'
`(declare-fun valina-5-'`I'` () (_ BitVec 4))'
`(declare-fun valina-6-'`I'` () (_ BitVec 4))'
`(declare-fun valina-7-'`I'` () (_ BitVec 4))'
`(declare-fun valina-8-'`I'` () (_ BitVec 1))'
`(declare-fun valina-9-'`I'` () (_ BitVec 1))'
`(declare-fun valina-10-'`I'` () (_ BitVec 1))'
`(declare-fun valina-11-'`I'` () (_ BitVec 1))'
`(declare-fun valina-12-'`I'` () (_ BitVec 1))'
`(declare-fun valina-13-'`I'` () (_ BitVec 1))'
`(declare-fun valina-14-'`I'` () (_ BitVec 1))'
`(declare-fun valina-15-'`I'` () (_ BitVec 1))'
`(declare-fun valina-16-'`I'` () (_ BitVec 4))'
`(declare-fun valina-17-'`I'` () (_ BitVec 4))'
`(declare-fun valina-18-'`I'` () (_ BitVec 1))'
`(declare-fun valina-19-'`I'` () (_ BitVec 1))'
)

`(declare-fun valin-1-NEXT () (_ BitVec 8))'
`(declare-fun valin-2-NEXT () (_ BitVec 4))'
`(declare-fun valin-3-NEXT () (_ BitVec 4))'
`(declare-fun valin-4-NEXT () (_ BitVec 4))'
`(declare-fun valin-5-NEXT () (_ BitVec 4))'
`(declare-fun valin-6-NEXT () (_ BitVec 4))'
`(declare-fun valin-7-NEXT () (_ BitVec 4))'
`(declare-fun valin-8-NEXT () (_ BitVec 1))'
`(declare-fun valin-9-NEXT () (_ BitVec 1))'
`(declare-fun valin-10-NEXT () (_ BitVec 1))'
`(declare-fun valin-11-NEXT () (_ BitVec 1))'
`(declare-fun valin-12-NEXT () (_ BitVec 1))'
`(declare-fun valin-13-NEXT () (_ BitVec 1))'
`(declare-fun valin-14-NEXT () (_ BitVec 1))'
`(declare-fun valin-15-NEXT () (_ BitVec 1))'
`(declare-fun valin-16-NEXT () (_ BitVec 4))'
`(declare-fun valin-17-NEXT () (_ BitVec 4))'
`(declare-fun valin-18-NEXT () (_ BitVec 1))'
`(declare-fun valin-19-NEXT () (_ BitVec 1))'

forloop(`I',1,NEXT,dnl
`(declare-fun valouta-1-'`I'` () (_ BitVec 8))'
`(declare-fun valouta-2-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-3-'`I'` () (_ BitVec 4))'
`(declare-fun valouta-4-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-5-'`I'` () (_ BitVec 4))'
`(declare-fun valouta-6-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-7-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-8-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-9-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-10-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-11-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-12-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-13-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-14-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-15-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-16-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-17-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-18-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-19-'`I'` () (_ BitVec 1))'
`(declare-fun valouta-20-'`I'` () (_ BitVec 4))'
`(declare-fun valouta-21-'`I'` () (_ BitVec 4))'
`(declare-fun valouta-22-'`I'` () (_ BitVec 4))'
`(declare-fun valouta-23-'`I'` () (_ BitVec 4))'
)

`(declare-fun valout-1-NEXT () (_ BitVec 8))'
`(declare-fun valout-2-NEXT () (_ BitVec 1))'
`(declare-fun valout-3-NEXT () (_ BitVec 4))'
`(declare-fun valout-4-NEXT () (_ BitVec 1))'
`(declare-fun valout-5-NEXT () (_ BitVec 4))'
`(declare-fun valout-6-NEXT () (_ BitVec 1))'
`(declare-fun valout-7-NEXT () (_ BitVec 1))'
`(declare-fun valout-8-NEXT () (_ BitVec 1))'
`(declare-fun valout-9-NEXT () (_ BitVec 1))'
`(declare-fun valout-10-NEXT () (_ BitVec 1))'
`(declare-fun valout-11-NEXT () (_ BitVec 1))'
`(declare-fun valout-12-NEXT () (_ BitVec 1))'
`(declare-fun valout-13-NEXT () (_ BitVec 1))'
`(declare-fun valout-14-NEXT () (_ BitVec 1))'
`(declare-fun valout-15-NEXT () (_ BitVec 1))'
`(declare-fun valout-16-NEXT () (_ BitVec 1))'
`(declare-fun valout-17-NEXT () (_ BitVec 1))'
`(declare-fun valout-18-NEXT () (_ BitVec 1))'
`(declare-fun valout-19-NEXT () (_ BitVec 1))'
`(declare-fun valout-20-NEXT () (_ BitVec 4))'
`(declare-fun valout-21-NEXT () (_ BitVec 4))'
`(declare-fun valout-22-NEXT () (_ BitVec 4))'
`(declare-fun valout-23-NEXT () (_ BitVec 4))'
`(declare-fun sysinxl-NEXT () (_ BitVec 4))'
`(declare-fun sysinxh-NEXT () (_ BitVec 4))'
`(declare-fun sysinyl-NEXT () (_ BitVec 4))'
`(declare-fun sysinyh-NEXT () (_ BitVec 4))'
`(declare-fun sysout-NEXT  () (_ BitVec 8))'
`(declare-fun sysouta () (_ BitVec 8))'
)

;----------------------------------------------------------------------------
; Circuit invariants
;----------------------------------------------------------------------------
;
; Circuit ordering. Note this implicitly also says that there are no
; loops (since it imposes some total order properties on output nets). 
; 
(declare-fun loc2 () (_ BitVec NUMCOMPLOG))
(declare-fun loc3 () (_ BitVec NUMCOMPLOG))
(declare-fun loc5 () (_ BitVec NUMCOMPLOG))
(declare-fun loc6 () (_ BitVec NUMCOMPLOG))
(declare-fun loc7 () (_ BitVec NUMCOMPLOG))
(declare-fun loc8 () (_ BitVec NUMCOMPLOG))
(declare-fun loc9 () (_ BitVec NUMCOMPLOG))
(declare-fun loc10 () (_ BitVec NUMCOMPLOG))
(declare-fun loc11 () (_ BitVec NUMCOMPLOG))
(declare-fun loc12 () (_ BitVec NUMCOMPLOG))
(declare-fun loc16 () (_ BitVec NUMCOMPLOG))
(declare-fun loc20 () (_ BitVec NUMCOMPLOG))
(declare-fun loc21 () (_ BitVec NUMCOMPLOG))
(declare-fun loc22 () (_ BitVec NUMCOMPLOG))
(declare-fun loc23 () (_ BitVec NUMCOMPLOG))

; system inputs are before real functional units
(assert (bvult loc20 loc2))  (assert (bvult loc20 loc3))
(assert (bvult loc20 loc5))  (assert (bvult loc20 loc6))
(assert (bvult loc20 loc7))  (assert (bvult loc20 loc8))
(assert (bvult loc20 loc9))  (assert (bvult loc20 loc10))
(assert (bvult loc20 loc11)) (assert (bvult loc20 loc12))
(assert (bvult loc20 loc16))
(assert (bvult loc21 loc2))  (assert (bvult loc21 loc3))
(assert (bvult loc21 loc5))  (assert (bvult loc21 loc6))
(assert (bvult loc21 loc7))  (assert (bvult loc21 loc8))
(assert (bvult loc21 loc9))  (assert (bvult loc21 loc10))
(assert (bvult loc21 loc11)) (assert (bvult loc21 loc12))
(assert (bvult loc21 loc16))
(assert (bvult loc22 loc2))  (assert (bvult loc22 loc3))
(assert (bvult loc22 loc5))  (assert (bvult loc22 loc6))
(assert (bvult loc22 loc7))  (assert (bvult loc22 loc8))
(assert (bvult loc22 loc9))  (assert (bvult loc22 loc10))
(assert (bvult loc22 loc11)) (assert (bvult loc22 loc12))
(assert (bvult loc22 loc16))
(assert (bvult loc23 loc2))  (assert (bvult loc23 loc3))
(assert (bvult loc23 loc5))  (assert (bvult loc23 loc6))
(assert (bvult loc23 loc7))  (assert (bvult loc23 loc8))
(assert (bvult loc23 loc9))  (assert (bvult loc23 loc10))
(assert (bvult loc23 loc11)) (assert (bvult loc23 loc12))
(assert (bvult loc23 loc16))

;
; The axioms here are regular to keep things simple - some are not
; needed since the antecedent of the implication will never happen due
; to type mismatches (other reasons in some special cases). However,
; this part is fundamentally irregular since the functional unit
; associated with an input net is an arbitrary component-dependent map
;not representable in a regular way. 
;

; out* --> in2 
(assert (=> (= in-2 #b00001) (bvult loc2 loc2)))
(assert (=> (= in-2 #b00010) (bvult loc3 loc2)))
(assert (=> (= in-2 #b00011) (bvult loc3 loc2)))
(assert (=> (= in-2 #b00100) (bvult loc5 loc2)))
(assert (=> (= in-2 #b00101) (bvult loc5 loc2)))
(assert (=> (= in-2 #b00110) (bvult loc6 loc2)))
(assert (=> (= in-2 #b00111) (bvult loc7 loc2)))
(assert (=> (= in-2 #b01000) (bvult loc8 loc2)))
(assert (=> (= in-2 #b01001) (bvult loc9 loc2)))
(assert (=> (= in-2 #b01010) (bvult loc10 loc2)))
(assert (=> (= in-2 #b01011) (bvult loc11 loc2)))
(assert (=> (= in-2 #b01100) (bvult loc12 loc2)))
(assert (=> (= in-2 #b01101) (bvult loc12 loc2)))
(assert (=> (= in-2 #b01110) (bvult loc12 loc2)))
(assert (=> (= in-2 #b01111) (bvult loc12 loc2)))
(assert (=> (= in-2 #b10000) (bvult loc16 loc2)))
(assert (=> (= in-2 #b10001) (bvult loc16 loc2)))
(assert (=> (= in-2 #b10010) (bvult loc16 loc2)))
(assert (=> (= in-2 #b10011) (bvult loc16 loc2)))

; out* --> in3
(assert (=> (= in-3 #b00001) (bvult loc2 loc2)))
(assert (=> (= in-3 #b00010) (bvult loc3 loc2)))
(assert (=> (= in-3 #b00011) (bvult loc3 loc2)))
(assert (=> (= in-3 #b00100) (bvult loc5 loc2)))
(assert (=> (= in-3 #b00101) (bvult loc5 loc2)))
(assert (=> (= in-3 #b00110) (bvult loc6 loc2)))
(assert (=> (= in-3 #b00111) (bvult loc7 loc2)))
(assert (=> (= in-3 #b01000) (bvult loc8 loc2)))
(assert (=> (= in-3 #b01001) (bvult loc9 loc2)))
(assert (=> (= in-3 #b01010) (bvult loc10 loc2)))
(assert (=> (= in-3 #b01011) (bvult loc11 loc2)))
(assert (=> (= in-3 #b01100) (bvult loc12 loc2)))
(assert (=> (= in-3 #b01101) (bvult loc12 loc2)))
(assert (=> (= in-3 #b01110) (bvult loc12 loc2)))
(assert (=> (= in-3 #b01111) (bvult loc12 loc2)))
(assert (=> (= in-3 #b10000) (bvult loc16 loc2)))
(assert (=> (= in-3 #b10001) (bvult loc16 loc2)))
(assert (=> (= in-3 #b10010) (bvult loc16 loc2)))
(assert (=> (= in-3 #b10011) (bvult loc16 loc2)))

; out* --> in4
(assert (=> (= in-4 #b00001) (bvult loc2 loc3)))
(assert (=> (= in-4 #b00010) (bvult loc3 loc3)))
(assert (=> (= in-4 #b00011) (bvult loc3 loc3)))
(assert (=> (= in-4 #b00100) (bvult loc5 loc3)))
(assert (=> (= in-4 #b00101) (bvult loc5 loc3)))
(assert (=> (= in-4 #b00110) (bvult loc6 loc3)))
(assert (=> (= in-4 #b00111) (bvult loc7 loc3)))
(assert (=> (= in-4 #b01000) (bvult loc8 loc3)))
(assert (=> (= in-4 #b01001) (bvult loc9 loc3)))
(assert (=> (= in-4 #b01010) (bvult loc10 loc3)))
(assert (=> (= in-4 #b01011) (bvult loc11 loc3)))
(assert (=> (= in-4 #b01100) (bvult loc12 loc3)))
(assert (=> (= in-4 #b01101) (bvult loc12 loc3)))
(assert (=> (= in-4 #b01110) (bvult loc12 loc3)))
(assert (=> (= in-4 #b01111) (bvult loc12 loc3)))
(assert (=> (= in-4 #b10000) (bvult loc16 loc3)))
(assert (=> (= in-4 #b10001) (bvult loc16 loc3)))
(assert (=> (= in-4 #b10010) (bvult loc16 loc3)))
(assert (=> (= in-4 #b10011) (bvult loc16 loc3)))

; out* --> in5
(assert (=> (= in-5 #b00001) (bvult loc2 loc3)))
(assert (=> (= in-5 #b00010) (bvult loc3 loc3)))
(assert (=> (= in-5 #b00011) (bvult loc3 loc3)))
(assert (=> (= in-5 #b00100) (bvult loc5 loc3)))
(assert (=> (= in-5 #b00101) (bvult loc5 loc3)))
(assert (=> (= in-5 #b00110) (bvult loc6 loc3)))
(assert (=> (= in-5 #b00111) (bvult loc7 loc3)))
(assert (=> (= in-5 #b01000) (bvult loc8 loc3)))
(assert (=> (= in-5 #b01001) (bvult loc9 loc3)))
(assert (=> (= in-5 #b01010) (bvult loc10 loc3)))
(assert (=> (= in-5 #b01011) (bvult loc11 loc3)))
(assert (=> (= in-5 #b01100) (bvult loc12 loc3)))
(assert (=> (= in-5 #b01101) (bvult loc12 loc3)))
(assert (=> (= in-5 #b01110) (bvult loc12 loc3)))
(assert (=> (= in-5 #b01111) (bvult loc12 loc3)))
(assert (=> (= in-5 #b10000) (bvult loc16 loc3)))
(assert (=> (= in-5 #b10001) (bvult loc16 loc3)))
(assert (=> (= in-5 #b10010) (bvult loc16 loc3)))
(assert (=> (= in-5 #b10011) (bvult loc16 loc3)))

; out* --> in6
(assert (=> (= in-6 #b00001) (bvult loc2 loc5)))
(assert (=> (= in-6 #b00010) (bvult loc3 loc5)))
(assert (=> (= in-6 #b00011) (bvult loc3 loc5)))
(assert (=> (= in-6 #b00100) (bvult loc5 loc5)))
(assert (=> (= in-6 #b00101) (bvult loc5 loc5)))
(assert (=> (= in-6 #b00110) (bvult loc6 loc5)))
(assert (=> (= in-6 #b00111) (bvult loc7 loc5)))
(assert (=> (= in-6 #b01000) (bvult loc8 loc5)))
(assert (=> (= in-6 #b01001) (bvult loc9 loc5)))
(assert (=> (= in-6 #b01010) (bvult loc10 loc5)))
(assert (=> (= in-6 #b01011) (bvult loc11 loc5)))
(assert (=> (= in-6 #b01100) (bvult loc12 loc5)))
(assert (=> (= in-6 #b01101) (bvult loc12 loc5)))
(assert (=> (= in-6 #b01110) (bvult loc12 loc5)))
(assert (=> (= in-6 #b01111) (bvult loc12 loc5)))
(assert (=> (= in-6 #b10000) (bvult loc16 loc5)))
(assert (=> (= in-6 #b10001) (bvult loc16 loc5)))
(assert (=> (= in-6 #b10010) (bvult loc16 loc5)))
(assert (=> (= in-6 #b10011) (bvult loc16 loc5)))

; out* --> in7
(assert (=> (= in-7 #b00001) (bvult loc2 loc5)))
(assert (=> (= in-7 #b00010) (bvult loc3 loc5)))
(assert (=> (= in-7 #b00011) (bvult loc3 loc5)))
(assert (=> (= in-7 #b00100) (bvult loc5 loc5)))
(assert (=> (= in-7 #b00101) (bvult loc5 loc5)))
(assert (=> (= in-7 #b00110) (bvult loc6 loc5)))
(assert (=> (= in-7 #b00111) (bvult loc7 loc5)))
(assert (=> (= in-7 #b01000) (bvult loc8 loc5)))
(assert (=> (= in-7 #b01001) (bvult loc9 loc5)))
(assert (=> (= in-7 #b01010) (bvult loc10 loc5)))
(assert (=> (= in-7 #b01011) (bvult loc11 loc5)))
(assert (=> (= in-7 #b01100) (bvult loc12 loc5)))
(assert (=> (= in-7 #b01101) (bvult loc12 loc5)))
(assert (=> (= in-7 #b01110) (bvult loc12 loc5)))
(assert (=> (= in-7 #b01111) (bvult loc12 loc5)))
(assert (=> (= in-7 #b10000) (bvult loc16 loc5)))
(assert (=> (= in-7 #b10001) (bvult loc16 loc5)))
(assert (=> (= in-7 #b10010) (bvult loc16 loc5)))
(assert (=> (= in-7 #b10011) (bvult loc16 loc5)))

; out* --> in8
(assert (=> (= in-8 #b00001) (bvult loc2 loc8)))
(assert (=> (= in-8 #b00010) (bvult loc3 loc8)))
(assert (=> (= in-8 #b00011) (bvult loc3 loc8)))
(assert (=> (= in-8 #b00100) (bvult loc5 loc8)))
(assert (=> (= in-8 #b00101) (bvult loc5 loc8)))
(assert (=> (= in-8 #b00110) (bvult loc6 loc8)))
(assert (=> (= in-8 #b00111) (bvult loc7 loc8)))
(assert (=> (= in-8 #b01000) (bvult loc8 loc8)))
(assert (=> (= in-8 #b01001) (bvult loc9 loc8)))
(assert (=> (= in-8 #b01010) (bvult loc10 loc8)))
(assert (=> (= in-8 #b01011) (bvult loc11 loc8)))
(assert (=> (= in-8 #b01100) (bvult loc12 loc8)))
(assert (=> (= in-8 #b01101) (bvult loc12 loc8)))
(assert (=> (= in-8 #b01110) (bvult loc12 loc8)))
(assert (=> (= in-8 #b01111) (bvult loc12 loc8)))
(assert (=> (= in-8 #b10000) (bvult loc16 loc8)))
(assert (=> (= in-8 #b10001) (bvult loc16 loc8)))
(assert (=> (= in-8 #b10010) (bvult loc16 loc8)))
(assert (=> (= in-8 #b10011) (bvult loc16 loc8)))

; out* --> in9
(assert (=> (= in-9 #b00001) (bvult loc2 loc8)))
(assert (=> (= in-9 #b00010) (bvult loc3 loc8)))
(assert (=> (= in-9 #b00011) (bvult loc3 loc8)))
(assert (=> (= in-9 #b00100) (bvult loc5 loc8)))
(assert (=> (= in-9 #b00101) (bvult loc5 loc8)))
(assert (=> (= in-9 #b00110) (bvult loc6 loc8)))
(assert (=> (= in-9 #b00111) (bvult loc7 loc8)))
(assert (=> (= in-9 #b01000) (bvult loc8 loc8)))
(assert (=> (= in-9 #b01001) (bvult loc9 loc8)))
(assert (=> (= in-9 #b01010) (bvult loc10 loc8)))
(assert (=> (= in-9 #b01011) (bvult loc11 loc8)))
(assert (=> (= in-9 #b01100) (bvult loc12 loc8)))
(assert (=> (= in-9 #b01101) (bvult loc12 loc8)))
(assert (=> (= in-9 #b01110) (bvult loc12 loc8)))
(assert (=> (= in-9 #b01111) (bvult loc12 loc8)))
(assert (=> (= in-9 #b10000) (bvult loc16 loc8)))
(assert (=> (= in-9 #b10001) (bvult loc16 loc8)))
(assert (=> (= in-9 #b10010) (bvult loc16 loc8)))
(assert (=> (= in-9 #b10011) (bvult loc16 loc8)))

; out* --> in10
(assert (=> (= in-10 #b00001) (bvult loc2 loc9)))
(assert (=> (= in-10 #b00010) (bvult loc3 loc9)))
(assert (=> (= in-10 #b00011) (bvult loc3 loc9)))
(assert (=> (= in-10 #b00100) (bvult loc5 loc9)))
(assert (=> (= in-10 #b00101) (bvult loc5 loc9)))
(assert (=> (= in-10 #b00110) (bvult loc6 loc9)))
(assert (=> (= in-10 #b00111) (bvult loc7 loc9)))
(assert (=> (= in-10 #b01000) (bvult loc8 loc9)))
(assert (=> (= in-10 #b01001) (bvult loc9 loc9)))
(assert (=> (= in-10 #b01010) (bvult loc10 loc9)))
(assert (=> (= in-10 #b01011) (bvult loc11 loc9)))
(assert (=> (= in-10 #b01100) (bvult loc12 loc9)))
(assert (=> (= in-10 #b01101) (bvult loc12 loc9)))
(assert (=> (= in-10 #b01110) (bvult loc12 loc9)))
(assert (=> (= in-10 #b01111) (bvult loc12 loc9)))
(assert (=> (= in-10 #b10000) (bvult loc16 loc9)))
(assert (=> (= in-10 #b10001) (bvult loc16 loc9)))
(assert (=> (= in-10 #b10010) (bvult loc16 loc9)))
(assert (=> (= in-10 #b10011) (bvult loc16 loc9)))

; out* --> in11
(assert (=> (= in-11 #b00001) (bvult loc2 loc9)))
(assert (=> (= in-11 #b00010) (bvult loc3 loc9)))
(assert (=> (= in-11 #b00011) (bvult loc3 loc9)))
(assert (=> (= in-11 #b00100) (bvult loc5 loc9)))
(assert (=> (= in-11 #b00101) (bvult loc5 loc9)))
(assert (=> (= in-11 #b00110) (bvult loc6 loc9)))
(assert (=> (= in-11 #b00111) (bvult loc7 loc9)))
(assert (=> (= in-11 #b01000) (bvult loc8 loc9)))
(assert (=> (= in-11 #b01001) (bvult loc9 loc9)))
(assert (=> (= in-11 #b01010) (bvult loc10 loc9)))
(assert (=> (= in-11 #b01011) (bvult loc11 loc9)))
(assert (=> (= in-11 #b01100) (bvult loc12 loc9)))
(assert (=> (= in-11 #b01101) (bvult loc12 loc9)))
(assert (=> (= in-11 #b01110) (bvult loc12 loc9)))
(assert (=> (= in-11 #b01111) (bvult loc12 loc9)))
(assert (=> (= in-11 #b10000) (bvult loc16 loc9)))
(assert (=> (= in-11 #b10001) (bvult loc16 loc9)))
(assert (=> (= in-11 #b10010) (bvult loc16 loc9)))
(assert (=> (= in-11 #b10011) (bvult loc16 loc9)))

; out* --> in12
(assert (=> (= in-12 #b00001) (bvult loc2 loc10)))
(assert (=> (= in-12 #b00010) (bvult loc3 loc10)))
(assert (=> (= in-12 #b00011) (bvult loc3 loc10)))
(assert (=> (= in-12 #b00100) (bvult loc5 loc10)))
(assert (=> (= in-12 #b00101) (bvult loc5 loc10)))
(assert (=> (= in-12 #b00110) (bvult loc6 loc10)))
(assert (=> (= in-12 #b00111) (bvult loc7 loc10)))
(assert (=> (= in-12 #b01000) (bvult loc8 loc10)))
(assert (=> (= in-12 #b01001) (bvult loc9 loc10)))
(assert (=> (= in-12 #b01010) (bvult loc10 loc10)))
(assert (=> (= in-12 #b01011) (bvult loc11 loc10)))
(assert (=> (= in-12 #b01100) (bvult loc12 loc10)))
(assert (=> (= in-12 #b01101) (bvult loc12 loc10)))
(assert (=> (= in-12 #b01110) (bvult loc12 loc10)))
(assert (=> (= in-12 #b01111) (bvult loc12 loc10)))
(assert (=> (= in-12 #b10000) (bvult loc16 loc10)))
(assert (=> (= in-12 #b10001) (bvult loc16 loc10)))
(assert (=> (= in-12 #b10010) (bvult loc16 loc10)))
(assert (=> (= in-12 #b10011) (bvult loc16 loc10)))

; out* --> in13
(assert (=> (= in-13 #b00001) (bvult loc2 loc10)))
(assert (=> (= in-13 #b00010) (bvult loc3 loc10)))
(assert (=> (= in-13 #b00011) (bvult loc3 loc10)))
(assert (=> (= in-13 #b00100) (bvult loc5 loc10)))
(assert (=> (= in-13 #b00101) (bvult loc5 loc10)))
(assert (=> (= in-13 #b00110) (bvult loc6 loc10)))
(assert (=> (= in-13 #b00111) (bvult loc7 loc10)))
(assert (=> (= in-13 #b01000) (bvult loc8 loc10)))
(assert (=> (= in-13 #b01001) (bvult loc9 loc10)))
(assert (=> (= in-13 #b01010) (bvult loc10 loc10)))
(assert (=> (= in-13 #b01011) (bvult loc11 loc10)))
(assert (=> (= in-13 #b01100) (bvult loc12 loc10)))
(assert (=> (= in-13 #b01101) (bvult loc12 loc10)))
(assert (=> (= in-13 #b01110) (bvult loc12 loc10)))
(assert (=> (= in-13 #b01111) (bvult loc12 loc10)))
(assert (=> (= in-13 #b10000) (bvult loc16 loc10)))
(assert (=> (= in-13 #b10001) (bvult loc16 loc10)))
(assert (=> (= in-13 #b10010) (bvult loc16 loc10)))
(assert (=> (= in-13 #b10011) (bvult loc16 loc10)))

; out* --> in14
(assert (=> (= in-14 #b00001) (bvult loc2 loc11)))
(assert (=> (= in-14 #b00010) (bvult loc3 loc11)))
(assert (=> (= in-14 #b00011) (bvult loc3 loc11)))
(assert (=> (= in-14 #b00100) (bvult loc5 loc11)))
(assert (=> (= in-14 #b00101) (bvult loc5 loc11)))
(assert (=> (= in-14 #b00110) (bvult loc6 loc11)))
(assert (=> (= in-14 #b00111) (bvult loc7 loc11)))
(assert (=> (= in-14 #b01000) (bvult loc8 loc11)))
(assert (=> (= in-14 #b01001) (bvult loc9 loc11)))
(assert (=> (= in-14 #b01010) (bvult loc10 loc11)))
(assert (=> (= in-14 #b01011) (bvult loc11 loc11)))
(assert (=> (= in-14 #b01100) (bvult loc12 loc11)))
(assert (=> (= in-14 #b01101) (bvult loc12 loc11)))
(assert (=> (= in-14 #b01110) (bvult loc12 loc11)))
(assert (=> (= in-14 #b01111) (bvult loc12 loc11)))
(assert (=> (= in-14 #b10000) (bvult loc16 loc11)))
(assert (=> (= in-14 #b10001) (bvult loc16 loc11)))
(assert (=> (= in-14 #b10010) (bvult loc16 loc11)))
(assert (=> (= in-14 #b10011) (bvult loc16 loc11)))

; out* --> in15
(assert (=> (= in-15 #b00001) (bvult loc2 loc11)))
(assert (=> (= in-15 #b00010) (bvult loc3 loc11)))
(assert (=> (= in-15 #b00011) (bvult loc3 loc11)))
(assert (=> (= in-15 #b00100) (bvult loc5 loc11)))
(assert (=> (= in-15 #b00101) (bvult loc5 loc11)))
(assert (=> (= in-15 #b00110) (bvult loc6 loc11)))
(assert (=> (= in-15 #b00111) (bvult loc7 loc11)))
(assert (=> (= in-15 #b01000) (bvult loc8 loc11)))
(assert (=> (= in-15 #b01001) (bvult loc9 loc11)))
(assert (=> (= in-15 #b01010) (bvult loc10 loc11)))
(assert (=> (= in-15 #b01011) (bvult loc11 loc11)))
(assert (=> (= in-15 #b01100) (bvult loc12 loc11)))
(assert (=> (= in-15 #b01101) (bvult loc12 loc11)))
(assert (=> (= in-15 #b01110) (bvult loc12 loc11)))
(assert (=> (= in-15 #b01111) (bvult loc12 loc11)))
(assert (=> (= in-15 #b10000) (bvult loc16 loc11)))
(assert (=> (= in-15 #b10001) (bvult loc16 loc11)))
(assert (=> (= in-15 #b10010) (bvult loc16 loc11)))
(assert (=> (= in-15 #b10011) (bvult loc16 loc11)))

; out* --> in16
(assert (=> (= in-16 #b00001) (bvult loc2 loc12)))
(assert (=> (= in-16 #b00010) (bvult loc3 loc12)))
(assert (=> (= in-16 #b00011) (bvult loc3 loc12)))
(assert (=> (= in-16 #b00100) (bvult loc5 loc12)))
(assert (=> (= in-16 #b00101) (bvult loc5 loc12)))
(assert (=> (= in-16 #b00110) (bvult loc6 loc12)))
(assert (=> (= in-16 #b00111) (bvult loc7 loc12)))
(assert (=> (= in-16 #b01000) (bvult loc8 loc12)))
(assert (=> (= in-16 #b01001) (bvult loc9 loc12)))
(assert (=> (= in-16 #b01010) (bvult loc10 loc12)))
(assert (=> (= in-16 #b01011) (bvult loc11 loc12)))
(assert (=> (= in-16 #b01100) (bvult loc12 loc12)))
(assert (=> (= in-16 #b01101) (bvult loc12 loc12)))
(assert (=> (= in-16 #b01110) (bvult loc12 loc12)))
(assert (=> (= in-16 #b01111) (bvult loc12 loc12)))
(assert (=> (= in-16 #b10000) (bvult loc16 loc12)))
(assert (=> (= in-16 #b10001) (bvult loc16 loc12)))
(assert (=> (= in-16 #b10010) (bvult loc16 loc12)))
(assert (=> (= in-16 #b10011) (bvult loc16 loc12)))

; out* --> in17
(assert (=> (= in-17 #b00001) (bvult loc2 loc16)))
(assert (=> (= in-17 #b00010) (bvult loc3 loc16)))
(assert (=> (= in-17 #b00011) (bvult loc3 loc16)))
(assert (=> (= in-17 #b00100) (bvult loc5 loc16)))
(assert (=> (= in-17 #b00101) (bvult loc5 loc16)))
(assert (=> (= in-17 #b00110) (bvult loc6 loc16)))
(assert (=> (= in-17 #b00111) (bvult loc7 loc16)))
(assert (=> (= in-17 #b01000) (bvult loc8 loc16)))
(assert (=> (= in-17 #b01001) (bvult loc9 loc16)))
(assert (=> (= in-17 #b01010) (bvult loc10 loc16)))
(assert (=> (= in-17 #b01011) (bvult loc11 loc16)))
(assert (=> (= in-17 #b01100) (bvult loc12 loc16)))
(assert (=> (= in-17 #b01101) (bvult loc12 loc16)))
(assert (=> (= in-17 #b01110) (bvult loc12 loc16)))
(assert (=> (= in-17 #b01111) (bvult loc12 loc16)))
(assert (=> (= in-17 #b10000) (bvult loc16 loc16)))
(assert (=> (= in-17 #b10001) (bvult loc16 loc16)))
(assert (=> (= in-17 #b10010) (bvult loc16 loc16)))
(assert (=> (= in-17 #b10011) (bvult loc16 loc16)))

; out* --> in18
(assert (=> (= in-18 #b00001) (bvult loc2 loc3)))
(assert (=> (= in-18 #b00010) (bvult loc3 loc3)))
(assert (=> (= in-18 #b00011) (bvult loc3 loc3)))
(assert (=> (= in-18 #b00100) (bvult loc5 loc3)))
(assert (=> (= in-18 #b00101) (bvult loc5 loc3)))
(assert (=> (= in-18 #b00110) (bvult loc6 loc3)))
(assert (=> (= in-18 #b00111) (bvult loc7 loc3)))
(assert (=> (= in-18 #b01000) (bvult loc8 loc3)))
(assert (=> (= in-18 #b01001) (bvult loc9 loc3)))
(assert (=> (= in-18 #b01010) (bvult loc10 loc3)))
(assert (=> (= in-18 #b01011) (bvult loc11 loc3)))
(assert (=> (= in-18 #b01100) (bvult loc12 loc3)))
(assert (=> (= in-18 #b01101) (bvult loc12 loc3)))
(assert (=> (= in-18 #b01110) (bvult loc12 loc3)))
(assert (=> (= in-18 #b01111) (bvult loc12 loc3)))
(assert (=> (= in-18 #b10000) (bvult loc16 loc3)))
(assert (=> (= in-18 #b10001) (bvult loc16 loc3)))
(assert (=> (= in-18 #b10010) (bvult loc16 loc3)))
(assert (=> (= in-18 #b10011) (bvult loc16 loc3)))

; out* --> in19
(assert (=> (= in-19 #b00001) (bvult loc2 loc5)))
(assert (=> (= in-19 #b00010) (bvult loc3 loc5)))
(assert (=> (= in-19 #b00011) (bvult loc3 loc5)))
(assert (=> (= in-19 #b00100) (bvult loc5 loc5)))
(assert (=> (= in-19 #b00101) (bvult loc5 loc5)))
(assert (=> (= in-19 #b00110) (bvult loc6 loc5)))
(assert (=> (= in-19 #b00111) (bvult loc7 loc5)))
(assert (=> (= in-19 #b01000) (bvult loc8 loc5)))
(assert (=> (= in-19 #b01001) (bvult loc9 loc5)))
(assert (=> (= in-19 #b01010) (bvult loc10 loc5)))
(assert (=> (= in-19 #b01011) (bvult loc11 loc5)))
(assert (=> (= in-19 #b01100) (bvult loc12 loc5)))
(assert (=> (= in-19 #b01101) (bvult loc12 loc5)))
(assert (=> (= in-19 #b01110) (bvult loc12 loc5)))
(assert (=> (= in-19 #b01111) (bvult loc12 loc5)))
(assert (=> (= in-19 #b10000) (bvult loc16 loc5)))
(assert (=> (= in-19 #b10001) (bvult loc16 loc5)))
(assert (=> (= in-19 #b10010) (bvult loc16 loc5)))
(assert (=> (= in-19 #b10011) (bvult loc16 loc5)))

; Copy of above with in-->ina loc-->loca 
ifdef(`DIST',dnl
;
; Circuit ordering. Note this implicitly also says that there are no
; loops (since it imposes some total order properties on output nets). 
; 
(declare-fun loca2 () (_ BitVec NUMCOMPLOG))
(declare-fun loca3 () (_ BitVec NUMCOMPLOG))
(declare-fun loca5 () (_ BitVec NUMCOMPLOG))
(declare-fun loca6 () (_ BitVec NUMCOMPLOG))
(declare-fun loca7 () (_ BitVec NUMCOMPLOG))
(declare-fun loca8 () (_ BitVec NUMCOMPLOG))
(declare-fun loca9 () (_ BitVec NUMCOMPLOG))
(declare-fun loca10 () (_ BitVec NUMCOMPLOG))
(declare-fun loca11 () (_ BitVec NUMCOMPLOG))
(declare-fun loca12 () (_ BitVec NUMCOMPLOG))
(declare-fun loca16 () (_ BitVec NUMCOMPLOG))
(declare-fun loca20 () (_ BitVec NUMCOMPLOG))
(declare-fun loca21 () (_ BitVec NUMCOMPLOG))
(declare-fun loca22 () (_ BitVec NUMCOMPLOG))
(declare-fun loca23 () (_ BitVec NUMCOMPLOG))

; system inputs are before real functional units
(assert (bvult loca20 loca2))  (assert (bvult loca20 loca3))
(assert (bvult loca20 loca5))  (assert (bvult loca20 loca6))
(assert (bvult loca20 loca7))  (assert (bvult loca20 loca8))
(assert (bvult loca20 loca9))  (assert (bvult loca20 loca10))
(assert (bvult loca20 loca11)) (assert (bvult loca20 loca12))
(assert (bvult loca20 loca16))
(assert (bvult loca21 loca2))  (assert (bvult loca21 loca3))
(assert (bvult loca21 loca5))  (assert (bvult loca21 loca6))
(assert (bvult loca21 loca7))  (assert (bvult loca21 loca8))
(assert (bvult loca21 loca9))  (assert (bvult loca21 loca10))
(assert (bvult loca21 loca11)) (assert (bvult loca21 loca12))
(assert (bvult loca21 loca16))
(assert (bvult loca22 loca2))  (assert (bvult loca22 loca3))
(assert (bvult loca22 loca5))  (assert (bvult loca22 loca6))
(assert (bvult loca22 loca7))  (assert (bvult loca22 loca8))
(assert (bvult loca22 loca9))  (assert (bvult loca22 loca10))
(assert (bvult loca22 loca11)) (assert (bvult loca22 loca12))
(assert (bvult loca22 loca16))
(assert (bvult loca23 loca2))  (assert (bvult loca23 loca3))
(assert (bvult loca23 loca5))  (assert (bvult loca23 loca6))
(assert (bvult loca23 loca7))  (assert (bvult loca23 loca8))
(assert (bvult loca23 loca9))  (assert (bvult loca23 loca10))
(assert (bvult loca23 loca11)) (assert (bvult loca23 loca12))
(assert (bvult loca23 loca16))

;
; The axioms here are regular to keep things simple - some are not
; needed since the antecedent of the implication will never happen due
; to type mismatches (other reasons in some special cases).
;

; out* --> in2 
(assert (=> (= ina-2 #b00001) (bvult loca2 loca2)))
(assert (=> (= ina-2 #b00010) (bvult loca3 loca2)))
(assert (=> (= ina-2 #b00011) (bvult loca3 loca2)))
(assert (=> (= ina-2 #b00100) (bvult loca5 loca2)))
(assert (=> (= ina-2 #b00101) (bvult loca5 loca2)))
(assert (=> (= ina-2 #b00110) (bvult loca6 loca2)))
(assert (=> (= ina-2 #b00111) (bvult loca7 loca2)))
(assert (=> (= ina-2 #b01000) (bvult loca8 loca2)))
(assert (=> (= ina-2 #b01001) (bvult loca9 loca2)))
(assert (=> (= ina-2 #b01010) (bvult loca10 loca2)))
(assert (=> (= ina-2 #b01011) (bvult loca11 loca2)))
(assert (=> (= ina-2 #b01100) (bvult loca12 loca2)))
(assert (=> (= ina-2 #b01101) (bvult loca12 loca2)))
(assert (=> (= ina-2 #b01110) (bvult loca12 loca2)))
(assert (=> (= ina-2 #b01111) (bvult loca12 loca2)))
(assert (=> (= ina-2 #b10000) (bvult loca16 loca2)))
(assert (=> (= ina-2 #b10001) (bvult loca16 loca2)))
(assert (=> (= ina-2 #b10010) (bvult loca16 loca2)))
(assert (=> (= ina-2 #b10011) (bvult loca16 loca2)))

; out* --> in3
(assert (=> (= ina-3 #b00001) (bvult loca2 loca2)))
(assert (=> (= ina-3 #b00010) (bvult loca3 loca2)))
(assert (=> (= ina-3 #b00011) (bvult loca3 loca2)))
(assert (=> (= ina-3 #b00100) (bvult loca5 loca2)))
(assert (=> (= ina-3 #b00101) (bvult loca5 loca2)))
(assert (=> (= ina-3 #b00110) (bvult loca6 loca2)))
(assert (=> (= ina-3 #b00111) (bvult loca7 loca2)))
(assert (=> (= ina-3 #b01000) (bvult loca8 loca2)))
(assert (=> (= ina-3 #b01001) (bvult loca9 loca2)))
(assert (=> (= ina-3 #b01010) (bvult loca10 loca2)))
(assert (=> (= ina-3 #b01011) (bvult loca11 loca2)))
(assert (=> (= ina-3 #b01100) (bvult loca12 loca2)))
(assert (=> (= ina-3 #b01101) (bvult loca12 loca2)))
(assert (=> (= ina-3 #b01110) (bvult loca12 loca2)))
(assert (=> (= ina-3 #b01111) (bvult loca12 loca2)))
(assert (=> (= ina-3 #b10000) (bvult loca16 loca2)))
(assert (=> (= ina-3 #b10001) (bvult loca16 loca2)))
(assert (=> (= ina-3 #b10010) (bvult loca16 loca2)))
(assert (=> (= ina-3 #b10011) (bvult loca16 loca2)))

; out* --> in4
(assert (=> (= ina-4 #b00001) (bvult loca2 loca3)))
(assert (=> (= ina-4 #b00010) (bvult loca3 loca3)))
(assert (=> (= ina-4 #b00011) (bvult loca3 loca3)))
(assert (=> (= ina-4 #b00100) (bvult loca5 loca3)))
(assert (=> (= ina-4 #b00101) (bvult loca5 loca3)))
(assert (=> (= ina-4 #b00110) (bvult loca6 loca3)))
(assert (=> (= ina-4 #b00111) (bvult loca7 loca3)))
(assert (=> (= ina-4 #b01000) (bvult loca8 loca3)))
(assert (=> (= ina-4 #b01001) (bvult loca9 loca3)))
(assert (=> (= ina-4 #b01010) (bvult loca10 loca3)))
(assert (=> (= ina-4 #b01011) (bvult loca11 loca3)))
(assert (=> (= ina-4 #b01100) (bvult loca12 loca3)))
(assert (=> (= ina-4 #b01101) (bvult loca12 loca3)))
(assert (=> (= ina-4 #b01110) (bvult loca12 loca3)))
(assert (=> (= ina-4 #b01111) (bvult loca12 loca3)))
(assert (=> (= ina-4 #b10000) (bvult loca16 loca3)))
(assert (=> (= ina-4 #b10001) (bvult loca16 loca3)))
(assert (=> (= ina-4 #b10010) (bvult loca16 loca3)))
(assert (=> (= ina-4 #b10011) (bvult loca16 loca3)))

; out* --> in5
(assert (=> (= ina-5 #b00001) (bvult loca2 loca3)))
(assert (=> (= ina-5 #b00010) (bvult loca3 loca3)))
(assert (=> (= ina-5 #b00011) (bvult loca3 loca3)))
(assert (=> (= ina-5 #b00100) (bvult loca5 loca3)))
(assert (=> (= ina-5 #b00101) (bvult loca5 loca3)))
(assert (=> (= ina-5 #b00110) (bvult loca6 loca3)))
(assert (=> (= ina-5 #b00111) (bvult loca7 loca3)))
(assert (=> (= ina-5 #b01000) (bvult loca8 loca3)))
(assert (=> (= ina-5 #b01001) (bvult loca9 loca3)))
(assert (=> (= ina-5 #b01010) (bvult loca10 loca3)))
(assert (=> (= ina-5 #b01011) (bvult loca11 loca3)))
(assert (=> (= ina-5 #b01100) (bvult loca12 loca3)))
(assert (=> (= ina-5 #b01101) (bvult loca12 loca3)))
(assert (=> (= ina-5 #b01110) (bvult loca12 loca3)))
(assert (=> (= ina-5 #b01111) (bvult loca12 loca3)))
(assert (=> (= ina-5 #b10000) (bvult loca16 loca3)))
(assert (=> (= ina-5 #b10001) (bvult loca16 loca3)))
(assert (=> (= ina-5 #b10010) (bvult loca16 loca3)))
(assert (=> (= ina-5 #b10011) (bvult loca16 loca3)))

; out* --> in6
(assert (=> (= ina-6 #b00001) (bvult loca2 loca5)))
(assert (=> (= ina-6 #b00010) (bvult loca3 loca5)))
(assert (=> (= ina-6 #b00011) (bvult loca3 loca5)))
(assert (=> (= ina-6 #b00100) (bvult loca5 loca5)))
(assert (=> (= ina-6 #b00101) (bvult loca5 loca5)))
(assert (=> (= ina-6 #b00110) (bvult loca6 loca5)))
(assert (=> (= ina-6 #b00111) (bvult loca7 loca5)))
(assert (=> (= ina-6 #b01000) (bvult loca8 loca5)))
(assert (=> (= ina-6 #b01001) (bvult loca9 loca5)))
(assert (=> (= ina-6 #b01010) (bvult loca10 loca5)))
(assert (=> (= ina-6 #b01011) (bvult loca11 loca5)))
(assert (=> (= ina-6 #b01100) (bvult loca12 loca5)))
(assert (=> (= ina-6 #b01101) (bvult loca12 loca5)))
(assert (=> (= ina-6 #b01110) (bvult loca12 loca5)))
(assert (=> (= ina-6 #b01111) (bvult loca12 loca5)))
(assert (=> (= ina-6 #b10000) (bvult loca16 loca5)))
(assert (=> (= ina-6 #b10001) (bvult loca16 loca5)))
(assert (=> (= ina-6 #b10010) (bvult loca16 loca5)))
(assert (=> (= ina-6 #b10011) (bvult loca16 loca5)))

; out* --> in7
(assert (=> (= ina-7 #b00001) (bvult loca2 loca5)))
(assert (=> (= ina-7 #b00010) (bvult loca3 loca5)))
(assert (=> (= ina-7 #b00011) (bvult loca3 loca5)))
(assert (=> (= ina-7 #b00100) (bvult loca5 loca5)))
(assert (=> (= ina-7 #b00101) (bvult loca5 loca5)))
(assert (=> (= ina-7 #b00110) (bvult loca6 loca5)))
(assert (=> (= ina-7 #b00111) (bvult loca7 loca5)))
(assert (=> (= ina-7 #b01000) (bvult loca8 loca5)))
(assert (=> (= ina-7 #b01001) (bvult loca9 loca5)))
(assert (=> (= ina-7 #b01010) (bvult loca10 loca5)))
(assert (=> (= ina-7 #b01011) (bvult loca11 loca5)))
(assert (=> (= ina-7 #b01100) (bvult loca12 loca5)))
(assert (=> (= ina-7 #b01101) (bvult loca12 loca5)))
(assert (=> (= ina-7 #b01110) (bvult loca12 loca5)))
(assert (=> (= ina-7 #b01111) (bvult loca12 loca5)))
(assert (=> (= ina-7 #b10000) (bvult loca16 loca5)))
(assert (=> (= ina-7 #b10001) (bvult loca16 loca5)))
(assert (=> (= ina-7 #b10010) (bvult loca16 loca5)))
(assert (=> (= ina-7 #b10011) (bvult loca16 loca5)))

; out* --> in8
(assert (=> (= ina-8 #b00001) (bvult loca2 loca8)))
(assert (=> (= ina-8 #b00010) (bvult loca3 loca8)))
(assert (=> (= ina-8 #b00011) (bvult loca3 loca8)))
(assert (=> (= ina-8 #b00100) (bvult loca5 loca8)))
(assert (=> (= ina-8 #b00101) (bvult loca5 loca8)))
(assert (=> (= ina-8 #b00110) (bvult loca6 loca8)))
(assert (=> (= ina-8 #b00111) (bvult loca7 loca8)))
(assert (=> (= ina-8 #b01000) (bvult loca8 loca8)))
(assert (=> (= ina-8 #b01001) (bvult loca9 loca8)))
(assert (=> (= ina-8 #b01010) (bvult loca10 loca8)))
(assert (=> (= ina-8 #b01011) (bvult loca11 loca8)))
(assert (=> (= ina-8 #b01100) (bvult loca12 loca8)))
(assert (=> (= ina-8 #b01101) (bvult loca12 loca8)))
(assert (=> (= ina-8 #b01110) (bvult loca12 loca8)))
(assert (=> (= ina-8 #b01111) (bvult loca12 loca8)))
(assert (=> (= ina-8 #b10000) (bvult loca16 loca8)))
(assert (=> (= ina-8 #b10001) (bvult loca16 loca8)))
(assert (=> (= ina-8 #b10010) (bvult loca16 loca8)))
(assert (=> (= ina-8 #b10011) (bvult loca16 loca8)))

; out* --> in9
(assert (=> (= ina-9 #b00001) (bvult loca2 loca8)))
(assert (=> (= ina-9 #b00010) (bvult loca3 loca8)))
(assert (=> (= ina-9 #b00011) (bvult loca3 loca8)))
(assert (=> (= ina-9 #b00100) (bvult loca5 loca8)))
(assert (=> (= ina-9 #b00101) (bvult loca5 loca8)))
(assert (=> (= ina-9 #b00110) (bvult loca6 loca8)))
(assert (=> (= ina-9 #b00111) (bvult loca7 loca8)))
(assert (=> (= ina-9 #b01000) (bvult loca8 loca8)))
(assert (=> (= ina-9 #b01001) (bvult loca9 loca8)))
(assert (=> (= ina-9 #b01010) (bvult loca10 loca8)))
(assert (=> (= ina-9 #b01011) (bvult loca11 loca8)))
(assert (=> (= ina-9 #b01100) (bvult loca12 loca8)))
(assert (=> (= ina-9 #b01101) (bvult loca12 loca8)))
(assert (=> (= ina-9 #b01110) (bvult loca12 loca8)))
(assert (=> (= ina-9 #b01111) (bvult loca12 loca8)))
(assert (=> (= ina-9 #b10000) (bvult loca16 loca8)))
(assert (=> (= ina-9 #b10001) (bvult loca16 loca8)))
(assert (=> (= ina-9 #b10010) (bvult loca16 loca8)))
(assert (=> (= ina-9 #b10011) (bvult loca16 loca8)))

; out* --> in10
(assert (=> (= ina-10 #b00001) (bvult loca2 loca9)))
(assert (=> (= ina-10 #b00010) (bvult loca3 loca9)))
(assert (=> (= ina-10 #b00011) (bvult loca3 loca9)))
(assert (=> (= ina-10 #b00100) (bvult loca5 loca9)))
(assert (=> (= ina-10 #b00101) (bvult loca5 loca9)))
(assert (=> (= ina-10 #b00110) (bvult loca6 loca9)))
(assert (=> (= ina-10 #b00111) (bvult loca7 loca9)))
(assert (=> (= ina-10 #b01000) (bvult loca8 loca9)))
(assert (=> (= ina-10 #b01001) (bvult loca9 loca9)))
(assert (=> (= ina-10 #b01010) (bvult loca10 loca9)))
(assert (=> (= ina-10 #b01011) (bvult loca11 loca9)))
(assert (=> (= ina-10 #b01100) (bvult loca12 loca9)))
(assert (=> (= ina-10 #b01101) (bvult loca12 loca9)))
(assert (=> (= ina-10 #b01110) (bvult loca12 loca9)))
(assert (=> (= ina-10 #b01111) (bvult loca12 loca9)))
(assert (=> (= ina-10 #b10000) (bvult loca16 loca9)))
(assert (=> (= ina-10 #b10001) (bvult loca16 loca9)))
(assert (=> (= ina-10 #b10010) (bvult loca16 loca9)))
(assert (=> (= ina-10 #b10011) (bvult loca16 loca9)))

; out* --> in11
(assert (=> (= ina-11 #b00001) (bvult loca2 loca9)))
(assert (=> (= ina-11 #b00010) (bvult loca3 loca9)))
(assert (=> (= ina-11 #b00011) (bvult loca3 loca9)))
(assert (=> (= ina-11 #b00100) (bvult loca5 loca9)))
(assert (=> (= ina-11 #b00101) (bvult loca5 loca9)))
(assert (=> (= ina-11 #b00110) (bvult loca6 loca9)))
(assert (=> (= ina-11 #b00111) (bvult loca7 loca9)))
(assert (=> (= ina-11 #b01000) (bvult loca8 loca9)))
(assert (=> (= ina-11 #b01001) (bvult loca9 loca9)))
(assert (=> (= ina-11 #b01010) (bvult loca10 loca9)))
(assert (=> (= ina-11 #b01011) (bvult loca11 loca9)))
(assert (=> (= ina-11 #b01100) (bvult loca12 loca9)))
(assert (=> (= ina-11 #b01101) (bvult loca12 loca9)))
(assert (=> (= ina-11 #b01110) (bvult loca12 loca9)))
(assert (=> (= ina-11 #b01111) (bvult loca12 loca9)))
(assert (=> (= ina-11 #b10000) (bvult loca16 loca9)))
(assert (=> (= ina-11 #b10001) (bvult loca16 loca9)))
(assert (=> (= ina-11 #b10010) (bvult loca16 loca9)))
(assert (=> (= ina-11 #b10011) (bvult loca16 loca9)))

; out* --> in12
(assert (=> (= ina-12 #b00001) (bvult loca2 loca10)))
(assert (=> (= ina-12 #b00010) (bvult loca3 loca10)))
(assert (=> (= ina-12 #b00011) (bvult loca3 loca10)))
(assert (=> (= ina-12 #b00100) (bvult loca5 loca10)))
(assert (=> (= ina-12 #b00101) (bvult loca5 loca10)))
(assert (=> (= ina-12 #b00110) (bvult loca6 loca10)))
(assert (=> (= ina-12 #b00111) (bvult loca7 loca10)))
(assert (=> (= ina-12 #b01000) (bvult loca8 loca10)))
(assert (=> (= ina-12 #b01001) (bvult loca9 loca10)))
(assert (=> (= ina-12 #b01010) (bvult loca10 loca10)))
(assert (=> (= ina-12 #b01011) (bvult loca11 loca10)))
(assert (=> (= ina-12 #b01100) (bvult loca12 loca10)))
(assert (=> (= ina-12 #b01101) (bvult loca12 loca10)))
(assert (=> (= ina-12 #b01110) (bvult loca12 loca10)))
(assert (=> (= ina-12 #b01111) (bvult loca12 loca10)))
(assert (=> (= ina-12 #b10000) (bvult loca16 loca10)))
(assert (=> (= ina-12 #b10001) (bvult loca16 loca10)))
(assert (=> (= ina-12 #b10010) (bvult loca16 loca10)))
(assert (=> (= ina-12 #b10011) (bvult loca16 loca10)))

; out* --> in13
(assert (=> (= ina-13 #b00001) (bvult loca2 loca10)))
(assert (=> (= ina-13 #b00010) (bvult loca3 loca10)))
(assert (=> (= ina-13 #b00011) (bvult loca3 loca10)))
(assert (=> (= ina-13 #b00100) (bvult loca5 loca10)))
(assert (=> (= ina-13 #b00101) (bvult loca5 loca10)))
(assert (=> (= ina-13 #b00110) (bvult loca6 loca10)))
(assert (=> (= ina-13 #b00111) (bvult loca7 loca10)))
(assert (=> (= ina-13 #b01000) (bvult loca8 loca10)))
(assert (=> (= ina-13 #b01001) (bvult loca9 loca10)))
(assert (=> (= ina-13 #b01010) (bvult loca10 loca10)))
(assert (=> (= ina-13 #b01011) (bvult loca11 loca10)))
(assert (=> (= ina-13 #b01100) (bvult loca12 loca10)))
(assert (=> (= ina-13 #b01101) (bvult loca12 loca10)))
(assert (=> (= ina-13 #b01110) (bvult loca12 loca10)))
(assert (=> (= ina-13 #b01111) (bvult loca12 loca10)))
(assert (=> (= ina-13 #b10000) (bvult loca16 loca10)))
(assert (=> (= ina-13 #b10001) (bvult loca16 loca10)))
(assert (=> (= ina-13 #b10010) (bvult loca16 loca10)))
(assert (=> (= ina-13 #b10011) (bvult loca16 loca10)))

; out* --> in14
(assert (=> (= ina-14 #b00001) (bvult loca2 loca11)))
(assert (=> (= ina-14 #b00010) (bvult loca3 loca11)))
(assert (=> (= ina-14 #b00011) (bvult loca3 loca11)))
(assert (=> (= ina-14 #b00100) (bvult loca5 loca11)))
(assert (=> (= ina-14 #b00101) (bvult loca5 loca11)))
(assert (=> (= ina-14 #b00110) (bvult loca6 loca11)))
(assert (=> (= ina-14 #b00111) (bvult loca7 loca11)))
(assert (=> (= ina-14 #b01000) (bvult loca8 loca11)))
(assert (=> (= ina-14 #b01001) (bvult loca9 loca11)))
(assert (=> (= ina-14 #b01010) (bvult loca10 loca11)))
(assert (=> (= ina-14 #b01011) (bvult loca11 loca11)))
(assert (=> (= ina-14 #b01100) (bvult loca12 loca11)))
(assert (=> (= ina-14 #b01101) (bvult loca12 loca11)))
(assert (=> (= ina-14 #b01110) (bvult loca12 loca11)))
(assert (=> (= ina-14 #b01111) (bvult loca12 loca11)))
(assert (=> (= ina-14 #b10000) (bvult loca16 loca11)))
(assert (=> (= ina-14 #b10001) (bvult loca16 loca11)))
(assert (=> (= ina-14 #b10010) (bvult loca16 loca11)))
(assert (=> (= ina-14 #b10011) (bvult loca16 loca11)))

; out* --> in15
(assert (=> (= ina-15 #b00001) (bvult loca2 loca11)))
(assert (=> (= ina-15 #b00010) (bvult loca3 loca11)))
(assert (=> (= ina-15 #b00011) (bvult loca3 loca11)))
(assert (=> (= ina-15 #b00100) (bvult loca5 loca11)))
(assert (=> (= ina-15 #b00101) (bvult loca5 loca11)))
(assert (=> (= ina-15 #b00110) (bvult loca6 loca11)))
(assert (=> (= ina-15 #b00111) (bvult loca7 loca11)))
(assert (=> (= ina-15 #b01000) (bvult loca8 loca11)))
(assert (=> (= ina-15 #b01001) (bvult loca9 loca11)))
(assert (=> (= ina-15 #b01010) (bvult loca10 loca11)))
(assert (=> (= ina-15 #b01011) (bvult loca11 loca11)))
(assert (=> (= ina-15 #b01100) (bvult loca12 loca11)))
(assert (=> (= ina-15 #b01101) (bvult loca12 loca11)))
(assert (=> (= ina-15 #b01110) (bvult loca12 loca11)))
(assert (=> (= ina-15 #b01111) (bvult loca12 loca11)))
(assert (=> (= ina-15 #b10000) (bvult loca16 loca11)))
(assert (=> (= ina-15 #b10001) (bvult loca16 loca11)))
(assert (=> (= ina-15 #b10010) (bvult loca16 loca11)))
(assert (=> (= ina-15 #b10011) (bvult loca16 loca11)))

; out* --> in16
(assert (=> (= ina-16 #b00001) (bvult loca2 loca12)))
(assert (=> (= ina-16 #b00010) (bvult loca3 loca12)))
(assert (=> (= ina-16 #b00011) (bvult loca3 loca12)))
(assert (=> (= ina-16 #b00100) (bvult loca5 loca12)))
(assert (=> (= ina-16 #b00101) (bvult loca5 loca12)))
(assert (=> (= ina-16 #b00110) (bvult loca6 loca12)))
(assert (=> (= ina-16 #b00111) (bvult loca7 loca12)))
(assert (=> (= ina-16 #b01000) (bvult loca8 loca12)))
(assert (=> (= ina-16 #b01001) (bvult loca9 loca12)))
(assert (=> (= ina-16 #b01010) (bvult loca10 loca12)))
(assert (=> (= ina-16 #b01011) (bvult loca11 loca12)))
(assert (=> (= ina-16 #b01100) (bvult loca12 loca12)))
(assert (=> (= ina-16 #b01101) (bvult loca12 loca12)))
(assert (=> (= ina-16 #b01110) (bvult loca12 loca12)))
(assert (=> (= ina-16 #b01111) (bvult loca12 loca12)))
(assert (=> (= ina-16 #b10000) (bvult loca16 loca12)))
(assert (=> (= ina-16 #b10001) (bvult loca16 loca12)))
(assert (=> (= ina-16 #b10010) (bvult loca16 loca12)))
(assert (=> (= ina-16 #b10011) (bvult loca16 loca12)))

; out* --> in17
(assert (=> (= ina-17 #b00001) (bvult loca2 loca16)))
(assert (=> (= ina-17 #b00010) (bvult loca3 loca16)))
(assert (=> (= ina-17 #b00011) (bvult loca3 loca16)))
(assert (=> (= ina-17 #b00100) (bvult loca5 loca16)))
(assert (=> (= ina-17 #b00101) (bvult loca5 loca16)))
(assert (=> (= ina-17 #b00110) (bvult loca6 loca16)))
(assert (=> (= ina-17 #b00111) (bvult loca7 loca16)))
(assert (=> (= ina-17 #b01000) (bvult loca8 loca16)))
(assert (=> (= ina-17 #b01001) (bvult loca9 loca16)))
(assert (=> (= ina-17 #b01010) (bvult loca10 loca16)))
(assert (=> (= ina-17 #b01011) (bvult loca11 loca16)))
(assert (=> (= ina-17 #b01100) (bvult loca12 loca16)))
(assert (=> (= ina-17 #b01101) (bvult loca12 loca16)))
(assert (=> (= ina-17 #b01110) (bvult loca12 loca16)))
(assert (=> (= ina-17 #b01111) (bvult loca12 loca16)))
(assert (=> (= ina-17 #b10000) (bvult loca16 loca16)))
(assert (=> (= ina-17 #b10001) (bvult loca16 loca16)))
(assert (=> (= ina-17 #b10010) (bvult loca16 loca16)))
(assert (=> (= ina-17 #b10011) (bvult loca16 loca16)))

; out* --> in18
(assert (=> (= ina-18 #b00001) (bvult loca2 loca3)))
(assert (=> (= ina-18 #b00010) (bvult loca3 loca3)))
(assert (=> (= ina-18 #b00011) (bvult loca3 loca3)))
(assert (=> (= ina-18 #b00100) (bvult loca5 loca3)))
(assert (=> (= ina-18 #b00101) (bvult loca5 loca3)))
(assert (=> (= ina-18 #b00110) (bvult loca6 loca3)))
(assert (=> (= ina-18 #b00111) (bvult loca7 loca3)))
(assert (=> (= ina-18 #b01000) (bvult loca8 loca3)))
(assert (=> (= ina-18 #b01001) (bvult loca9 loca3)))
(assert (=> (= ina-18 #b01010) (bvult loca10 loca3)))
(assert (=> (= ina-18 #b01011) (bvult loca11 loca3)))
(assert (=> (= ina-18 #b01100) (bvult loca12 loca3)))
(assert (=> (= ina-18 #b01101) (bvult loca12 loca3)))
(assert (=> (= ina-18 #b01110) (bvult loca12 loca3)))
(assert (=> (= ina-18 #b01111) (bvult loca12 loca3)))
(assert (=> (= ina-18 #b10000) (bvult loca16 loca3)))
(assert (=> (= ina-18 #b10001) (bvult loca16 loca3)))
(assert (=> (= ina-18 #b10010) (bvult loca16 loca3)))
(assert (=> (= ina-18 #b10011) (bvult loca16 loca3)))

; out* --> in19
(assert (=> (= ina-19 #b00001) (bvult loca2 loca5)))
(assert (=> (= ina-19 #b00010) (bvult loca3 loca5)))
(assert (=> (= ina-19 #b00011) (bvult loca3 loca5)))
(assert (=> (= ina-19 #b00100) (bvult loca5 loca5)))
(assert (=> (= ina-19 #b00101) (bvult loca5 loca5)))
(assert (=> (= ina-19 #b00110) (bvult loca6 loca5)))
(assert (=> (= ina-19 #b00111) (bvult loca7 loca5)))
(assert (=> (= ina-19 #b01000) (bvult loca8 loca5)))
(assert (=> (= ina-19 #b01001) (bvult loca9 loca5)))
(assert (=> (= ina-19 #b01010) (bvult loca10 loca5)))
(assert (=> (= ina-19 #b01011) (bvult loca11 loca5)))
(assert (=> (= ina-19 #b01100) (bvult loca12 loca5)))
(assert (=> (= ina-19 #b01101) (bvult loca12 loca5)))
(assert (=> (= ina-19 #b01110) (bvult loca12 loca5)))
(assert (=> (= ina-19 #b01111) (bvult loca12 loca5)))
(assert (=> (= ina-19 #b10000) (bvult loca16 loca5)))
(assert (=> (= ina-19 #b10001) (bvult loca16 loca5)))
(assert (=> (= ina-19 #b10010) (bvult loca16 loca5)))
(assert (=> (= ina-19 #b10011) (bvult loca16 loca5)))
)
;----------------------------------------------------------------------------
; Circuit isomorphism
;----------------------------------------------------------------------------
; 
; If there are multiple units of the same type use them in order
; In this case: 3=5 8=9=10=11 and 12=16 (type-wise)
; This assumes the presence of axioms elsewhere ensuring that either
; all or none of the inputs of a component are connected. 
;
(assert (=> (= in-4 #b00000) (= in-6 #b00000)))   ; use 3 before 5
(assert (=> (= in-8 #b00000) (= in-10 #b00000)))  ; use 8 before 9
(assert (=> (= in-10 #b00000) (= in-12 #b00000))) ; use 9 before 10
(assert (=> (= in-12 #b00000) (= in-14 #b00000))) ; use 10 before 11
(assert (=> (= in-16 #b00000) (= in-17 #b00000))) ; use 12 before 16

; Copy of above with in --> ina
ifdef(`DIST',dnl
(assert (=> (= ina-4 #b00000) (= ina-6 #b00000)))   ; use 3 before 5
(assert (=> (= ina-8 #b00000) (= ina-10 #b00000)))  ; use 8 before 9
(assert (=> (= ina-10 #b00000) (= ina-12 #b00000))) ; use 9 before 10
(assert (=> (= ina-12 #b00000) (= ina-14 #b00000))) ; use 10 before 11
(assert (=> (= ina-16 #b00000) (= ina-17 #b00000))) ; use 12 before 16
)

;
; Inputs to commutative units are in order. 
; In this case, components 3 5 and 8-11 are commutative (not all
; inputs in the case of 3 and 5)  
;
(assert (or (bvult in-4 in-5)     ; in4 <= in5
            (= in-4 in-5)))
(assert (or (bvult in-6 in-7)     ; in6 <= in7
            (= in-6 in-7)))
(assert (or (bvult in-8 in-9)     ; in8 <= in9
            (= in-8 in-9)))
(assert (or (bvult in-10 in-11)   ; in10 <= in11
            (= in-10 in-11)))
(assert (or (bvult in-12 in-13)   ; in12 <= in13
            (= in-12 in-13)))
(assert (or (bvult in-14 in-15)   ; in14 <= in15
            (= in-14 in-15)))

; copy of above with in --> ina
ifdef(`DIST',dnl
(assert (or (bvult ina-4 ina-5)   ; in4 <= in5
            (= ina-4 ina-5)))
(assert (or (bvult ina-6 ina-7)   ; in6 <= in7
            (= ina-6 ina-7)))
(assert (or (bvult ina-8 ina-9)   ; in8 <= in9
            (= ina-8 ina-9)))
(assert (or (bvult ina-10 ina-11) ; in10 <= in11
            (= ina-10 ina-11)))
(assert (or (bvult ina-12 ina-13) ; in12 <= in13
            (= ina-12 ina-13)))
(assert (or (bvult ina-14 ina-15) ; in14 <= in15
            (= ina-14 ina-15)))
)

; 
; Control inputs should use the 'most refined' net possible. 
; Implementation-wise, that means that if any output net N is
; connected to a nand gate input, then all output nets N' with
; loc(N')>loc(N) must also be connected to a nand gate input, where
; loc(N) is defined to be the value of loc for the functional unit
; producing N.  
; 
; This raises the question of what a control output is. Here, we
; define a control output to be all 1 bit output nets. In this
; example, this corresponds to the outputs for: adder carries,
; constants, nand gates, splitters.
; 
; An extra variable is created to represent the set of all output nets
; connected to some nand gate input, but this can be avoided at the
; cost of a huge constraint. 
; 
(declare-fun allouts () (_ BitVec NUMOUT))

(assert (= (= (GETBIT(2) allouts) #b1)
           (or (= in-8 #b00010)  (= in-9 #b00010)  (= in-10 #b00010)
               (= in-11 #b00010) (= in-12 #b00010) (= in-13 #b00010)
               (= in-14 #b00010) (= in-15 #b00010))))
(assert (= (= (GETBIT(4) allouts) #b1)
           (or (= in-8 #b00100)  (= in-9 #b00100)  (= in-10 #b00100)
               (= in-11 #b00100) (= in-12 #b00100) (= in-13 #b00100)
               (= in-14 #b00100) (= in-15 #b00100))))
(assert (= (= (GETBIT(6) allouts) #b1)
           (or (= in-8 #b00110)  (= in-9 #b00110)  (= in-10 #b00110)
               (= in-11 #b00110) (= in-12 #b00110) (= in-13 #b00110)
               (= in-14 #b00110) (= in-15 #b00110))))
(assert (= (= (GETBIT(7) allouts) #b1)
           (or (= in-8 #b00111)  (= in-9 #b00111)  (= in-10 #b00111)
               (= in-11 #b00111) (= in-12 #b00111) (= in-13 #b00111)
               (= in-14 #b00111) (= in-15 #b00111))))
(assert (= (= (GETBIT(8) allouts) #b1)
           (or (= in-8 #b01000)  (= in-9 #b01000)  (= in-10 #b01000)
               (= in-11 #b01000) (= in-12 #b01000) (= in-13 #b01000)
               (= in-14 #b01000) (= in-15 #b01000))))
(assert (= (= (GETBIT(9) allouts) #b1)
           (or (= in-8 #b01001)  (= in-9 #b01001)  (= in-10 #b01001)
               (= in-11 #b01001) (= in-12 #b01001) (= in-13 #b01001)
               (= in-14 #b01001) (= in-15 #b01001))))
(assert (= (= (GETBIT(10) allouts) #b1)
           (or (= in-8 #b01010)  (= in-9 #b01010)  (= in-10 #b01010)
               (= in-11 #b01010) (= in-12 #b01010) (= in-13 #b01010)
               (= in-14 #b01010) (= in-15 #b01010))))
(assert (= (= (GETBIT(11) allouts) #b1)
           (or (= in-8 #b01011)  (= in-9 #b01011)  (= in-10 #b01011)
               (= in-11 #b01011) (= in-12 #b01011) (= in-13 #b01011)
               (= in-14 #b01011) (= in-15 #b01011))))
(assert (= (= (GETBIT(12) allouts) #b1)
           (or (= in-8 #b01100)  (= in-9 #b01100)  (= in-10 #b01100)
               (= in-11 #b01100) (= in-12 #b01100) (= in-13 #b01100)
               (= in-14 #b01100) (= in-15 #b01100))))
(assert (= (= (GETBIT(13) allouts) #b1)
           (or (= in-8 #b01101)  (= in-9 #b01101)  (= in-10 #b01101)
               (= in-11 #b01101) (= in-12 #b01101) (= in-13 #b01101)
               (= in-14 #b01101) (= in-15 #b01101))))
(assert (= (= (GETBIT(14) allouts) #b1)
           (or (= in-8 #b01110)  (= in-9 #b01110)  (= in-10 #b01110)
               (= in-11 #b01110) (= in-12 #b01110) (= in-13 #b01110)
               (= in-14 #b01110) (= in-15 #b01110))))
(assert (= (= (GETBIT(15) allouts) #b1)
           (or (= in-8 #b01111)  (= in-9 #b01111)  (= in-10 #b01111)
               (= in-11 #b01111) (= in-12 #b01111) (= in-13 #b01111)
               (= in-14 #b01111) (= in-15 #b01111))))
(assert (= (= (GETBIT(16) allouts) #b1)
           (or (= in-8 #b10000)  (= in-9 #b10000)  (= in-10 #b10000)
               (= in-11 #b10000) (= in-12 #b10000) (= in-13 #b10000)
               (= in-14 #b10000) (= in-15 #b10000))))
(assert (= (= (GETBIT(17) allouts) #b1)
           (or (= in-8 #b10001)  (= in-9 #b10001)  (= in-10 #b10001)
               (= in-11 #b10001) (= in-12 #b10001) (= in-13 #b10001)
               (= in-14 #b10001) (= in-15 #b10001))))
(assert (= (= (GETBIT(18) allouts) #b1)
           (or (= in-8 #b10010)  (= in-9 #b10010)  (= in-10 #b10010)
               (= in-11 #b10010) (= in-12 #b10010) (= in-13 #b10010)
               (= in-14 #b10010) (= in-15 #b10010))))
(assert (= (= (GETBIT(19) allouts) #b1)
           (or (= in-8 #b10011)  (= in-9 #b10011)  (= in-10 #b10011)
               (= in-11 #b10011) (= in-12 #b10011) (= in-13 #b10011)
               (= in-14 #b10011) (= in-15 #b10011))))

; The following macro says that if output net arg1 is connected to
; some nand gate input and loc(arg2) < loc(f) (f is a component), then 
; the output nets of f are also connected to some nand gate input.
define(`OUTLOC',
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc3))
            (= (GETBIT(2) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc5))
            (= (GETBIT(4) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc6))
            (= (GETBIT(6) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc7))
            (= (GETBIT(7) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc8))
            (= (GETBIT(8) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc9))
            (= (GETBIT(9) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc10))
            (= (GETBIT(10) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc11))
            (= (GETBIT(11) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc12))
            (= (GETBIT(12) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc12))
            (= (GETBIT(13) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc12))
            (= (GETBIT(14) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc12))
            (= (GETBIT(15) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc16))
            (= (GETBIT(16) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc16))
            (= (GETBIT(17) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc16))
            (= (GETBIT(18) allouts) #b1)))
(assert (=> (and (= (GETBIT($1) allouts) #b1) (bvult $2 loc16))
            (= (GETBIT(19) allouts) #b1)))
)
OUTLOC(2,loc3)
OUTLOC(4,loc5)
OUTLOC(6,loc6)
OUTLOC(7,loc7)
OUTLOC(8,loc8)
OUTLOC(9,loc9)
OUTLOC(10,loc10)
OUTLOC(11,loc11)
OUTLOC(12,loc12)
OUTLOC(13,loc12)
OUTLOC(14,loc12)
OUTLOC(15,loc12)
OUTLOC(16,loc16)
OUTLOC(17,loc16)
OUTLOC(18,loc16)
OUTLOC(19,loc16)

; Copy of above with allouts-->alloutsa loc-->loca in-->ina
ifdef(`DIST',dnl
(declare-fun alloutsa () (_ BitVec NUMOUT))

(assert (= (= (GETBIT(2) alloutsa) #b1)
           (or (= ina-8 #b00010)  (= ina-9 #b00010)  (= ina-10 #b00010)
               (= ina-11 #b00010) (= ina-12 #b00010) (= ina-13 #b00010)
               (= ina-14 #b00010) (= ina-15 #b00010))))
(assert (= (= (GETBIT(4) alloutsa) #b1)
           (or (= ina-8 #b00100)  (= ina-9 #b00100)  (= ina-10 #b00100)
               (= ina-11 #b00100) (= ina-12 #b00100) (= ina-13 #b00100)
               (= ina-14 #b00100) (= ina-15 #b00100))))
(assert (= (= (GETBIT(6) alloutsa) #b1)
           (or (= ina-8 #b00110)  (= ina-9 #b00110)  (= ina-10 #b00110)
               (= ina-11 #b00110) (= ina-12 #b00110) (= ina-13 #b00110)
               (= ina-14 #b00110) (= ina-15 #b00110))))
(assert (= (= (GETBIT(7) alloutsa) #b1)
           (or (= ina-8 #b00111)  (= ina-9 #b00111)  (= ina-10 #b00111)
               (= ina-11 #b00111) (= ina-12 #b00111) (= ina-13 #b00111)
               (= ina-14 #b00111) (= ina-15 #b00111))))
(assert (= (= (GETBIT(8) alloutsa) #b1)
           (or (= ina-8 #b01000)  (= ina-9 #b01000)  (= ina-10 #b01000)
               (= ina-11 #b01000) (= ina-12 #b01000) (= ina-13 #b01000)
               (= ina-14 #b01000) (= ina-15 #b01000))))
(assert (= (= (GETBIT(9) alloutsa) #b1)
           (or (= ina-8 #b01001)  (= ina-9 #b01001)  (= ina-10 #b01001)
               (= ina-11 #b01001) (= ina-12 #b01001) (= ina-13 #b01001)
               (= ina-14 #b01001) (= ina-15 #b01001))))
(assert (= (= (GETBIT(10) alloutsa) #b1)
           (or (= ina-8 #b01010)  (= ina-9 #b01010)  (= ina-10 #b01010)
               (= ina-11 #b01010) (= ina-12 #b01010) (= ina-13 #b01010)
               (= ina-14 #b01010) (= ina-15 #b01010))))
(assert (= (= (GETBIT(11) alloutsa) #b1)
           (or (= ina-8 #b01011)  (= ina-9 #b01011)  (= ina-10 #b01011)
               (= ina-11 #b01011) (= ina-12 #b01011) (= ina-13 #b01011)
               (= ina-14 #b01011) (= ina-15 #b01011))))
(assert (= (= (GETBIT(12) alloutsa) #b1)
           (or (= ina-8 #b01100)  (= ina-9 #b01100)  (= ina-10 #b01100)
               (= ina-11 #b01100) (= ina-12 #b01100) (= ina-13 #b01100)
               (= ina-14 #b01100) (= ina-15 #b01100))))
(assert (= (= (GETBIT(13) alloutsa) #b1)
           (or (= ina-8 #b01101)  (= ina-9 #b01101)  (= ina-10 #b01101)
               (= ina-11 #b01101) (= ina-12 #b01101) (= ina-13 #b01101)
               (= ina-14 #b01101) (= ina-15 #b01101))))
(assert (= (= (GETBIT(14) alloutsa) #b1)
           (or (= ina-8 #b01110)  (= ina-9 #b01110)  (= ina-10 #b01110)
               (= ina-11 #b01110) (= ina-12 #b01110) (= ina-13 #b01110)
               (= ina-14 #b01110) (= ina-15 #b01110))))
(assert (= (= (GETBIT(15) alloutsa) #b1)
           (or (= ina-8 #b01111)  (= ina-9 #b01111)  (= ina-10 #b01111)
               (= ina-11 #b01111) (= ina-12 #b01111) (= ina-13 #b01111)
               (= ina-14 #b01111) (= ina-15 #b01111))))
(assert (= (= (GETBIT(16) alloutsa) #b1)
           (or (= ina-8 #b10000)  (= ina-9 #b10000)  (= ina-10 #b10000)
               (= ina-11 #b10000) (= ina-12 #b10000) (= ina-13 #b10000)
               (= ina-14 #b10000) (= ina-15 #b10000))))
(assert (= (= (GETBIT(17) alloutsa) #b1)
           (or (= ina-8 #b10001)  (= ina-9 #b10001)  (= ina-10 #b10001)
               (= ina-11 #b10001) (= ina-12 #b10001) (= ina-13 #b10001)
               (= ina-14 #b10001) (= ina-15 #b10001))))
(assert (= (= (GETBIT(18) alloutsa) #b1)
           (or (= ina-8 #b10010)  (= ina-9 #b10010)  (= ina-10 #b10010)
               (= ina-11 #b10010) (= ina-12 #b10010) (= ina-13 #b10010)
               (= ina-14 #b10010) (= ina-15 #b10010))))
(assert (= (= (GETBIT(19) alloutsa) #b1)
           (or (= ina-8 #b10011)  (= ina-9 #b10011)  (= ina-10 #b10011)
               (= ina-11 #b10011) (= ina-12 #b10011) (= ina-13 #b10011)
               (= ina-14 #b10011) (= ina-15 #b10011))))

define(`OUTLOCA',
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca3))
            (= (GETBIT(2) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca5))
            (= (GETBIT(4) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca6))
            (= (GETBIT(6) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca7))
            (= (GETBIT(7) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca8))
            (= (GETBIT(8) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca9))
            (= (GETBIT(9) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca10))
            (= (GETBIT(10) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca11))
            (= (GETBIT(11) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca12))
            (= (GETBIT(12) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca12))
            (= (GETBIT(13) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca12))
            (= (GETBIT(14) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca12))
            (= (GETBIT(15) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca16))
            (= (GETBIT(16) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca16))
            (= (GETBIT(17) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca16))
            (= (GETBIT(18) alloutsa) #b1)))
(assert (=> (and (= (GETBIT($1) alloutsa) #b1) (bvult $2 loca16))
            (= (GETBIT(19) alloutsa) #b1)))
)
OUTLOCA(2,loca3)
OUTLOCA(4,loca5)
OUTLOCA(6,loca6)
OUTLOCA(7,loca7)
OUTLOCA(8,loca8)
OUTLOCA(9,loca9)
OUTLOCA(10,loca10)
OUTLOCA(11,loca11)
OUTLOCA(12,loca12)
OUTLOCA(13,loca12)
OUTLOCA(14,loca12)
OUTLOCA(15,loca12)
OUTLOCA(16,loca16)
OUTLOCA(17,loca16)
OUTLOCA(18,loca16)
OUTLOCA(19,loca16)
)

;----------------------------------------------------------------------------
; Semantics 
;----------------------------------------------------------------------------
;
; Semantics of functional units (including system inputs/outputs). 
;
; (assert (= valin-1  sysout))
; (assert (= valout-1 (concat valin-3 valin-2)))
; (assert (= valout-2 (ite 
;   (bvult (bvadd (concat #b0 valin-4) (concat #b0 valin-5)
;                 (concat #b0000 valin-18)) 
;          #b10000)
;   #b0 #b1)))
; (assert (= valout-3 (bvadd valin-4 valin-5 (concat #b000 valin-18))))
; (assert (= valout-4 (ite 
;   (bvult (bvadd (concat #b0 valin-6) (concat #b0 valin-7)
;                 (concat #b0000 valin-19)) 
;          #b10000)
;   #b0 #b1)))
; (assert (= valout-5 (bvadd valin-6 valin-7 (concat #b000 valin-19))))
; (assert (= valout-6 #b0))
; (assert (= valout-7 #b1))
; (assert (= valout-8 (bvnot (bvand valin-8 valin-9))))
; (assert (= valout-9 (bvnot (bvand valin-10 valin-11))))
; (assert (= valout-10 (bvnot (bvand valin-12 valin-13))))
; (assert (= valout-11 (bvnot (bvand valin-14 valin-15))))
; (assert (= valout-12 (GETBIT(0) valin-16)))
; (assert (= valout-13 (GETBIT(1) valin-16)))
; (assert (= valout-14 (GETBIT(2) valin-16)))
; (assert (= valout-15 (GETBIT(3) valin-16)))
; (assert (= valout-16 (GETBIT(0) valin-17)))
; (assert (= valout-17 (GETBIT(1) valin-17)))
; (assert (= valout-18 (GETBIT(2) valin-17)))
; (assert (= valout-19 (GETBIT(3) valin-17)))
; (assert (= valout-20 sysinxl))
; (assert (= valout-21 sysinxh))
; (assert (= valout-22 sysinyl))
; (assert (= valout-23 sysinyh))
;
ifdef(`INFO',dnl
syscmd(`echo "
(sysout (in-1) ())
(join-1 (in-3 in-2) (out-1))
(add-1 (in-4 in-5 in-18) (out-2 out-1))
(add-2 (in-6 in-7 in-19) (out-4 out-3))
(zero () (out-6))
(one () (out-7))
(nand-1 (in-8 in-9) (out-8))
(nand-2 (in-10 in-11) (out-9))
(nand-3 (in-12 in-13) (out-10))
(nand-4 (in-14 in-15) (out-11))
(split-1 (in-16) (out-15 out-14 out-13 out-12))
(split-2 (in-17) (out-19 out-18 out-17 out-16))
(xl () (out-20))
(xh () (out-21))
(yl () (out-22))
(yh () (out-23))
" >> components'))

forloop(`I',1,ITER,
`(assert (= valin-1-'`I'` sysout-'`I'`))'
`(assert (= valout-1-'`I'` (concat valin-3-'`I'` valin-2-'`I'`)))'
`(assert (= valout-2-'`I'` (ite'
`  (bvult (bvadd (concat #b0 valin-4-'`I'`)(concat #b0 valin-5-'`I'`)'
`                (concat #b0000 valin-18-'`I'`))'
`         #b10000)'
`  #b0 #b1)))'
`(assert (= valout-3-'`I'` (bvadd valin-4-'`I'` valin-5-'`I'
`                                (concat #b000 valin-18-'`I'`))))'
`(assert (= valout-4-'`I'` (ite'
`  (bvult (bvadd (concat #b0 valin-6-'`I'`)(concat #b0 valin-7-'`I'`)'
`                (concat #b0000 valin-19-'`I'`))'
`         #b10000)'
`  #b0 #b1)))'
`(assert (= valout-5-'`I'` (bvadd valin-6-'`I'` valin-7-'`I'
`                                (concat #b000 valin-19-'`I'`))))'
`(assert (= valout-6-'`I'` #b0))'
`(assert (= valout-7-'`I'` #b1))'
`(assert (= valout-8-'`I'` (bvnot (bvand valin-8-'`I'` valin-9-'`I'`))))'
`(assert (= valout-9-'`I'` (bvnot (bvand valin-10-'`I'` valin-11-'`I'`))))'
`(assert (= valout-10-'`I'` (bvnot (bvand valin-12-'`I'` valin-13-'`I'`))))'
`(assert (= valout-11-'`I'` (bvnot (bvand valin-14-'`I'` valin-15-'`I'`))))'
`(assert (= valout-12-'`I'` (GETBIT(0) valin-16-'`I'`)))'
`(assert (= valout-13-'`I'` (GETBIT(1) valin-16-'`I'`)))'
`(assert (= valout-14-'`I'` (GETBIT(2) valin-16-'`I'`)))'
`(assert (= valout-15-'`I'` (GETBIT(3) valin-16-'`I'`)))'
`(assert (= valout-16-'`I'` (GETBIT(0) valin-17-'`I'`)))'
`(assert (= valout-17-'`I'` (GETBIT(1) valin-17-'`I'`)))'
`(assert (= valout-18-'`I'` (GETBIT(2) valin-17-'`I'`)))'
`(assert (= valout-19-'`I'` (GETBIT(3) valin-17-'`I'`)))'
`(assert (= valout-20-'`I'` sysinxl-'`I'`))'
`(assert (= valout-21-'`I'` sysinxh-'`I'`))'
`(assert (= valout-22-'`I'` sysinyl-'`I'`))'
`(assert (= valout-23-'`I'` sysinyh-'`I'`))'
)

; Copy of above with val-->vala (except the special case sysout) 
ifdef(`DIST',dnl
forloop(`I',1,ITER,
`(assert (= valina-1-'`I'` sysout-'`I'`))'
)
`(assert (= valina-1-'NEXT` sysouta))'

forloop(`I',1,NEXT,
`(assert (= valouta-1-'`I'` (concat valina-3-'`I'` valina-2-'`I'`)))'
`(assert (= valouta-2-'`I'` (ite'
`  (bvult (bvadd (concat #b0 valina-4-'`I'`)(concat #b0 valina-5-'`I'`)'
`                (concat #b0000 valina-18-'`I'`))'
`         #b10000)'
`  #b0 #b1)))'
`(assert (= valouta-3-'`I'` (bvadd valina-4-'`I'` valina-5-'`I'
`                                 (concat #b000 valina-18-'`I'`))))'
`(assert (= valouta-4-'`I'` (ite'
`  (bvult (bvadd (concat #b0 valina-6-'`I'`)(concat #b0 valina-7-'`I'`)'
`                (concat #b0000 valina-19-'`I'`))'
`         #b10000)'
`  #b0 #b1)))'
`(assert (= valouta-5-'`I'` (bvadd valina-6-'`I'` valina-7-'`I'
`                                (concat #b000 valina-19-'`I'`))))'
`(assert (= valouta-6-'`I'` #b0))'
`(assert (= valouta-7-'`I'` #b1))'
`(assert (= valouta-8-'`I'` (bvnot (bvand valina-8-'`I'` valina-9-'`I'`))))'
`(assert (= valouta-9-'`I'` (bvnot (bvand valina-10-'`I'` valina-11-'`I'`))))'
`(assert (= valouta-10-'`I'` (bvnot (bvand valina-12-'`I'` valina-13-'`I'`))))'
`(assert (= valouta-11-'`I'` (bvnot (bvand valina-14-'`I'` valina-15-'`I'`))))'
`(assert (= valouta-12-'`I'` (GETBIT(0) valina-16-'`I'`)))'
`(assert (= valouta-13-'`I'` (GETBIT(1) valina-16-'`I'`)))'
`(assert (= valouta-14-'`I'` (GETBIT(2) valina-16-'`I'`)))'
`(assert (= valouta-15-'`I'` (GETBIT(3) valina-16-'`I'`)))'
`(assert (= valouta-16-'`I'` (GETBIT(0) valina-17-'`I'`)))'
`(assert (= valouta-17-'`I'` (GETBIT(1) valina-17-'`I'`)))'
`(assert (= valouta-18-'`I'` (GETBIT(2) valina-17-'`I'`)))'
`(assert (= valouta-19-'`I'` (GETBIT(3) valina-17-'`I'`)))'
`(assert (= valouta-20-'`I'` sysinxl-'`I'`))'
`(assert (= valouta-21-'`I'` sysinxh-'`I'`))'
`(assert (= valouta-22-'`I'` sysinyl-'`I'`))'
`(assert (= valouta-23-'`I'` sysinyh-'`I'`))'
)

; Copy of above with `I' --> `NEXT'
`(assert (= valin-1-'NEXT` sysout-'NEXT`))'
`(assert (= valout-1-'NEXT` (concat valin-3-'NEXT` valin-2-'NEXT`)))'
`(assert (= valout-2-'`NEXT'` (ite'
`  (bvult (bvadd (concat #b0 valin-4-'`NEXT'`)(concat #b0 valin-5-'`NEXT'`)'
`                (concat #b0000 valin-18-'`NEXT'`))'
`         #b10000)'
`  #b0 #b1)))'
`(assert (= valout-3-'NEXT` (bvadd valin-4-'NEXT` valin-5-'NEXT
`                                (concat #b000 valin-18-'NEXT`))))'
`(assert (= valout-4-'`NEXT'` (ite'
`  (bvult (bvadd (concat #b0 valin-6-'`NEXT'`)(concat #b0 valin-7-'`NEXT'`)'
`                (concat #b0000 valin-19-'`NEXT'`))'
`         #b10000)'
`  #b0 #b1)))'
`(assert (= valout-5-'NEXT` (bvadd valin-6-'NEXT` valin-7-'NEXT
`                                (concat #b000 valin-19-'NEXT`))))'
`(assert (= valout-6-'NEXT` #b0))'
`(assert (= valout-7-'NEXT` #b1))'
`(assert (= valout-8-'NEXT` (bvnot (bvand valin-8-'NEXT` valin-9-'NEXT`))))'
`(assert (= valout-9-'NEXT` (bvnot (bvand valin-10-'NEXT` valin-11-'NEXT`))))'
`(assert (= valout-10-'NEXT` (bvnot (bvand valin-12-'NEXT` valin-13-'NEXT`))))'
`(assert (= valout-11-'NEXT` (bvnot (bvand valin-14-'NEXT` valin-15-'NEXT`))))'
`(assert (= valout-12-'NEXT` (GETBIT(0) valin-16-'NEXT`)))'
`(assert (= valout-13-'NEXT` (GETBIT(1) valin-16-'NEXT`)))'
`(assert (= valout-14-'NEXT` (GETBIT(2) valin-16-'NEXT`)))'
`(assert (= valout-15-'NEXT` (GETBIT(3) valin-16-'NEXT`)))'
`(assert (= valout-16-'NEXT` (GETBIT(0) valin-17-'NEXT`)))'
`(assert (= valout-17-'NEXT` (GETBIT(1) valin-17-'NEXT`)))'
`(assert (= valout-18-'NEXT` (GETBIT(2) valin-17-'NEXT`)))'
`(assert (= valout-19-'NEXT` (GETBIT(3) valin-17-'NEXT`)))'
`(assert (= valout-20-'NEXT` sysinxl-'NEXT`))'
`(assert (= valout-21-'NEXT` sysinxh-'NEXT`))'
`(assert (= valout-22-'NEXT` sysinyl-'NEXT`))'
`(assert (= valout-23-'NEXT` sysinyh-'NEXT`))'
)

;
; Connection semantics
; Note there are lots of axioms but they are all very simple (just
; equalities). Hopefully this doesn't cause problems. 
;

;
; Type compatibility 
; Two nets of different types/sizes aren't connected. 
; In this case the following are of the same sizes:
;       Input nets  Output nets
;   1:  8-15,18,19  2 4 6-19
;   n:  2-7  16 17  3 5 20-23
;   2n: 1           1
; Of course any input net could be connected to output 0 (ie,
; disconnected) too. 
;   
(assert (or (= in-1 #b00001) 
            (= in-1 #b00000)))

(assert (or (= in-2 #b00011) (= in-2 #b00101) (= in-2 #b10100)
            (= in-2 #b10101) (= in-2 #b10110) (= in-2 #b10111)
            (= in-2 #b00000)))
(assert (or (= in-3 #b00011) (= in-3 #b00101) (= in-3 #b10100)
            (= in-3 #b10101) (= in-3 #b10110) (= in-3 #b10111)
            (= in-3 #b00000)))
(assert (or (= in-4 #b00011) (= in-4 #b00101) (= in-4 #b10100)
            (= in-4 #b10101) (= in-4 #b10110) (= in-4 #b10111)
            (= in-4 #b00000)))
(assert (or (= in-5 #b00011) (= in-5 #b00101) (= in-5 #b10100)
            (= in-5 #b10101) (= in-5 #b10110) (= in-5 #b10111)
            (= in-5 #b00000)))
(assert (or (= in-6 #b00011) (= in-6 #b00101) (= in-6 #b10100)
            (= in-6 #b10101) (= in-6 #b10110) (= in-6 #b10111)
            (= in-6 #b00000)))
(assert (or (= in-7 #b00011) (= in-7 #b00101) (= in-7 #b10100)
            (= in-7 #b10101) (= in-7 #b10110) (= in-7 #b10111)
            (= in-7 #b00000)))
(assert (or (= in-16 #b00011) (= in-16 #b00101) (= in-16 #b10100)
            (= in-16 #b10101) (= in-16 #b10110) (= in-16 #b10111)
            (= in-16 #b00000)))
(assert (or (= in-17 #b00011) (= in-17 #b00101) (= in-17 #b10100)
            (= in-17 #b10101) (= in-17 #b10110) (= in-17 #b10111)
            (= in-17 #b00000)))

(assert (or (= in-8 #b00010) (= in-8 #b00100) 
            (and (bvult in-8 #b10100) (bvult #b00101 in-8))
            (= in-8 #b00000)))
(assert (or (= in-9 #b00010) (= in-9 #b00100) 
            (and (bvult in-9 #b10100) (bvult #b00101 in-9))
            (= in-9 #b00000)))
(assert (or (= in-10 #b00010) (= in-10 #b00100) 
            (and (bvult in-10 #b10100) (bvult #b00101 in-10))
            (= in-10 #b00000)))
(assert (or (= in-11 #b00010) (= in-11 #b00100) 
            (and (bvult in-11 #b10100) (bvult #b00101 in-11))
            (= in-11 #b00000)))
(assert (or (= in-12 #b00010) (= in-12 #b00100) 
            (and (bvult in-12 #b10100) (bvult #b00101 in-12))
            (= in-12 #b00000)))
(assert (or (= in-13 #b00010) (= in-13 #b00100) 
            (and (bvult in-13 #b10100) (bvult #b00101 in-13))
            (= in-13 #b00000)))
(assert (or (= in-14 #b00010) (= in-14 #b00100) 
            (and (bvult in-14 #b10100) (bvult #b00101 in-14))
            (= in-14 #b00000)))
(assert (or (= in-15 #b00010) (= in-15 #b00100) 
            (and (bvult in-15 #b10100) (bvult #b00101 in-15))
            (= in-15 #b00000)))
(assert (or (= in-18 #b00010) (= in-18 #b00100) 
            (and (bvult in-18 #b10100) (bvult #b00101 in-18))
            (= in-18 #b00000)))
(assert (or (= in-19 #b00010) (= in-19 #b00100) 
            (and (bvult in-19 #b10100) (bvult #b00101 in-19))
            (= in-19 #b00000)))

; Copy of above with in-->ina
ifdef(`DIST',dnl
(assert (or (= ina-1 #b00001) 
            (= ina-1 #b00000)))

(assert (or (= ina-2 #b00011) (= ina-2 #b00101) (= ina-2 #b10100)
            (= ina-2 #b10101) (= ina-2 #b10110) (= ina-2 #b10111)
            (= ina-2 #b00000)))
(assert (or (= ina-3 #b00011) (= ina-3 #b00101) (= ina-3 #b10100)
            (= ina-3 #b10101) (= ina-3 #b10110) (= ina-3 #b10111)
            (= ina-3 #b00000)))
(assert (or (= ina-4 #b00011) (= ina-4 #b00101) (= ina-4 #b10100)
            (= ina-4 #b10101) (= ina-4 #b10110) (= ina-4 #b10111)
            (= ina-4 #b00000)))
(assert (or (= ina-5 #b00011) (= ina-5 #b00101) (= ina-5 #b10100)
            (= ina-5 #b10101) (= ina-5 #b10110) (= ina-5 #b10111)
            (= ina-5 #b00000)))
(assert (or (= ina-6 #b00011) (= ina-6 #b00101) (= ina-6 #b10100)
            (= ina-6 #b10101) (= ina-6 #b10110) (= ina-6 #b10111)
            (= ina-6 #b00000)))
(assert (or (= ina-7 #b00011) (= ina-7 #b00101) (= ina-7 #b10100)
            (= ina-7 #b10101) (= ina-7 #b10110) (= ina-7 #b10111)
            (= ina-7 #b00000)))
(assert (or (= ina-16 #b00011) (= ina-16 #b00101) (= ina-16 #b10100)
            (= ina-16 #b10101) (= ina-16 #b10110) (= ina-16 #b10111)
            (= ina-16 #b00000)))
(assert (or (= ina-17 #b00011) (= ina-17 #b00101) (= ina-17 #b10100)
            (= ina-17 #b10101) (= ina-17 #b10110) (= ina-17 #b10111)
            (= ina-17 #b00000)))

(assert (or (= ina-8 #b00010) (= ina-8 #b00100) 
            (and (bvult ina-8 #b10100) (bvult #b00101 ina-8))
            (= ina-8 #b00000)))
(assert (or (= ina-9 #b00010) (= ina-9 #b00100) 
            (and (bvult ina-9 #b10100) (bvult #b00101 ina-9))
            (= ina-9 #b00000)))
(assert (or (= ina-10 #b00010) (= ina-10 #b00100) 
            (and (bvult ina-10 #b10100) (bvult #b00101 ina-10))
            (= ina-10 #b00000)))
(assert (or (= ina-11 #b00010) (= ina-11 #b00100) 
            (and (bvult ina-11 #b10100) (bvult #b00101 ina-11))
            (= ina-11 #b00000)))
(assert (or (= ina-12 #b00010) (= ina-12 #b00100) 
            (and (bvult ina-12 #b10100) (bvult #b00101 ina-12))
            (= ina-12 #b00000)))
(assert (or (= ina-13 #b00010) (= ina-13 #b00100) 
            (and (bvult ina-13 #b10100) (bvult #b00101 ina-13))
            (= ina-13 #b00000)))
(assert (or (= ina-14 #b00010) (= ina-14 #b00100) 
            (and (bvult ina-14 #b10100) (bvult #b00101 ina-14))
            (= ina-14 #b00000)))
(assert (or (= ina-15 #b00010) (= ina-15 #b00100) 
            (and (bvult ina-15 #b10100) (bvult #b00101 ina-15))
            (= ina-15 #b00000)))
(assert (or (= ina-18 #b00010) (= ina-18 #b00100) 
            (and (bvult ina-18 #b10100) (bvult #b00101 ina-18))
            (= ina-18 #b00000)))
(assert (or (= ina-19 #b00010) (= ina-19 #b00100) 
            (and (bvult ina-19 #b10100) (bvult #b00101 ina-19))
            (= ina-19 #b00000)))
)

;
; if input net c is connected to output net r
;   then valout-c = valin-r 
; This only applies to type-compatible nets. 
; Although other axioms make the type-incompatible nets fail the
; antecedent of the implications here, they are commented out
; anyway. The code could be made simpler by relying on these other
; axioms and looping through all possibilities without worrying about
; the inapplicable axioms. 
;
forloop(`I',1,ITER,dnl 
`(assert (=> (= in-1 #b00001) (= valin-1-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-1 #b00010) (= valin-1-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-1 #b00011) (= valin-1-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-1 #b00100) (= valin-1-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-1 #b00101) (= valin-1-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-1 #b00110) (= valin-1-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-1 #b00111) (= valin-1-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-1 #b01000) (= valin-1-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-1 #b01001) (= valin-1-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-1 #b01010) (= valin-1-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-1 #b01011) (= valin-1-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-1 #b01100) (= valin-1-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-1 #b01101) (= valin-1-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-1 #b01110) (= valin-1-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-1 #b01111) (= valin-1-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-1 #b10000) (= valin-1-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-1 #b10001) (= valin-1-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-1 #b10010) (= valin-1-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-1 #b10011) (= valin-1-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-1 #b10100) (= valin-1-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-1 #b10101) (= valin-1-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-1 #b10110) (= valin-1-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-1 #b10111) (= valin-1-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-2 #b00001) (= valin-2-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-2 #b00010) (= valin-2-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-2 #b00011) (= valin-2-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-2 #b00100) (= valin-2-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-2 #b00101) (= valin-2-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-2 #b00110) (= valin-2-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-2 #b00111) (= valin-2-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-2 #b01000) (= valin-2-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-2 #b01001) (= valin-2-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-2 #b01010) (= valin-2-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-2 #b01011) (= valin-2-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-2 #b01100) (= valin-2-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-2 #b01101) (= valin-2-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-2 #b01110) (= valin-2-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-2 #b01111) (= valin-2-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-2 #b10000) (= valin-2-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-2 #b10001) (= valin-2-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-2 #b10010) (= valin-2-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-2 #b10011) (= valin-2-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-2 #b10100) (= valin-2-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-2 #b10101) (= valin-2-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-2 #b10110) (= valin-2-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-2 #b10111) (= valin-2-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-3 #b00001) (= valin-3-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-3 #b00010) (= valin-3-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-3 #b00011) (= valin-3-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-3 #b00100) (= valin-3-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-3 #b00101) (= valin-3-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-3 #b00110) (= valin-3-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-3 #b00111) (= valin-3-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-3 #b01000) (= valin-3-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-3 #b01001) (= valin-3-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-3 #b01010) (= valin-3-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-3 #b01011) (= valin-3-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-3 #b01100) (= valin-3-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-3 #b01101) (= valin-3-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-3 #b01110) (= valin-3-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-3 #b01111) (= valin-3-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-3 #b10000) (= valin-3-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-3 #b10001) (= valin-3-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-3 #b10010) (= valin-3-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-3 #b10011) (= valin-3-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-3 #b10100) (= valin-3-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-3 #b10101) (= valin-3-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-3 #b10110) (= valin-3-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-3 #b10111) (= valin-3-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-4 #b00001) (= valin-4-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-4 #b00010) (= valin-4-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-4 #b00011) (= valin-4-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-4 #b00100) (= valin-4-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-4 #b00101) (= valin-4-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-4 #b00110) (= valin-4-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-4 #b00111) (= valin-4-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-4 #b01000) (= valin-4-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-4 #b01001) (= valin-4-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-4 #b01010) (= valin-4-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-4 #b01011) (= valin-4-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-4 #b01100) (= valin-4-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-4 #b01101) (= valin-4-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-4 #b01110) (= valin-4-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-4 #b01111) (= valin-4-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-4 #b10000) (= valin-4-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-4 #b10001) (= valin-4-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-4 #b10010) (= valin-4-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-4 #b10011) (= valin-4-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-4 #b10100) (= valin-4-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-4 #b10101) (= valin-4-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-4 #b10110) (= valin-4-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-4 #b10111) (= valin-4-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-5 #b00001) (= valin-5-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-5 #b00010) (= valin-5-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-5 #b00011) (= valin-5-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-5 #b00100) (= valin-5-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-5 #b00101) (= valin-5-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-5 #b00110) (= valin-5-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-5 #b00111) (= valin-5-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-5 #b01000) (= valin-5-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-5 #b01001) (= valin-5-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-5 #b01010) (= valin-5-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-5 #b01011) (= valin-5-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-5 #b01100) (= valin-5-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-5 #b01101) (= valin-5-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-5 #b01110) (= valin-5-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-5 #b01111) (= valin-5-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-5 #b10000) (= valin-5-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-5 #b10001) (= valin-5-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-5 #b10010) (= valin-5-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-5 #b10011) (= valin-5-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-5 #b10100) (= valin-5-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-5 #b10101) (= valin-5-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-5 #b10110) (= valin-5-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-5 #b10111) (= valin-5-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-6 #b00001) (= valin-6-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-6 #b00010) (= valin-6-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-6 #b00011) (= valin-6-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-6 #b00100) (= valin-6-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-6 #b00101) (= valin-6-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-6 #b00110) (= valin-6-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-6 #b00111) (= valin-6-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-6 #b01000) (= valin-6-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-6 #b01001) (= valin-6-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-6 #b01010) (= valin-6-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-6 #b01011) (= valin-6-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-6 #b01100) (= valin-6-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-6 #b01101) (= valin-6-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-6 #b01110) (= valin-6-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-6 #b01111) (= valin-6-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-6 #b10000) (= valin-6-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-6 #b10001) (= valin-6-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-6 #b10010) (= valin-6-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-6 #b10011) (= valin-6-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-6 #b10100) (= valin-6-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-6 #b10101) (= valin-6-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-6 #b10110) (= valin-6-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-6 #b10111) (= valin-6-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-7 #b00001) (= valin-7-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-7 #b00010) (= valin-7-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-7 #b00011) (= valin-7-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-7 #b00100) (= valin-7-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-7 #b00101) (= valin-7-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-7 #b00110) (= valin-7-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-7 #b00111) (= valin-7-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-7 #b01000) (= valin-7-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-7 #b01001) (= valin-7-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-7 #b01010) (= valin-7-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-7 #b01011) (= valin-7-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-7 #b01100) (= valin-7-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-7 #b01101) (= valin-7-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-7 #b01110) (= valin-7-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-7 #b01111) (= valin-7-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-7 #b10000) (= valin-7-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-7 #b10001) (= valin-7-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-7 #b10010) (= valin-7-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-7 #b10011) (= valin-7-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-7 #b10100) (= valin-7-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-7 #b10101) (= valin-7-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-7 #b10110) (= valin-7-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-7 #b10111) (= valin-7-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-8 #b00001) (= valin-8-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-8 #b00010) (= valin-8-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-8 #b00011) (= valin-8-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-8 #b00100) (= valin-8-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-8 #b00101) (= valin-8-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-8 #b00110) (= valin-8-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-8 #b00111) (= valin-8-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-8 #b01000) (= valin-8-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-8 #b01001) (= valin-8-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-8 #b01010) (= valin-8-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-8 #b01011) (= valin-8-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-8 #b01100) (= valin-8-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-8 #b01101) (= valin-8-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-8 #b01110) (= valin-8-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-8 #b01111) (= valin-8-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-8 #b10000) (= valin-8-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-8 #b10001) (= valin-8-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-8 #b10010) (= valin-8-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-8 #b10011) (= valin-8-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-8 #b10100) (= valin-8-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-8 #b10101) (= valin-8-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-8 #b10110) (= valin-8-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-8 #b10111) (= valin-8-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-9 #b00001) (= valin-9-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-9 #b00010) (= valin-9-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-9 #b00011) (= valin-9-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-9 #b00100) (= valin-9-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-9 #b00101) (= valin-9-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-9 #b00110) (= valin-9-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-9 #b00111) (= valin-9-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-9 #b01000) (= valin-9-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-9 #b01001) (= valin-9-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-9 #b01010) (= valin-9-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-9 #b01011) (= valin-9-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-9 #b01100) (= valin-9-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-9 #b01101) (= valin-9-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-9 #b01110) (= valin-9-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-9 #b01111) (= valin-9-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-9 #b10000) (= valin-9-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-9 #b10001) (= valin-9-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-9 #b10010) (= valin-9-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-9 #b10011) (= valin-9-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-9 #b10100) (= valin-9-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-9 #b10101) (= valin-9-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-9 #b10110) (= valin-9-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-9 #b10111) (= valin-9-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-10 #b00001) (= valin-10-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-10 #b00010) (= valin-10-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-10 #b00011) (= valin-10-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-10 #b00100) (= valin-10-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-10 #b00101) (= valin-10-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-10 #b00110) (= valin-10-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-10 #b00111) (= valin-10-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-10 #b01000) (= valin-10-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-10 #b01001) (= valin-10-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-10 #b01010) (= valin-10-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-10 #b01011) (= valin-10-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-10 #b01100) (= valin-10-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-10 #b01101) (= valin-10-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-10 #b01110) (= valin-10-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-10 #b01111) (= valin-10-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-10 #b10000) (= valin-10-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-10 #b10001) (= valin-10-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-10 #b10010) (= valin-10-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-10 #b10011) (= valin-10-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-10 #b10100) (= valin-10-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-10 #b10101) (= valin-10-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-10 #b10110) (= valin-10-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-10 #b10111) (= valin-10-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-11 #b00001) (= valin-11-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-11 #b00010) (= valin-11-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-11 #b00011) (= valin-11-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-11 #b00100) (= valin-11-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-11 #b00101) (= valin-11-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-11 #b00110) (= valin-11-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-11 #b00111) (= valin-11-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-11 #b01000) (= valin-11-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-11 #b01001) (= valin-11-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-11 #b01010) (= valin-11-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-11 #b01011) (= valin-11-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-11 #b01100) (= valin-11-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-11 #b01101) (= valin-11-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-11 #b01110) (= valin-11-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-11 #b01111) (= valin-11-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-11 #b10000) (= valin-11-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-11 #b10001) (= valin-11-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-11 #b10010) (= valin-11-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-11 #b10011) (= valin-11-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-11 #b10100) (= valin-11-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-11 #b10101) (= valin-11-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-11 #b10110) (= valin-11-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-11 #b10111) (= valin-11-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-12 #b00001) (= valin-12-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-12 #b00010) (= valin-12-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-12 #b00011) (= valin-12-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-12 #b00100) (= valin-12-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-12 #b00101) (= valin-12-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-12 #b00110) (= valin-12-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-12 #b00111) (= valin-12-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-12 #b01000) (= valin-12-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-12 #b01001) (= valin-12-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-12 #b01010) (= valin-12-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-12 #b01011) (= valin-12-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-12 #b01100) (= valin-12-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-12 #b01101) (= valin-12-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-12 #b01110) (= valin-12-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-12 #b01111) (= valin-12-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-12 #b10000) (= valin-12-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-12 #b10001) (= valin-12-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-12 #b10010) (= valin-12-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-12 #b10011) (= valin-12-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-12 #b10100) (= valin-12-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-12 #b10101) (= valin-12-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-12 #b10110) (= valin-12-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-12 #b10111) (= valin-12-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-13 #b00001) (= valin-13-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-13 #b00010) (= valin-13-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-13 #b00011) (= valin-13-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-13 #b00100) (= valin-13-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-13 #b00101) (= valin-13-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-13 #b00110) (= valin-13-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-13 #b00111) (= valin-13-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-13 #b01000) (= valin-13-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-13 #b01001) (= valin-13-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-13 #b01010) (= valin-13-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-13 #b01011) (= valin-13-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-13 #b01100) (= valin-13-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-13 #b01101) (= valin-13-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-13 #b01110) (= valin-13-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-13 #b01111) (= valin-13-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-13 #b10000) (= valin-13-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-13 #b10001) (= valin-13-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-13 #b10010) (= valin-13-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-13 #b10011) (= valin-13-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-13 #b10100) (= valin-13-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-13 #b10101) (= valin-13-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-13 #b10110) (= valin-13-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-13 #b10111) (= valin-13-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-14 #b00001) (= valin-14-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-14 #b00010) (= valin-14-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-14 #b00011) (= valin-14-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-14 #b00100) (= valin-14-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-14 #b00101) (= valin-14-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-14 #b00110) (= valin-14-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-14 #b00111) (= valin-14-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-14 #b01000) (= valin-14-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-14 #b01001) (= valin-14-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-14 #b01010) (= valin-14-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-14 #b01011) (= valin-14-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-14 #b01100) (= valin-14-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-14 #b01101) (= valin-14-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-14 #b01110) (= valin-14-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-14 #b01111) (= valin-14-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-14 #b10000) (= valin-14-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-14 #b10001) (= valin-14-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-14 #b10010) (= valin-14-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-14 #b10011) (= valin-14-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-14 #b10100) (= valin-14-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-14 #b10101) (= valin-14-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-14 #b10110) (= valin-14-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-14 #b10111) (= valin-14-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-15 #b00001) (= valin-15-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-15 #b00010) (= valin-15-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-15 #b00011) (= valin-15-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-15 #b00100) (= valin-15-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-15 #b00101) (= valin-15-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-15 #b00110) (= valin-15-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-15 #b00111) (= valin-15-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-15 #b01000) (= valin-15-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-15 #b01001) (= valin-15-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-15 #b01010) (= valin-15-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-15 #b01011) (= valin-15-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-15 #b01100) (= valin-15-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-15 #b01101) (= valin-15-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-15 #b01110) (= valin-15-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-15 #b01111) (= valin-15-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-15 #b10000) (= valin-15-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-15 #b10001) (= valin-15-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-15 #b10010) (= valin-15-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-15 #b10011) (= valin-15-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-15 #b10100) (= valin-15-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-15 #b10101) (= valin-15-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-15 #b10110) (= valin-15-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-15 #b10111) (= valin-15-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-16 #b00001) (= valin-16-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-16 #b00010) (= valin-16-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-16 #b00011) (= valin-16-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-16 #b00100) (= valin-16-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-16 #b00101) (= valin-16-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-16 #b00110) (= valin-16-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-16 #b00111) (= valin-16-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-16 #b01000) (= valin-16-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-16 #b01001) (= valin-16-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-16 #b01010) (= valin-16-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-16 #b01011) (= valin-16-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-16 #b01100) (= valin-16-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-16 #b01101) (= valin-16-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-16 #b01110) (= valin-16-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-16 #b01111) (= valin-16-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-16 #b10000) (= valin-16-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-16 #b10001) (= valin-16-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-16 #b10010) (= valin-16-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-16 #b10011) (= valin-16-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-16 #b10100) (= valin-16-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-16 #b10101) (= valin-16-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-16 #b10110) (= valin-16-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-16 #b10111) (= valin-16-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-17 #b00001) (= valin-17-'`I'` valout-1-'`I'`)))'
;`(assert (=> (= in-17 #b00010) (= valin-17-'`I'` valout-2-'`I'`)))'
`(assert (=> (= in-17 #b00011) (= valin-17-'`I'` valout-3-'`I'`)))'
;`(assert (=> (= in-17 #b00100) (= valin-17-'`I'` valout-4-'`I'`)))'
`(assert (=> (= in-17 #b00101) (= valin-17-'`I'` valout-5-'`I'`)))'
;`(assert (=> (= in-17 #b00110) (= valin-17-'`I'` valout-6-'`I'`)))'
;`(assert (=> (= in-17 #b00111) (= valin-17-'`I'` valout-7-'`I'`)))'
;`(assert (=> (= in-17 #b01000) (= valin-17-'`I'` valout-8-'`I'`)))'
;`(assert (=> (= in-17 #b01001) (= valin-17-'`I'` valout-9-'`I'`)))'
;`(assert (=> (= in-17 #b01010) (= valin-17-'`I'` valout-10-'`I'`)))'
;`(assert (=> (= in-17 #b01011) (= valin-17-'`I'` valout-11-'`I'`)))'
;`(assert (=> (= in-17 #b01100) (= valin-17-'`I'` valout-12-'`I'`)))'
;`(assert (=> (= in-17 #b01101) (= valin-17-'`I'` valout-13-'`I'`)))'
;`(assert (=> (= in-17 #b01110) (= valin-17-'`I'` valout-14-'`I'`)))'
;`(assert (=> (= in-17 #b01111) (= valin-17-'`I'` valout-15-'`I'`)))'
;`(assert (=> (= in-17 #b10000) (= valin-17-'`I'` valout-16-'`I'`)))'
;`(assert (=> (= in-17 #b10001) (= valin-17-'`I'` valout-17-'`I'`)))'
;`(assert (=> (= in-17 #b10010) (= valin-17-'`I'` valout-18-'`I'`)))'
;`(assert (=> (= in-17 #b10011) (= valin-17-'`I'` valout-19-'`I'`)))'
`(assert (=> (= in-17 #b10100) (= valin-17-'`I'` valout-20-'`I'`)))'
`(assert (=> (= in-17 #b10101) (= valin-17-'`I'` valout-21-'`I'`)))'
`(assert (=> (= in-17 #b10110) (= valin-17-'`I'` valout-22-'`I'`)))'
`(assert (=> (= in-17 #b10111) (= valin-17-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-18 #b00001) (= valin-18-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-18 #b00010) (= valin-18-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-18 #b00011) (= valin-18-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-18 #b00100) (= valin-18-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-18 #b00101) (= valin-18-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-18 #b00110) (= valin-18-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-18 #b00111) (= valin-18-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-18 #b01000) (= valin-18-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-18 #b01001) (= valin-18-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-18 #b01010) (= valin-18-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-18 #b01011) (= valin-18-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-18 #b01100) (= valin-18-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-18 #b01101) (= valin-18-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-18 #b01110) (= valin-18-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-18 #b01111) (= valin-18-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-18 #b10000) (= valin-18-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-18 #b10001) (= valin-18-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-18 #b10010) (= valin-18-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-18 #b10011) (= valin-18-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-18 #b10100) (= valin-18-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-18 #b10101) (= valin-18-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-18 #b10110) (= valin-18-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-18 #b10111) (= valin-18-'`I'` valout-23-'`I'`)))'

;`(assert (=> (= in-19 #b00001) (= valin-19-'`I'` valout-1-'`I'`)))'
`(assert (=> (= in-19 #b00010) (= valin-19-'`I'` valout-2-'`I'`)))'
;`(assert (=> (= in-19 #b00011) (= valin-19-'`I'` valout-3-'`I'`)))'
`(assert (=> (= in-19 #b00100) (= valin-19-'`I'` valout-4-'`I'`)))'
;`(assert (=> (= in-19 #b00101) (= valin-19-'`I'` valout-5-'`I'`)))'
`(assert (=> (= in-19 #b00110) (= valin-19-'`I'` valout-6-'`I'`)))'
`(assert (=> (= in-19 #b00111) (= valin-19-'`I'` valout-7-'`I'`)))'
`(assert (=> (= in-19 #b01000) (= valin-19-'`I'` valout-8-'`I'`)))'
`(assert (=> (= in-19 #b01001) (= valin-19-'`I'` valout-9-'`I'`)))'
`(assert (=> (= in-19 #b01010) (= valin-19-'`I'` valout-10-'`I'`)))'
`(assert (=> (= in-19 #b01011) (= valin-19-'`I'` valout-11-'`I'`)))'
`(assert (=> (= in-19 #b01100) (= valin-19-'`I'` valout-12-'`I'`)))'
`(assert (=> (= in-19 #b01101) (= valin-19-'`I'` valout-13-'`I'`)))'
`(assert (=> (= in-19 #b01110) (= valin-19-'`I'` valout-14-'`I'`)))'
`(assert (=> (= in-19 #b01111) (= valin-19-'`I'` valout-15-'`I'`)))'
`(assert (=> (= in-19 #b10000) (= valin-19-'`I'` valout-16-'`I'`)))'
`(assert (=> (= in-19 #b10001) (= valin-19-'`I'` valout-17-'`I'`)))'
`(assert (=> (= in-19 #b10010) (= valin-19-'`I'` valout-18-'`I'`)))'
`(assert (=> (= in-19 #b10011) (= valin-19-'`I'` valout-19-'`I'`)))'
;`(assert (=> (= in-19 #b10100) (= valin-19-'`I'` valout-20-'`I'`)))'
;`(assert (=> (= in-19 #b10101) (= valin-19-'`I'` valout-21-'`I'`)))'
;`(assert (=> (= in-19 #b10110) (= valin-19-'`I'` valout-22-'`I'`)))'
;`(assert (=> (= in-19 #b10111) (= valin-19-'`I'` valout-23-'`I'`)))'
)

; Copy of above with in-->ina valin-->valina valout-->valouta
ifdef(`DIST',dnl
forloop(`I',1,NEXT,dnl 
`(assert (=> (= ina-1 #b00001) (= valina-1-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-1 #b00010) (= valina-1-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-1 #b00011) (= valina-1-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-1 #b00100) (= valina-1-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-1 #b00101) (= valina-1-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-1 #b00110) (= valina-1-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-1 #b00111) (= valina-1-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-1 #b01000) (= valina-1-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-1 #b01001) (= valina-1-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-1 #b01010) (= valina-1-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-1 #b01011) (= valina-1-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-1 #b01100) (= valina-1-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-1 #b01101) (= valina-1-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-1 #b01110) (= valina-1-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-1 #b01111) (= valina-1-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-1 #b10000) (= valina-1-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-1 #b10001) (= valina-1-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-1 #b10010) (= valina-1-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-1 #b10011) (= valina-1-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-1 #b10100) (= valina-1-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-1 #b10101) (= valina-1-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-1 #b10110) (= valina-1-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-1 #b10111) (= valina-1-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-2 #b00001) (= valina-2-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-2 #b00010) (= valina-2-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-2 #b00011) (= valina-2-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-2 #b00100) (= valina-2-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-2 #b00101) (= valina-2-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-2 #b00110) (= valina-2-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-2 #b00111) (= valina-2-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-2 #b01000) (= valina-2-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-2 #b01001) (= valina-2-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-2 #b01010) (= valina-2-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-2 #b01011) (= valina-2-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-2 #b01100) (= valina-2-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-2 #b01101) (= valina-2-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-2 #b01110) (= valina-2-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-2 #b01111) (= valina-2-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-2 #b10000) (= valina-2-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-2 #b10001) (= valina-2-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-2 #b10010) (= valina-2-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-2 #b10011) (= valina-2-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-2 #b10100) (= valina-2-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-2 #b10101) (= valina-2-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-2 #b10110) (= valina-2-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-2 #b10111) (= valina-2-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-3 #b00001) (= valina-3-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-3 #b00010) (= valina-3-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-3 #b00011) (= valina-3-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-3 #b00100) (= valina-3-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-3 #b00101) (= valina-3-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-3 #b00110) (= valina-3-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-3 #b00111) (= valina-3-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-3 #b01000) (= valina-3-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-3 #b01001) (= valina-3-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-3 #b01010) (= valina-3-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-3 #b01011) (= valina-3-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-3 #b01100) (= valina-3-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-3 #b01101) (= valina-3-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-3 #b01110) (= valina-3-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-3 #b01111) (= valina-3-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-3 #b10000) (= valina-3-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-3 #b10001) (= valina-3-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-3 #b10010) (= valina-3-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-3 #b10011) (= valina-3-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-3 #b10100) (= valina-3-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-3 #b10101) (= valina-3-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-3 #b10110) (= valina-3-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-3 #b10111) (= valina-3-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-4 #b00001) (= valina-4-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-4 #b00010) (= valina-4-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-4 #b00011) (= valina-4-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-4 #b00100) (= valina-4-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-4 #b00101) (= valina-4-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-4 #b00110) (= valina-4-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-4 #b00111) (= valina-4-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-4 #b01000) (= valina-4-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-4 #b01001) (= valina-4-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-4 #b01010) (= valina-4-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-4 #b01011) (= valina-4-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-4 #b01100) (= valina-4-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-4 #b01101) (= valina-4-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-4 #b01110) (= valina-4-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-4 #b01111) (= valina-4-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-4 #b10000) (= valina-4-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-4 #b10001) (= valina-4-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-4 #b10010) (= valina-4-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-4 #b10011) (= valina-4-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-4 #b10100) (= valina-4-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-4 #b10101) (= valina-4-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-4 #b10110) (= valina-4-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-4 #b10111) (= valina-4-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-5 #b00001) (= valina-5-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-5 #b00010) (= valina-5-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-5 #b00011) (= valina-5-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-5 #b00100) (= valina-5-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-5 #b00101) (= valina-5-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-5 #b00110) (= valina-5-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-5 #b00111) (= valina-5-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-5 #b01000) (= valina-5-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-5 #b01001) (= valina-5-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-5 #b01010) (= valina-5-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-5 #b01011) (= valina-5-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-5 #b01100) (= valina-5-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-5 #b01101) (= valina-5-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-5 #b01110) (= valina-5-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-5 #b01111) (= valina-5-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-5 #b10000) (= valina-5-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-5 #b10001) (= valina-5-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-5 #b10010) (= valina-5-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-5 #b10011) (= valina-5-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-5 #b10100) (= valina-5-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-5 #b10101) (= valina-5-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-5 #b10110) (= valina-5-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-5 #b10111) (= valina-5-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-6 #b00001) (= valina-6-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-6 #b00010) (= valina-6-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-6 #b00011) (= valina-6-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-6 #b00100) (= valina-6-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-6 #b00101) (= valina-6-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-6 #b00110) (= valina-6-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-6 #b00111) (= valina-6-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-6 #b01000) (= valina-6-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-6 #b01001) (= valina-6-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-6 #b01010) (= valina-6-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-6 #b01011) (= valina-6-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-6 #b01100) (= valina-6-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-6 #b01101) (= valina-6-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-6 #b01110) (= valina-6-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-6 #b01111) (= valina-6-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-6 #b10000) (= valina-6-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-6 #b10001) (= valina-6-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-6 #b10010) (= valina-6-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-6 #b10011) (= valina-6-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-6 #b10100) (= valina-6-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-6 #b10101) (= valina-6-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-6 #b10110) (= valina-6-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-6 #b10111) (= valina-6-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-7 #b00001) (= valina-7-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-7 #b00010) (= valina-7-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-7 #b00011) (= valina-7-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-7 #b00100) (= valina-7-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-7 #b00101) (= valina-7-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-7 #b00110) (= valina-7-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-7 #b00111) (= valina-7-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-7 #b01000) (= valina-7-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-7 #b01001) (= valina-7-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-7 #b01010) (= valina-7-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-7 #b01011) (= valina-7-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-7 #b01100) (= valina-7-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-7 #b01101) (= valina-7-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-7 #b01110) (= valina-7-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-7 #b01111) (= valina-7-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-7 #b10000) (= valina-7-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-7 #b10001) (= valina-7-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-7 #b10010) (= valina-7-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-7 #b10011) (= valina-7-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-7 #b10100) (= valina-7-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-7 #b10101) (= valina-7-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-7 #b10110) (= valina-7-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-7 #b10111) (= valina-7-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-8 #b00001) (= valina-8-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-8 #b00010) (= valina-8-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-8 #b00011) (= valina-8-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-8 #b00100) (= valina-8-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-8 #b00101) (= valina-8-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-8 #b00110) (= valina-8-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-8 #b00111) (= valina-8-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-8 #b01000) (= valina-8-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-8 #b01001) (= valina-8-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-8 #b01010) (= valina-8-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-8 #b01011) (= valina-8-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-8 #b01100) (= valina-8-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-8 #b01101) (= valina-8-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-8 #b01110) (= valina-8-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-8 #b01111) (= valina-8-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-8 #b10000) (= valina-8-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-8 #b10001) (= valina-8-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-8 #b10010) (= valina-8-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-8 #b10011) (= valina-8-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-8 #b10100) (= valina-8-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-8 #b10101) (= valina-8-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-8 #b10110) (= valina-8-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-8 #b10111) (= valina-8-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-9 #b00001) (= valina-9-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-9 #b00010) (= valina-9-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-9 #b00011) (= valina-9-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-9 #b00100) (= valina-9-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-9 #b00101) (= valina-9-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-9 #b00110) (= valina-9-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-9 #b00111) (= valina-9-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-9 #b01000) (= valina-9-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-9 #b01001) (= valina-9-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-9 #b01010) (= valina-9-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-9 #b01011) (= valina-9-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-9 #b01100) (= valina-9-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-9 #b01101) (= valina-9-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-9 #b01110) (= valina-9-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-9 #b01111) (= valina-9-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-9 #b10000) (= valina-9-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-9 #b10001) (= valina-9-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-9 #b10010) (= valina-9-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-9 #b10011) (= valina-9-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-9 #b10100) (= valina-9-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-9 #b10101) (= valina-9-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-9 #b10110) (= valina-9-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-9 #b10111) (= valina-9-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-10 #b00001) (= valina-10-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-10 #b00010) (= valina-10-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-10 #b00011) (= valina-10-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-10 #b00100) (= valina-10-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-10 #b00101) (= valina-10-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-10 #b00110) (= valina-10-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-10 #b00111) (= valina-10-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-10 #b01000) (= valina-10-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-10 #b01001) (= valina-10-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-10 #b01010) (= valina-10-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-10 #b01011) (= valina-10-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-10 #b01100) (= valina-10-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-10 #b01101) (= valina-10-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-10 #b01110) (= valina-10-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-10 #b01111) (= valina-10-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-10 #b10000) (= valina-10-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-10 #b10001) (= valina-10-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-10 #b10010) (= valina-10-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-10 #b10011) (= valina-10-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-10 #b10100) (= valina-10-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-10 #b10101) (= valina-10-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-10 #b10110) (= valina-10-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-10 #b10111) (= valina-10-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-11 #b00001) (= valina-11-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-11 #b00010) (= valina-11-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-11 #b00011) (= valina-11-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-11 #b00100) (= valina-11-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-11 #b00101) (= valina-11-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-11 #b00110) (= valina-11-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-11 #b00111) (= valina-11-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-11 #b01000) (= valina-11-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-11 #b01001) (= valina-11-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-11 #b01010) (= valina-11-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-11 #b01011) (= valina-11-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-11 #b01100) (= valina-11-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-11 #b01101) (= valina-11-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-11 #b01110) (= valina-11-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-11 #b01111) (= valina-11-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-11 #b10000) (= valina-11-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-11 #b10001) (= valina-11-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-11 #b10010) (= valina-11-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-11 #b10011) (= valina-11-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-11 #b10100) (= valina-11-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-11 #b10101) (= valina-11-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-11 #b10110) (= valina-11-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-11 #b10111) (= valina-11-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-12 #b00001) (= valina-12-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-12 #b00010) (= valina-12-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-12 #b00011) (= valina-12-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-12 #b00100) (= valina-12-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-12 #b00101) (= valina-12-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-12 #b00110) (= valina-12-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-12 #b00111) (= valina-12-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-12 #b01000) (= valina-12-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-12 #b01001) (= valina-12-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-12 #b01010) (= valina-12-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-12 #b01011) (= valina-12-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-12 #b01100) (= valina-12-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-12 #b01101) (= valina-12-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-12 #b01110) (= valina-12-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-12 #b01111) (= valina-12-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-12 #b10000) (= valina-12-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-12 #b10001) (= valina-12-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-12 #b10010) (= valina-12-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-12 #b10011) (= valina-12-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-12 #b10100) (= valina-12-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-12 #b10101) (= valina-12-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-12 #b10110) (= valina-12-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-12 #b10111) (= valina-12-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-13 #b00001) (= valina-13-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-13 #b00010) (= valina-13-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-13 #b00011) (= valina-13-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-13 #b00100) (= valina-13-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-13 #b00101) (= valina-13-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-13 #b00110) (= valina-13-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-13 #b00111) (= valina-13-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-13 #b01000) (= valina-13-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-13 #b01001) (= valina-13-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-13 #b01010) (= valina-13-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-13 #b01011) (= valina-13-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-13 #b01100) (= valina-13-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-13 #b01101) (= valina-13-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-13 #b01110) (= valina-13-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-13 #b01111) (= valina-13-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-13 #b10000) (= valina-13-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-13 #b10001) (= valina-13-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-13 #b10010) (= valina-13-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-13 #b10011) (= valina-13-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-13 #b10100) (= valina-13-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-13 #b10101) (= valina-13-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-13 #b10110) (= valina-13-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-13 #b10111) (= valina-13-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-14 #b00001) (= valina-14-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-14 #b00010) (= valina-14-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-14 #b00011) (= valina-14-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-14 #b00100) (= valina-14-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-14 #b00101) (= valina-14-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-14 #b00110) (= valina-14-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-14 #b00111) (= valina-14-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-14 #b01000) (= valina-14-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-14 #b01001) (= valina-14-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-14 #b01010) (= valina-14-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-14 #b01011) (= valina-14-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-14 #b01100) (= valina-14-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-14 #b01101) (= valina-14-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-14 #b01110) (= valina-14-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-14 #b01111) (= valina-14-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-14 #b10000) (= valina-14-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-14 #b10001) (= valina-14-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-14 #b10010) (= valina-14-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-14 #b10011) (= valina-14-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-14 #b10100) (= valina-14-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-14 #b10101) (= valina-14-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-14 #b10110) (= valina-14-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-14 #b10111) (= valina-14-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-15 #b00001) (= valina-15-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-15 #b00010) (= valina-15-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-15 #b00011) (= valina-15-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-15 #b00100) (= valina-15-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-15 #b00101) (= valina-15-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-15 #b00110) (= valina-15-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-15 #b00111) (= valina-15-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-15 #b01000) (= valina-15-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-15 #b01001) (= valina-15-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-15 #b01010) (= valina-15-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-15 #b01011) (= valina-15-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-15 #b01100) (= valina-15-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-15 #b01101) (= valina-15-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-15 #b01110) (= valina-15-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-15 #b01111) (= valina-15-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-15 #b10000) (= valina-15-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-15 #b10001) (= valina-15-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-15 #b10010) (= valina-15-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-15 #b10011) (= valina-15-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-15 #b10100) (= valina-15-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-15 #b10101) (= valina-15-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-15 #b10110) (= valina-15-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-15 #b10111) (= valina-15-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-16 #b00001) (= valina-16-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-16 #b00010) (= valina-16-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-16 #b00011) (= valina-16-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-16 #b00100) (= valina-16-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-16 #b00101) (= valina-16-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-16 #b00110) (= valina-16-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-16 #b00111) (= valina-16-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-16 #b01000) (= valina-16-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-16 #b01001) (= valina-16-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-16 #b01010) (= valina-16-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-16 #b01011) (= valina-16-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-16 #b01100) (= valina-16-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-16 #b01101) (= valina-16-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-16 #b01110) (= valina-16-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-16 #b01111) (= valina-16-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-16 #b10000) (= valina-16-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-16 #b10001) (= valina-16-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-16 #b10010) (= valina-16-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-16 #b10011) (= valina-16-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-16 #b10100) (= valina-16-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-16 #b10101) (= valina-16-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-16 #b10110) (= valina-16-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-16 #b10111) (= valina-16-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-17 #b00001) (= valina-17-'`I'` valouta-1-'`I'`)))'
;`(assert (=> (= ina-17 #b00010) (= valina-17-'`I'` valouta-2-'`I'`)))'
`(assert (=> (= ina-17 #b00011) (= valina-17-'`I'` valouta-3-'`I'`)))'
;`(assert (=> (= ina-17 #b00100) (= valina-17-'`I'` valouta-4-'`I'`)))'
`(assert (=> (= ina-17 #b00101) (= valina-17-'`I'` valouta-5-'`I'`)))'
;`(assert (=> (= ina-17 #b00110) (= valina-17-'`I'` valouta-6-'`I'`)))'
;`(assert (=> (= ina-17 #b00111) (= valina-17-'`I'` valouta-7-'`I'`)))'
;`(assert (=> (= ina-17 #b01000) (= valina-17-'`I'` valouta-8-'`I'`)))'
;`(assert (=> (= ina-17 #b01001) (= valina-17-'`I'` valouta-9-'`I'`)))'
;`(assert (=> (= ina-17 #b01010) (= valina-17-'`I'` valouta-10-'`I'`)))'
;`(assert (=> (= ina-17 #b01011) (= valina-17-'`I'` valouta-11-'`I'`)))'
;`(assert (=> (= ina-17 #b01100) (= valina-17-'`I'` valouta-12-'`I'`)))'
;`(assert (=> (= ina-17 #b01101) (= valina-17-'`I'` valouta-13-'`I'`)))'
;`(assert (=> (= ina-17 #b01110) (= valina-17-'`I'` valouta-14-'`I'`)))'
;`(assert (=> (= ina-17 #b01111) (= valina-17-'`I'` valouta-15-'`I'`)))'
;`(assert (=> (= ina-17 #b10000) (= valina-17-'`I'` valouta-16-'`I'`)))'
;`(assert (=> (= ina-17 #b10001) (= valina-17-'`I'` valouta-17-'`I'`)))'
;`(assert (=> (= ina-17 #b10010) (= valina-17-'`I'` valouta-18-'`I'`)))'
;`(assert (=> (= ina-17 #b10011) (= valina-17-'`I'` valouta-19-'`I'`)))'
`(assert (=> (= ina-17 #b10100) (= valina-17-'`I'` valouta-20-'`I'`)))'
`(assert (=> (= ina-17 #b10101) (= valina-17-'`I'` valouta-21-'`I'`)))'
`(assert (=> (= ina-17 #b10110) (= valina-17-'`I'` valouta-22-'`I'`)))'
`(assert (=> (= ina-17 #b10111) (= valina-17-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-18 #b00001) (= valina-18-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-18 #b00010) (= valina-18-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-18 #b00011) (= valina-18-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-18 #b00100) (= valina-18-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-18 #b00101) (= valina-18-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-18 #b00110) (= valina-18-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-18 #b00111) (= valina-18-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-18 #b01000) (= valina-18-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-18 #b01001) (= valina-18-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-18 #b01010) (= valina-18-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-18 #b01011) (= valina-18-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-18 #b01100) (= valina-18-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-18 #b01101) (= valina-18-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-18 #b01110) (= valina-18-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-18 #b01111) (= valina-18-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-18 #b10000) (= valina-18-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-18 #b10001) (= valina-18-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-18 #b10010) (= valina-18-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-18 #b10011) (= valina-18-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-18 #b10100) (= valina-18-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-18 #b10101) (= valina-18-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-18 #b10110) (= valina-18-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-18 #b10111) (= valina-18-'`I'` valouta-23-'`I'`)))'

;`(assert (=> (= ina-19 #b00001) (= valina-19-'`I'` valouta-1-'`I'`)))'
`(assert (=> (= ina-19 #b00010) (= valina-19-'`I'` valouta-2-'`I'`)))'
;`(assert (=> (= ina-19 #b00011) (= valina-19-'`I'` valouta-3-'`I'`)))'
`(assert (=> (= ina-19 #b00100) (= valina-19-'`I'` valouta-4-'`I'`)))'
;`(assert (=> (= ina-19 #b00101) (= valina-19-'`I'` valouta-5-'`I'`)))'
`(assert (=> (= ina-19 #b00110) (= valina-19-'`I'` valouta-6-'`I'`)))'
`(assert (=> (= ina-19 #b00111) (= valina-19-'`I'` valouta-7-'`I'`)))'
`(assert (=> (= ina-19 #b01000) (= valina-19-'`I'` valouta-8-'`I'`)))'
`(assert (=> (= ina-19 #b01001) (= valina-19-'`I'` valouta-9-'`I'`)))'
`(assert (=> (= ina-19 #b01010) (= valina-19-'`I'` valouta-10-'`I'`)))'
`(assert (=> (= ina-19 #b01011) (= valina-19-'`I'` valouta-11-'`I'`)))'
`(assert (=> (= ina-19 #b01100) (= valina-19-'`I'` valouta-12-'`I'`)))'
`(assert (=> (= ina-19 #b01101) (= valina-19-'`I'` valouta-13-'`I'`)))'
`(assert (=> (= ina-19 #b01110) (= valina-19-'`I'` valouta-14-'`I'`)))'
`(assert (=> (= ina-19 #b01111) (= valina-19-'`I'` valouta-15-'`I'`)))'
`(assert (=> (= ina-19 #b10000) (= valina-19-'`I'` valouta-16-'`I'`)))'
`(assert (=> (= ina-19 #b10001) (= valina-19-'`I'` valouta-17-'`I'`)))'
`(assert (=> (= ina-19 #b10010) (= valina-19-'`I'` valouta-18-'`I'`)))'
`(assert (=> (= ina-19 #b10011) (= valina-19-'`I'` valouta-19-'`I'`)))'
;`(assert (=> (= ina-19 #b10100) (= valina-19-'`I'` valouta-20-'`I'`)))'
;`(assert (=> (= ina-19 #b10101) (= valina-19-'`I'` valouta-21-'`I'`)))'
;`(assert (=> (= ina-19 #b10110) (= valina-19-'`I'` valouta-22-'`I'`)))'
;`(assert (=> (= ina-19 #b10111) (= valina-19-'`I'` valouta-23-'`I'`)))'
)

; Copy of above for distinguishing input 
`(assert (=> (= in-1 #b00001) (= valin-1-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-1 #b00010) (= valin-1-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-1 #b00011) (= valin-1-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-1 #b00100) (= valin-1-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-1 #b00101) (= valin-1-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-1 #b00110) (= valin-1-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-1 #b00111) (= valin-1-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-1 #b01000) (= valin-1-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-1 #b01001) (= valin-1-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-1 #b01010) (= valin-1-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-1 #b01011) (= valin-1-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-1 #b01100) (= valin-1-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-1 #b01101) (= valin-1-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-1 #b01110) (= valin-1-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-1 #b01111) (= valin-1-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-1 #b10000) (= valin-1-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-1 #b10001) (= valin-1-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-1 #b10010) (= valin-1-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-1 #b10011) (= valin-1-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-1 #b10100) (= valin-1-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-1 #b10101) (= valin-1-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-1 #b10110) (= valin-1-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-1 #b10111) (= valin-1-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-2 #b00001) (= valin-2-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-2 #b00010) (= valin-2-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-2 #b00011) (= valin-2-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-2 #b00100) (= valin-2-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-2 #b00101) (= valin-2-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-2 #b00110) (= valin-2-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-2 #b00111) (= valin-2-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-2 #b01000) (= valin-2-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-2 #b01001) (= valin-2-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-2 #b01010) (= valin-2-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-2 #b01011) (= valin-2-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-2 #b01100) (= valin-2-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-2 #b01101) (= valin-2-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-2 #b01110) (= valin-2-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-2 #b01111) (= valin-2-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-2 #b10000) (= valin-2-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-2 #b10001) (= valin-2-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-2 #b10010) (= valin-2-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-2 #b10011) (= valin-2-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-2 #b10100) (= valin-2-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-2 #b10101) (= valin-2-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-2 #b10110) (= valin-2-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-2 #b10111) (= valin-2-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-3 #b00001) (= valin-3-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-3 #b00010) (= valin-3-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-3 #b00011) (= valin-3-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-3 #b00100) (= valin-3-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-3 #b00101) (= valin-3-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-3 #b00110) (= valin-3-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-3 #b00111) (= valin-3-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-3 #b01000) (= valin-3-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-3 #b01001) (= valin-3-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-3 #b01010) (= valin-3-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-3 #b01011) (= valin-3-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-3 #b01100) (= valin-3-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-3 #b01101) (= valin-3-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-3 #b01110) (= valin-3-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-3 #b01111) (= valin-3-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-3 #b10000) (= valin-3-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-3 #b10001) (= valin-3-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-3 #b10010) (= valin-3-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-3 #b10011) (= valin-3-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-3 #b10100) (= valin-3-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-3 #b10101) (= valin-3-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-3 #b10110) (= valin-3-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-3 #b10111) (= valin-3-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-4 #b00001) (= valin-4-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-4 #b00010) (= valin-4-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-4 #b00011) (= valin-4-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-4 #b00100) (= valin-4-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-4 #b00101) (= valin-4-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-4 #b00110) (= valin-4-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-4 #b00111) (= valin-4-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-4 #b01000) (= valin-4-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-4 #b01001) (= valin-4-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-4 #b01010) (= valin-4-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-4 #b01011) (= valin-4-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-4 #b01100) (= valin-4-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-4 #b01101) (= valin-4-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-4 #b01110) (= valin-4-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-4 #b01111) (= valin-4-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-4 #b10000) (= valin-4-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-4 #b10001) (= valin-4-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-4 #b10010) (= valin-4-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-4 #b10011) (= valin-4-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-4 #b10100) (= valin-4-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-4 #b10101) (= valin-4-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-4 #b10110) (= valin-4-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-4 #b10111) (= valin-4-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-5 #b00001) (= valin-5-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-5 #b00010) (= valin-5-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-5 #b00011) (= valin-5-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-5 #b00100) (= valin-5-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-5 #b00101) (= valin-5-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-5 #b00110) (= valin-5-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-5 #b00111) (= valin-5-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-5 #b01000) (= valin-5-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-5 #b01001) (= valin-5-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-5 #b01010) (= valin-5-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-5 #b01011) (= valin-5-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-5 #b01100) (= valin-5-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-5 #b01101) (= valin-5-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-5 #b01110) (= valin-5-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-5 #b01111) (= valin-5-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-5 #b10000) (= valin-5-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-5 #b10001) (= valin-5-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-5 #b10010) (= valin-5-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-5 #b10011) (= valin-5-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-5 #b10100) (= valin-5-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-5 #b10101) (= valin-5-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-5 #b10110) (= valin-5-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-5 #b10111) (= valin-5-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-6 #b00001) (= valin-6-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-6 #b00010) (= valin-6-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-6 #b00011) (= valin-6-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-6 #b00100) (= valin-6-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-6 #b00101) (= valin-6-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-6 #b00110) (= valin-6-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-6 #b00111) (= valin-6-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-6 #b01000) (= valin-6-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-6 #b01001) (= valin-6-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-6 #b01010) (= valin-6-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-6 #b01011) (= valin-6-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-6 #b01100) (= valin-6-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-6 #b01101) (= valin-6-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-6 #b01110) (= valin-6-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-6 #b01111) (= valin-6-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-6 #b10000) (= valin-6-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-6 #b10001) (= valin-6-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-6 #b10010) (= valin-6-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-6 #b10011) (= valin-6-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-6 #b10100) (= valin-6-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-6 #b10101) (= valin-6-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-6 #b10110) (= valin-6-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-6 #b10111) (= valin-6-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-7 #b00001) (= valin-7-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-7 #b00010) (= valin-7-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-7 #b00011) (= valin-7-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-7 #b00100) (= valin-7-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-7 #b00101) (= valin-7-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-7 #b00110) (= valin-7-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-7 #b00111) (= valin-7-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-7 #b01000) (= valin-7-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-7 #b01001) (= valin-7-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-7 #b01010) (= valin-7-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-7 #b01011) (= valin-7-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-7 #b01100) (= valin-7-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-7 #b01101) (= valin-7-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-7 #b01110) (= valin-7-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-7 #b01111) (= valin-7-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-7 #b10000) (= valin-7-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-7 #b10001) (= valin-7-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-7 #b10010) (= valin-7-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-7 #b10011) (= valin-7-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-7 #b10100) (= valin-7-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-7 #b10101) (= valin-7-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-7 #b10110) (= valin-7-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-7 #b10111) (= valin-7-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-8 #b00001) (= valin-8-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-8 #b00010) (= valin-8-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-8 #b00011) (= valin-8-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-8 #b00100) (= valin-8-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-8 #b00101) (= valin-8-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-8 #b00110) (= valin-8-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-8 #b00111) (= valin-8-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-8 #b01000) (= valin-8-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-8 #b01001) (= valin-8-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-8 #b01010) (= valin-8-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-8 #b01011) (= valin-8-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-8 #b01100) (= valin-8-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-8 #b01101) (= valin-8-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-8 #b01110) (= valin-8-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-8 #b01111) (= valin-8-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-8 #b10000) (= valin-8-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-8 #b10001) (= valin-8-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-8 #b10010) (= valin-8-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-8 #b10011) (= valin-8-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-8 #b10100) (= valin-8-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-8 #b10101) (= valin-8-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-8 #b10110) (= valin-8-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-8 #b10111) (= valin-8-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-9 #b00001) (= valin-9-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-9 #b00010) (= valin-9-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-9 #b00011) (= valin-9-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-9 #b00100) (= valin-9-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-9 #b00101) (= valin-9-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-9 #b00110) (= valin-9-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-9 #b00111) (= valin-9-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-9 #b01000) (= valin-9-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-9 #b01001) (= valin-9-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-9 #b01010) (= valin-9-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-9 #b01011) (= valin-9-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-9 #b01100) (= valin-9-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-9 #b01101) (= valin-9-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-9 #b01110) (= valin-9-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-9 #b01111) (= valin-9-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-9 #b10000) (= valin-9-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-9 #b10001) (= valin-9-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-9 #b10010) (= valin-9-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-9 #b10011) (= valin-9-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-9 #b10100) (= valin-9-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-9 #b10101) (= valin-9-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-9 #b10110) (= valin-9-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-9 #b10111) (= valin-9-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-10 #b00001) (= valin-10-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-10 #b00010) (= valin-10-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-10 #b00011) (= valin-10-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-10 #b00100) (= valin-10-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-10 #b00101) (= valin-10-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-10 #b00110) (= valin-10-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-10 #b00111) (= valin-10-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-10 #b01000) (= valin-10-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-10 #b01001) (= valin-10-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-10 #b01010) (= valin-10-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-10 #b01011) (= valin-10-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-10 #b01100) (= valin-10-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-10 #b01101) (= valin-10-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-10 #b01110) (= valin-10-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-10 #b01111) (= valin-10-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-10 #b10000) (= valin-10-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-10 #b10001) (= valin-10-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-10 #b10010) (= valin-10-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-10 #b10011) (= valin-10-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-10 #b10100) (= valin-10-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-10 #b10101) (= valin-10-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-10 #b10110) (= valin-10-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-10 #b10111) (= valin-10-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-11 #b00001) (= valin-11-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-11 #b00010) (= valin-11-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-11 #b00011) (= valin-11-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-11 #b00100) (= valin-11-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-11 #b00101) (= valin-11-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-11 #b00110) (= valin-11-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-11 #b00111) (= valin-11-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-11 #b01000) (= valin-11-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-11 #b01001) (= valin-11-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-11 #b01010) (= valin-11-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-11 #b01011) (= valin-11-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-11 #b01100) (= valin-11-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-11 #b01101) (= valin-11-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-11 #b01110) (= valin-11-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-11 #b01111) (= valin-11-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-11 #b10000) (= valin-11-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-11 #b10001) (= valin-11-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-11 #b10010) (= valin-11-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-11 #b10011) (= valin-11-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-11 #b10100) (= valin-11-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-11 #b10101) (= valin-11-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-11 #b10110) (= valin-11-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-11 #b10111) (= valin-11-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-12 #b00001) (= valin-12-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-12 #b00010) (= valin-12-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-12 #b00011) (= valin-12-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-12 #b00100) (= valin-12-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-12 #b00101) (= valin-12-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-12 #b00110) (= valin-12-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-12 #b00111) (= valin-12-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-12 #b01000) (= valin-12-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-12 #b01001) (= valin-12-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-12 #b01010) (= valin-12-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-12 #b01011) (= valin-12-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-12 #b01100) (= valin-12-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-12 #b01101) (= valin-12-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-12 #b01110) (= valin-12-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-12 #b01111) (= valin-12-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-12 #b10000) (= valin-12-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-12 #b10001) (= valin-12-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-12 #b10010) (= valin-12-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-12 #b10011) (= valin-12-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-12 #b10100) (= valin-12-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-12 #b10101) (= valin-12-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-12 #b10110) (= valin-12-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-12 #b10111) (= valin-12-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-13 #b00001) (= valin-13-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-13 #b00010) (= valin-13-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-13 #b00011) (= valin-13-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-13 #b00100) (= valin-13-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-13 #b00101) (= valin-13-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-13 #b00110) (= valin-13-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-13 #b00111) (= valin-13-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-13 #b01000) (= valin-13-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-13 #b01001) (= valin-13-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-13 #b01010) (= valin-13-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-13 #b01011) (= valin-13-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-13 #b01100) (= valin-13-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-13 #b01101) (= valin-13-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-13 #b01110) (= valin-13-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-13 #b01111) (= valin-13-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-13 #b10000) (= valin-13-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-13 #b10001) (= valin-13-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-13 #b10010) (= valin-13-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-13 #b10011) (= valin-13-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-13 #b10100) (= valin-13-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-13 #b10101) (= valin-13-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-13 #b10110) (= valin-13-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-13 #b10111) (= valin-13-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-14 #b00001) (= valin-14-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-14 #b00010) (= valin-14-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-14 #b00011) (= valin-14-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-14 #b00100) (= valin-14-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-14 #b00101) (= valin-14-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-14 #b00110) (= valin-14-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-14 #b00111) (= valin-14-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-14 #b01000) (= valin-14-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-14 #b01001) (= valin-14-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-14 #b01010) (= valin-14-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-14 #b01011) (= valin-14-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-14 #b01100) (= valin-14-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-14 #b01101) (= valin-14-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-14 #b01110) (= valin-14-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-14 #b01111) (= valin-14-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-14 #b10000) (= valin-14-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-14 #b10001) (= valin-14-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-14 #b10010) (= valin-14-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-14 #b10011) (= valin-14-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-14 #b10100) (= valin-14-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-14 #b10101) (= valin-14-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-14 #b10110) (= valin-14-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-14 #b10111) (= valin-14-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-15 #b00001) (= valin-15-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-15 #b00010) (= valin-15-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-15 #b00011) (= valin-15-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-15 #b00100) (= valin-15-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-15 #b00101) (= valin-15-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-15 #b00110) (= valin-15-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-15 #b00111) (= valin-15-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-15 #b01000) (= valin-15-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-15 #b01001) (= valin-15-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-15 #b01010) (= valin-15-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-15 #b01011) (= valin-15-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-15 #b01100) (= valin-15-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-15 #b01101) (= valin-15-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-15 #b01110) (= valin-15-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-15 #b01111) (= valin-15-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-15 #b10000) (= valin-15-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-15 #b10001) (= valin-15-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-15 #b10010) (= valin-15-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-15 #b10011) (= valin-15-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-15 #b10100) (= valin-15-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-15 #b10101) (= valin-15-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-15 #b10110) (= valin-15-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-15 #b10111) (= valin-15-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-16 #b00001) (= valin-16-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-16 #b00010) (= valin-16-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-16 #b00011) (= valin-16-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-16 #b00100) (= valin-16-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-16 #b00101) (= valin-16-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-16 #b00110) (= valin-16-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-16 #b00111) (= valin-16-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-16 #b01000) (= valin-16-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-16 #b01001) (= valin-16-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-16 #b01010) (= valin-16-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-16 #b01011) (= valin-16-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-16 #b01100) (= valin-16-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-16 #b01101) (= valin-16-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-16 #b01110) (= valin-16-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-16 #b01111) (= valin-16-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-16 #b10000) (= valin-16-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-16 #b10001) (= valin-16-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-16 #b10010) (= valin-16-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-16 #b10011) (= valin-16-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-16 #b10100) (= valin-16-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-16 #b10101) (= valin-16-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-16 #b10110) (= valin-16-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-16 #b10111) (= valin-16-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-17 #b00001) (= valin-17-'NEXT` valout-1-'NEXT`)))'
;`(assert (=> (= in-17 #b00010) (= valin-17-'NEXT` valout-2-'NEXT`)))'
`(assert (=> (= in-17 #b00011) (= valin-17-'NEXT` valout-3-'NEXT`)))'
;`(assert (=> (= in-17 #b00100) (= valin-17-'NEXT` valout-4-'NEXT`)))'
`(assert (=> (= in-17 #b00101) (= valin-17-'NEXT` valout-5-'NEXT`)))'
;`(assert (=> (= in-17 #b00110) (= valin-17-'NEXT` valout-6-'NEXT`)))'
;`(assert (=> (= in-17 #b00111) (= valin-17-'NEXT` valout-7-'NEXT`)))'
;`(assert (=> (= in-17 #b01000) (= valin-17-'NEXT` valout-8-'NEXT`)))'
;`(assert (=> (= in-17 #b01001) (= valin-17-'NEXT` valout-9-'NEXT`)))'
;`(assert (=> (= in-17 #b01010) (= valin-17-'NEXT` valout-10-'NEXT`)))'
;`(assert (=> (= in-17 #b01011) (= valin-17-'NEXT` valout-11-'NEXT`)))'
;`(assert (=> (= in-17 #b01100) (= valin-17-'NEXT` valout-12-'NEXT`)))'
;`(assert (=> (= in-17 #b01101) (= valin-17-'NEXT` valout-13-'NEXT`)))'
;`(assert (=> (= in-17 #b01110) (= valin-17-'NEXT` valout-14-'NEXT`)))'
;`(assert (=> (= in-17 #b01111) (= valin-17-'NEXT` valout-15-'NEXT`)))'
;`(assert (=> (= in-17 #b10000) (= valin-17-'NEXT` valout-16-'NEXT`)))'
;`(assert (=> (= in-17 #b10001) (= valin-17-'NEXT` valout-17-'NEXT`)))'
;`(assert (=> (= in-17 #b10010) (= valin-17-'NEXT` valout-18-'NEXT`)))'
;`(assert (=> (= in-17 #b10011) (= valin-17-'NEXT` valout-19-'NEXT`)))'
`(assert (=> (= in-17 #b10100) (= valin-17-'NEXT` valout-20-'NEXT`)))'
`(assert (=> (= in-17 #b10101) (= valin-17-'NEXT` valout-21-'NEXT`)))'
`(assert (=> (= in-17 #b10110) (= valin-17-'NEXT` valout-22-'NEXT`)))'
`(assert (=> (= in-17 #b10111) (= valin-17-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-18 #b00001) (= valin-18-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-18 #b00010) (= valin-18-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-18 #b00011) (= valin-18-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-18 #b00100) (= valin-18-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-18 #b00101) (= valin-18-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-18 #b00110) (= valin-18-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-18 #b00111) (= valin-18-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-18 #b01000) (= valin-18-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-18 #b01001) (= valin-18-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-18 #b01010) (= valin-18-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-18 #b01011) (= valin-18-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-18 #b01100) (= valin-18-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-18 #b01101) (= valin-18-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-18 #b01110) (= valin-18-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-18 #b01111) (= valin-18-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-18 #b10000) (= valin-18-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-18 #b10001) (= valin-18-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-18 #b10010) (= valin-18-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-18 #b10011) (= valin-18-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-18 #b10100) (= valin-18-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-18 #b10101) (= valin-18-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-18 #b10110) (= valin-18-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-18 #b10111) (= valin-18-'NEXT` valout-23-'NEXT`)))'

;`(assert (=> (= in-19 #b00001) (= valin-19-'NEXT` valout-1-'NEXT`)))'
`(assert (=> (= in-19 #b00010) (= valin-19-'NEXT` valout-2-'NEXT`)))'
;`(assert (=> (= in-19 #b00011) (= valin-19-'NEXT` valout-3-'NEXT`)))'
`(assert (=> (= in-19 #b00100) (= valin-19-'NEXT` valout-4-'NEXT`)))'
;`(assert (=> (= in-19 #b00101) (= valin-19-'NEXT` valout-5-'NEXT`)))'
`(assert (=> (= in-19 #b00110) (= valin-19-'NEXT` valout-6-'NEXT`)))'
`(assert (=> (= in-19 #b00111) (= valin-19-'NEXT` valout-7-'NEXT`)))'
`(assert (=> (= in-19 #b01000) (= valin-19-'NEXT` valout-8-'NEXT`)))'
`(assert (=> (= in-19 #b01001) (= valin-19-'NEXT` valout-9-'NEXT`)))'
`(assert (=> (= in-19 #b01010) (= valin-19-'NEXT` valout-10-'NEXT`)))'
`(assert (=> (= in-19 #b01011) (= valin-19-'NEXT` valout-11-'NEXT`)))'
`(assert (=> (= in-19 #b01100) (= valin-19-'NEXT` valout-12-'NEXT`)))'
`(assert (=> (= in-19 #b01101) (= valin-19-'NEXT` valout-13-'NEXT`)))'
`(assert (=> (= in-19 #b01110) (= valin-19-'NEXT` valout-14-'NEXT`)))'
`(assert (=> (= in-19 #b01111) (= valin-19-'NEXT` valout-15-'NEXT`)))'
`(assert (=> (= in-19 #b10000) (= valin-19-'NEXT` valout-16-'NEXT`)))'
`(assert (=> (= in-19 #b10001) (= valin-19-'NEXT` valout-17-'NEXT`)))'
`(assert (=> (= in-19 #b10010) (= valin-19-'NEXT` valout-18-'NEXT`)))'
`(assert (=> (= in-19 #b10011) (= valin-19-'NEXT` valout-19-'NEXT`)))'
;`(assert (=> (= in-19 #b10100) (= valin-19-'NEXT` valout-20-'NEXT`)))'
;`(assert (=> (= in-19 #b10101) (= valin-19-'NEXT` valout-21-'NEXT`)))'
;`(assert (=> (= in-19 #b10110) (= valin-19-'NEXT` valout-22-'NEXT`)))'
;`(assert (=> (= in-19 #b10111) (= valin-19-'NEXT` valout-23-'NEXT`)))'
)

;----------------------------------------------------------------------------
; Generic structural restrictions
;----------------------------------------------------------------------------
;
; If one input of a module is connected, then all its inputs are. 
; Additionally one other input is connected to one of the modules
;outputs. 
; 
; Note that such an axiom is needed since we could otherwise just
;'synthesize' arbitrary values into functional units that produce the
; desired output (and they would be different for each output value
; rather than constant). 
; 
; Note that cvc (or smtlib) does something strange for more than 2
; input equalities (presumably some kind of associativity); thus the
; multiple equalities. 
;
; These axioms are huge. Do not be fooled by the simplicity here,
; which is masqueraded by a macro.
;

; out1 in2 in3
(assert (= (= in-2 #b00000)
           (and forloop(`I',1,NUMIN,(not (= in-I #b00001))))))
(assert (= (= in-2 #b00000) (= in-3 #b00000)))

; out2 out3 in-4 in-5 in-18
(assert (= (= in-4 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= in-I #b00010))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b00011)))))))
(assert (= (= in-4 #b00000) (= in-5 #b00000)))
(assert (= (= in-4 #b00000) (= in-18 #b00000)))

; out4 out5 in-6 in-7 in-19
(assert (= (= in-6 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= in-I #b00100))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b00101)))))))
(assert (= (= in-6 #b00000) (= in-7 #b00000)))
(assert (= (= in-6 #b00000) (= in-19 #b00000)))

; out8 in-8 in-9
(assert (= (= in-8 #b00000)
           (and forloop(`I',1,NUMIN,(not (= in-I #b01000))))))
(assert (= (= in-8 #b00000) (= in-9 #b00000)))

; out9 in-10 in-11
(assert (= (= in-10 #b00000)
           (and forloop(`I',1,NUMIN,(not (= in-I #b01001))))))
(assert (= (= in-10 #b00000) (= in-11 #b00000)))

; out10 in-12 in-13
(assert (= (= in-12 #b00000)
           (and forloop(`I',1,NUMIN,(not (= in-I #b01010))))))
(assert (= (= in-12 #b00000) (= in-13 #b00000)))

; out11 in-14 in-15
(assert (= (= in-14 #b00000)
           (and forloop(`I',1,NUMIN,(not (= in-I #b01011))))))
(assert (= (= in-14 #b00000) (= in-15 #b00000)))

; out12-15 in-16
(assert (= (= in-16 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= in-I #b01100))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b01101))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b01110))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b01111)))))))

; out16-19 in-17
(assert (= (= in-17 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= in-I #b10000))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b10001))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b10010))))
                (and forloop(`I',1,NUMIN,(not (= in-I #b10011)))))))

; Copy of above with in-->ina
ifdef(`DIST',dnl 
; out1 ina-2 ina-3
(assert (= (= ina-2 #b00000)
           (and forloop(`I',1,NUMIN,(not (= ina-I #b00001))))))
(assert (= (= ina-2 #b00000) (= ina-3 #b00000)))

; out2 out3 ina-4 ina-5 ina-18
(assert (= (= ina-4 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= ina-I #b00010))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b00011)))))))
(assert (= (= ina-4 #b00000) (= ina-5 #b00000)))
(assert (= (= ina-4 #b00000) (= ina-18 #b00000)))

; out4 out5 ina-6 ina-7 ina-19
(assert (= (= ina-6 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= ina-I #b00100))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b00101)))))))
(assert (= (= ina-6 #b00000) (= ina-7 #b00000)))
(assert (= (= ina-6 #b00000) (= ina-19 #b00000)))

; out8 ina-8 ina-9
(assert (= (= ina-8 #b00000)
           (and forloop(`I',1,NUMIN,(not (= ina-I #b01000))))))
(assert (= (= ina-8 #b00000) (= ina-9 #b00000)))

; out9 ina-10 ina-11
(assert (= (= ina-10 #b00000)
           (and forloop(`I',1,NUMIN,(not (= ina-I #b01001))))))
(assert (= (= ina-10 #b00000) (= ina-11 #b00000)))

; out10 ina-12 ina-13
(assert (= (= ina-12 #b00000)
           (and forloop(`I',1,NUMIN,(not (= ina-I #b01010))))))
(assert (= (= ina-12 #b00000) (= ina-13 #b00000)))

; out11 ina-14 ina-15
(assert (= (= ina-14 #b00000)
           (and forloop(`I',1,NUMIN,(not (= ina-I #b01011))))))
(assert (= (= ina-14 #b00000) (= ina-15 #b00000)))

; out12-15 ina-16
(assert (= (= ina-16 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= ina-I #b01100))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b01101))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b01110))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b01111)))))))

; out16-19 ina-17
(assert (= (= ina-17 #b00000)
           (and (and forloop(`I',1,NUMIN,(not (= ina-I #b10000))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b10001))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b10010))))
                (and forloop(`I',1,NUMIN,(not (= ina-I #b10011)))))))
)

;
; The system output must be connected. 
; 
(assert (not (= in-1 #b00000)))

ifdef(`DIST',
(assert (not (= ina-1 #b00000)))
)

;----------------------------------------------------------------------------
; Oracles
;----------------------------------------------------------------------------
;
; I/O Relation (from oracle) 
; Update on each iteration
;
(assert (and (= sysinxh-1 #b0100)(= sysinxl-1 #b0001)   ; 4,1 = 65
             (= sysinyh-1 #b0011)(= sysinyl-1 #b0110)   ; 3,6 = 54
             (= sysout-1 #b01110111)))                  ; 119 = 7,7

; ADDWFF
; WIDMER: Add one of these per iteration based on 2nd SAT output. 
; Note that sysout-2 still needs manual editing (in this case, its the
; sum [xh,xl]+[yh,yl] where [xh,xl] means the concatenation of the two.  
; I give an example below. 
;(assert (and (= sysinxh-2 #b0001)(= sysinxl-2 #b1110)   ; 1,14
;             (= sysinyh-2 #b1000)(= sysinyl-2 #b1001)   ; 8,9
;             (= sysout-2 #b10100111)))                  ; 10,7

;----------------------------------------------------------------------------
; Distinguishing input generation
;   Two circuits are different 
;   All I/O oracle pairs get same result on both circuits
;     (already known from above)
;   Distinguishing input gets different results on the two circuits 
;----------------------------------------------------------------------------
ifdef(`DIST',dnl
(assert (not (and (= in-1 ina-1) (= in-2 ina-2) (= in-3 ina-3)
                  (= in-4 ina-4) (= in-5 ina-5) (= in-6 ina-6)
                  (= in-7 ina-7) (= in-8 ina-8) (= in-9 ina-9)
                  (= in-10 ina-10) (= in-11 ina-11) (= in-12 ina-12)
                  (= in-13 ina-13) (= in-14 ina-14) (= in-15 ina-14)
                  (= in-16 ina-16) (= in-17 ina-17))))

(assert (not (= sysout-NEXT sysouta)))
)

;----------------------------------------------------------------------------
; The values printed depend on whether we are doing circuit synthesis
; or generating a distinguishing input. Additionally we essentially
; dump all variables in debug mode except for those not anticipated to  
; cause any bugs (eg values on internal nets) 
;----------------------------------------------------------------------------
(check-sat)
ifdef(`BOOLECTOR',,
(get-value (in-1 in-2 in-3 in-4 in-5 in-6 in-7 in-8 in-9 in-10
            in-11 in-12 in-13 in-14 in-15 in-16 in-17 in-18 in-19))
)
ifdef(`DIST',dnl
ifdef(`BOOLECTOR',,
(get-value (sysinxh-NEXT sysinxl-NEXT sysinyh-NEXT sysinyl-NEXT))
(get-value (sysout-NEXT sysouta))
(get-value (ina-1 ina-2 ina-3 ina-4 ina-5 ina-6 ina-7 ina-8 ina-9 ina-10
            ina-11 ina-12 ina-13 ina-14 ina-15 ina-16 ina-17 ina-18 ina-19))
))

ifdef(`DEBUG',dnl
; Some of these are in comments since they need to be edited for
; debugging purposes 
(get-value (valin-1-NEXT valin-2-NEXT valin-3-NEXT valin-4-NEXT 
            valin-5-NEXT valin-6-NEXT valin-7-NEXT valin-8-NEXT 
            valin-9-NEXT valin-10-NEXT valin-11-NEXT valin-12-NEXT 
            valin-13-NEXT valin-14-NEXT valin-15-NEXT valin-16-NEXT 
            valin-17-NEXT valin-18-NEXT valin-19-NEXT))
(get-value (valout-1-NEXT valout-2-NEXT valout-3-NEXT valout-4-NEXT 
            valout-5-NEXT valout-6-NEXT valout-7-NEXT valout-8-NEXT
            valout-9-NEXT valout-10-NEXT valout-11-NEXT valout-12-NEXT 
            valout-13-NEXT valout-14-NEXT valout-15-NEXT valout-16-NEXT 
            valout-17-NEXT valout-18-NEXT valout-19-NEXT valout-20-NEXT
            valout-21-NEXT valout-22-NEXT valout-23-NEXT))
(get-value (valina-1-1 valina-2-1 valina-3-1 valina-4-1 valina-5-1 
            valina-6-1 valina-7-1 valina-8-1 valina-9-1 valina-10-1
            valina-11-1 valina-12-1 valina-13-1 valina-14-1 valina-15-1 
            valina-16-1 valina-17-1))
)

;(get-unsat-core) 
(exit)
