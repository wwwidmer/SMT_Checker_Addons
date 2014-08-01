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



;;define(`DIST',`')   

;;define(`DEBUG',`')
;;define(`BOOLECTOR',`')





;----------------------------------------------------------------------------
; Useful macros for writing the code.
; Be careful - its easy to generate huge smtlib files.
;----------------------------------------------------------------------------










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
; (set-option :produce-unsat-cores true)

; Produce satisfying values for constants (boolector does this using
; flags) 
(set-option :produce-models true)

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
(declare-fun in-1 () (_ BitVec 5))
(assert (not (bvult #b10111 in-1)))
(declare-fun in-2 () (_ BitVec 5))
(assert (not (bvult #b10111 in-2)))
(declare-fun in-3 () (_ BitVec 5))
(assert (not (bvult #b10111 in-3)))
(declare-fun in-4 () (_ BitVec 5))
(assert (not (bvult #b10111 in-4)))
(declare-fun in-5 () (_ BitVec 5))
(assert (not (bvult #b10111 in-5)))
(declare-fun in-6 () (_ BitVec 5))
(assert (not (bvult #b10111 in-6)))
(declare-fun in-7 () (_ BitVec 5))
(assert (not (bvult #b10111 in-7)))
(declare-fun in-8 () (_ BitVec 5))
(assert (not (bvult #b10111 in-8)))
(declare-fun in-9 () (_ BitVec 5))
(assert (not (bvult #b10111 in-9)))
(declare-fun in-10 () (_ BitVec 5))
(assert (not (bvult #b10111 in-10)))
(declare-fun in-11 () (_ BitVec 5))
(assert (not (bvult #b10111 in-11)))
(declare-fun in-12 () (_ BitVec 5))
(assert (not (bvult #b10111 in-12)))
(declare-fun in-13 () (_ BitVec 5))
(assert (not (bvult #b10111 in-13)))
(declare-fun in-14 () (_ BitVec 5))
(assert (not (bvult #b10111 in-14)))
(declare-fun in-15 () (_ BitVec 5))
(assert (not (bvult #b10111 in-15)))
(declare-fun in-16 () (_ BitVec 5))
(assert (not (bvult #b10111 in-16)))
(declare-fun in-17 () (_ BitVec 5))
(assert (not (bvult #b10111 in-17)))
(declare-fun in-18 () (_ BitVec 5))
(assert (not (bvult #b10111 in-18)))
(declare-fun in-19 () (_ BitVec 5))
(assert (not (bvult #b10111 in-19)))


; Copy of above with in-->ina

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
; Distinguishing inputs are represented as the 2 iteration. 
;
(declare-fun valin-1-1 () (_ BitVec 8))
(declare-fun valin-2-1 () (_ BitVec 4))
(declare-fun valin-3-1 () (_ BitVec 4))
(declare-fun valin-4-1 () (_ BitVec 4))
(declare-fun valin-5-1 () (_ BitVec 4))
(declare-fun valin-6-1 () (_ BitVec 4))
(declare-fun valin-7-1 () (_ BitVec 4))
(declare-fun valin-8-1 () (_ BitVec 1))
(declare-fun valin-9-1 () (_ BitVec 1))
(declare-fun valin-10-1 () (_ BitVec 1))
(declare-fun valin-11-1 () (_ BitVec 1))
(declare-fun valin-12-1 () (_ BitVec 1))
(declare-fun valin-13-1 () (_ BitVec 1))
(declare-fun valin-14-1 () (_ BitVec 1))
(declare-fun valin-15-1 () (_ BitVec 1))
(declare-fun valin-16-1 () (_ BitVec 4))
(declare-fun valin-17-1 () (_ BitVec 4))
(declare-fun valin-18-1 () (_ BitVec 1))
(declare-fun valin-19-1 () (_ BitVec 1))


(declare-fun valout-1-1 () (_ BitVec 8))
(declare-fun valout-2-1 () (_ BitVec 1))
(declare-fun valout-3-1 () (_ BitVec 4))
(declare-fun valout-4-1 () (_ BitVec 1))
(declare-fun valout-5-1 () (_ BitVec 4))
(declare-fun valout-6-1 () (_ BitVec 1))
(declare-fun valout-7-1 () (_ BitVec 1))
(declare-fun valout-8-1 () (_ BitVec 1))
(declare-fun valout-9-1 () (_ BitVec 1))
(declare-fun valout-10-1 () (_ BitVec 1))
(declare-fun valout-11-1 () (_ BitVec 1))
(declare-fun valout-12-1 () (_ BitVec 1))
(declare-fun valout-13-1 () (_ BitVec 1))
(declare-fun valout-14-1 () (_ BitVec 1))
(declare-fun valout-15-1 () (_ BitVec 1))
(declare-fun valout-16-1 () (_ BitVec 1))
(declare-fun valout-17-1 () (_ BitVec 1))
(declare-fun valout-18-1 () (_ BitVec 1))
(declare-fun valout-19-1 () (_ BitVec 1))
(declare-fun valout-20-1 () (_ BitVec 4))
(declare-fun valout-21-1 () (_ BitVec 4))
(declare-fun valout-22-1 () (_ BitVec 4))
(declare-fun valout-23-1 () (_ BitVec 4))


(declare-fun sysinxl-1 () (_ BitVec 4))
(declare-fun sysinxh-1 () (_ BitVec 4))
(declare-fun sysinyl-1 () (_ BitVec 4))
(declare-fun sysinyh-1 () (_ BitVec 4))
(declare-fun sysout-1 () (_ BitVec 8))




;----------------------------------------------------------------------------
; Circuit invariants
;----------------------------------------------------------------------------
;
; Circuit ordering. Note this implicitly also says that there are no
; loops (since it imposes some total order properties on output nets). 
; 
(declare-fun loc2 () (_ BitVec 4))
(declare-fun loc3 () (_ BitVec 4))
(declare-fun loc5 () (_ BitVec 4))
(declare-fun loc6 () (_ BitVec 4))
(declare-fun loc7 () (_ BitVec 4))
(declare-fun loc8 () (_ BitVec 4))
(declare-fun loc9 () (_ BitVec 4))
(declare-fun loc10 () (_ BitVec 4))
(declare-fun loc11 () (_ BitVec 4))
(declare-fun loc12 () (_ BitVec 4))
(declare-fun loc16 () (_ BitVec 4))
(declare-fun loc20 () (_ BitVec 4))
(declare-fun loc21 () (_ BitVec 4))
(declare-fun loc22 () (_ BitVec 4))
(declare-fun loc23 () (_ BitVec 4))

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
(declare-fun allouts () (_ BitVec 23))

(assert (= (= ((_ extract 2 2) allouts) #b1)
           (or (= in-8 #b00010)  (= in-9 #b00010)  (= in-10 #b00010)
               (= in-11 #b00010) (= in-12 #b00010) (= in-13 #b00010)
               (= in-14 #b00010) (= in-15 #b00010))))
(assert (= (= ((_ extract 4 4) allouts) #b1)
           (or (= in-8 #b00100)  (= in-9 #b00100)  (= in-10 #b00100)
               (= in-11 #b00100) (= in-12 #b00100) (= in-13 #b00100)
               (= in-14 #b00100) (= in-15 #b00100))))
(assert (= (= ((_ extract 6 6) allouts) #b1)
           (or (= in-8 #b00110)  (= in-9 #b00110)  (= in-10 #b00110)
               (= in-11 #b00110) (= in-12 #b00110) (= in-13 #b00110)
               (= in-14 #b00110) (= in-15 #b00110))))
(assert (= (= ((_ extract 7 7) allouts) #b1)
           (or (= in-8 #b00111)  (= in-9 #b00111)  (= in-10 #b00111)
               (= in-11 #b00111) (= in-12 #b00111) (= in-13 #b00111)
               (= in-14 #b00111) (= in-15 #b00111))))
(assert (= (= ((_ extract 8 8) allouts) #b1)
           (or (= in-8 #b01000)  (= in-9 #b01000)  (= in-10 #b01000)
               (= in-11 #b01000) (= in-12 #b01000) (= in-13 #b01000)
               (= in-14 #b01000) (= in-15 #b01000))))
(assert (= (= ((_ extract 9 9) allouts) #b1)
           (or (= in-8 #b01001)  (= in-9 #b01001)  (= in-10 #b01001)
               (= in-11 #b01001) (= in-12 #b01001) (= in-13 #b01001)
               (= in-14 #b01001) (= in-15 #b01001))))
(assert (= (= ((_ extract 10 10) allouts) #b1)
           (or (= in-8 #b01010)  (= in-9 #b01010)  (= in-10 #b01010)
               (= in-11 #b01010) (= in-12 #b01010) (= in-13 #b01010)
               (= in-14 #b01010) (= in-15 #b01010))))
(assert (= (= ((_ extract 11 11) allouts) #b1)
           (or (= in-8 #b01011)  (= in-9 #b01011)  (= in-10 #b01011)
               (= in-11 #b01011) (= in-12 #b01011) (= in-13 #b01011)
               (= in-14 #b01011) (= in-15 #b01011))))
(assert (= (= ((_ extract 12 12) allouts) #b1)
           (or (= in-8 #b01100)  (= in-9 #b01100)  (= in-10 #b01100)
               (= in-11 #b01100) (= in-12 #b01100) (= in-13 #b01100)
               (= in-14 #b01100) (= in-15 #b01100))))
(assert (= (= ((_ extract 13 13) allouts) #b1)
           (or (= in-8 #b01101)  (= in-9 #b01101)  (= in-10 #b01101)
               (= in-11 #b01101) (= in-12 #b01101) (= in-13 #b01101)
               (= in-14 #b01101) (= in-15 #b01101))))
(assert (= (= ((_ extract 14 14) allouts) #b1)
           (or (= in-8 #b01110)  (= in-9 #b01110)  (= in-10 #b01110)
               (= in-11 #b01110) (= in-12 #b01110) (= in-13 #b01110)
               (= in-14 #b01110) (= in-15 #b01110))))
(assert (= (= ((_ extract 15 15) allouts) #b1)
           (or (= in-8 #b01111)  (= in-9 #b01111)  (= in-10 #b01111)
               (= in-11 #b01111) (= in-12 #b01111) (= in-13 #b01111)
               (= in-14 #b01111) (= in-15 #b01111))))
(assert (= (= ((_ extract 16 16) allouts) #b1)
           (or (= in-8 #b10000)  (= in-9 #b10000)  (= in-10 #b10000)
               (= in-11 #b10000) (= in-12 #b10000) (= in-13 #b10000)
               (= in-14 #b10000) (= in-15 #b10000))))
(assert (= (= ((_ extract 17 17) allouts) #b1)
           (or (= in-8 #b10001)  (= in-9 #b10001)  (= in-10 #b10001)
               (= in-11 #b10001) (= in-12 #b10001) (= in-13 #b10001)
               (= in-14 #b10001) (= in-15 #b10001))))
(assert (= (= ((_ extract 18 18) allouts) #b1)
           (or (= in-8 #b10010)  (= in-9 #b10010)  (= in-10 #b10010)
               (= in-11 #b10010) (= in-12 #b10010) (= in-13 #b10010)
               (= in-14 #b10010) (= in-15 #b10010))))
(assert (= (= ((_ extract 19 19) allouts) #b1)
           (or (= in-8 #b10011)  (= in-9 #b10011)  (= in-10 #b10011)
               (= in-11 #b10011) (= in-12 #b10011) (= in-13 #b10011)
               (= in-14 #b10011) (= in-15 #b10011))))

; The following macro says that if output net arg1 is connected to
; some nand gate input and loc(arg2) < loc(f) (f is a component), then 
; the output nets of f are also connected to some nand gate input.

(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 2 2) allouts) #b1) (bvult loc3 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 4 4) allouts) #b1) (bvult loc5 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 6 6) allouts) #b1) (bvult loc6 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 7 7) allouts) #b1) (bvult loc7 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 8 8) allouts) #b1) (bvult loc8 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 9 9) allouts) #b1) (bvult loc9 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 10 10) allouts) #b1) (bvult loc10 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 11 11) allouts) #b1) (bvult loc11 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 12 12) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 13 13) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 14 14) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 15 15) allouts) #b1) (bvult loc12 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 16 16) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 17 17) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 18 18) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 19 19) allouts) #b1)))

(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc3))
            (= ((_ extract 2 2) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc5))
            (= ((_ extract 4 4) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc6))
            (= ((_ extract 6 6) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc7))
            (= ((_ extract 7 7) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc8))
            (= ((_ extract 8 8) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc9))
            (= ((_ extract 9 9) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc10))
            (= ((_ extract 10 10) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc11))
            (= ((_ extract 11 11) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 12 12) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 13 13) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 14 14) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc12))
            (= ((_ extract 15 15) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 16 16) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 17 17) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 18 18) allouts) #b1)))
(assert (=> (and (= ((_ extract 19 19) allouts) #b1) (bvult loc16 loc16))
            (= ((_ extract 19 19) allouts) #b1)))


; Copy of above with allouts-->alloutsa loc-->loca in-->ina


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
; (assert (= valout-12 ((_ extract 0 0) valin-16)))
; (assert (= valout-13 ((_ extract 1 1) valin-16)))
; (assert (= valout-14 ((_ extract 2 2) valin-16)))
; (assert (= valout-15 ((_ extract 3 3) valin-16)))
; (assert (= valout-16 ((_ extract 0 0) valin-17)))
; (assert (= valout-17 ((_ extract 1 1) valin-17)))
; (assert (= valout-18 ((_ extract 2 2) valin-17)))
; (assert (= valout-19 ((_ extract 3 3) valin-17)))
; (assert (= valout-20 sysinxl))
; (assert (= valout-21 sysinxh))
; (assert (= valout-22 sysinyl))
; (assert (= valout-23 sysinyh))
;


(assert (= valin-1-1 sysout-1))
(assert (= valout-1-1 (concat valin-3-1 valin-2-1)))
(assert (= valout-2-1 (ite
  (bvult (bvadd (concat #b0 valin-4-1)(concat #b0 valin-5-1)
                (concat #b0000 valin-18-1))
         #b10000)
  #b0 #b1)))
(assert (= valout-3-1 (bvadd valin-4-1 valin-5-1
                                (concat #b000 valin-18-1))))
(assert (= valout-4-1 (ite
  (bvult (bvadd (concat #b0 valin-6-1)(concat #b0 valin-7-1)
                (concat #b0000 valin-19-1))
         #b10000)
  #b0 #b1)))
(assert (= valout-5-1 (bvadd valin-6-1 valin-7-1
                                (concat #b000 valin-19-1))))
(assert (= valout-6-1 #b0))
(assert (= valout-7-1 #b1))
(assert (= valout-8-1 (bvnot (bvand valin-8-1 valin-9-1))))
(assert (= valout-9-1 (bvnot (bvand valin-10-1 valin-11-1))))
(assert (= valout-10-1 (bvnot (bvand valin-12-1 valin-13-1))))
(assert (= valout-11-1 (bvnot (bvand valin-14-1 valin-15-1))))
(assert (= valout-12-1 ((_ extract 0 0) valin-16-1)))
(assert (= valout-13-1 ((_ extract 1 1) valin-16-1)))
(assert (= valout-14-1 ((_ extract 2 2) valin-16-1)))
(assert (= valout-15-1 ((_ extract 3 3) valin-16-1)))
(assert (= valout-16-1 ((_ extract 0 0) valin-17-1)))
(assert (= valout-17-1 ((_ extract 1 1) valin-17-1)))
(assert (= valout-18-1 ((_ extract 2 2) valin-17-1)))
(assert (= valout-19-1 ((_ extract 3 3) valin-17-1)))
(assert (= valout-20-1 sysinxl-1))
(assert (= valout-21-1 sysinxh-1))
(assert (= valout-22-1 sysinyl-1))
(assert (= valout-23-1 sysinyh-1))


; Copy of above with val-->vala (except the special case sysout) 


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
(assert (=> (= in-1 #b00001) (= valin-1-1 valout-1-1)))
;(assert (=> (= in-1 #b00010) (= valin-1-1 valout-2-1)))
;(assert (=> (= in-1 #b00011) (= valin-1-1 valout-3-1)))
;(assert (=> (= in-1 #b00100) (= valin-1-1 valout-4-1)))
;(assert (=> (= in-1 #b00101) (= valin-1-1 valout-5-1)))
;(assert (=> (= in-1 #b00110) (= valin-1-1 valout-6-1)))
;(assert (=> (= in-1 #b00111) (= valin-1-1 valout-7-1)))
;(assert (=> (= in-1 #b01000) (= valin-1-1 valout-8-1)))
;(assert (=> (= in-1 #b01001) (= valin-1-1 valout-9-1)))
;(assert (=> (= in-1 #b01010) (= valin-1-1 valout-10-1)))
;(assert (=> (= in-1 #b01011) (= valin-1-1 valout-11-1)))
;(assert (=> (= in-1 #b01100) (= valin-1-1 valout-12-1)))
;(assert (=> (= in-1 #b01101) (= valin-1-1 valout-13-1)))
;(assert (=> (= in-1 #b01110) (= valin-1-1 valout-14-1)))
;(assert (=> (= in-1 #b01111) (= valin-1-1 valout-15-1)))
;(assert (=> (= in-1 #b10000) (= valin-1-1 valout-16-1)))
;(assert (=> (= in-1 #b10001) (= valin-1-1 valout-17-1)))
;(assert (=> (= in-1 #b10010) (= valin-1-1 valout-18-1)))
;(assert (=> (= in-1 #b10011) (= valin-1-1 valout-19-1)))
;(assert (=> (= in-1 #b10100) (= valin-1-1 valout-20-1)))
;(assert (=> (= in-1 #b10101) (= valin-1-1 valout-21-1)))
;(assert (=> (= in-1 #b10110) (= valin-1-1 valout-22-1)))
;(assert (=> (= in-1 #b10111) (= valin-1-1 valout-23-1)))

;(assert (=> (= in-2 #b00001) (= valin-2-1 valout-1-1)))
;(assert (=> (= in-2 #b00010) (= valin-2-1 valout-2-1)))
(assert (=> (= in-2 #b00011) (= valin-2-1 valout-3-1)))
;(assert (=> (= in-2 #b00100) (= valin-2-1 valout-4-1)))
(assert (=> (= in-2 #b00101) (= valin-2-1 valout-5-1)))
;(assert (=> (= in-2 #b00110) (= valin-2-1 valout-6-1)))
;(assert (=> (= in-2 #b00111) (= valin-2-1 valout-7-1)))
;(assert (=> (= in-2 #b01000) (= valin-2-1 valout-8-1)))
;(assert (=> (= in-2 #b01001) (= valin-2-1 valout-9-1)))
;(assert (=> (= in-2 #b01010) (= valin-2-1 valout-10-1)))
;(assert (=> (= in-2 #b01011) (= valin-2-1 valout-11-1)))
;(assert (=> (= in-2 #b01100) (= valin-2-1 valout-12-1)))
;(assert (=> (= in-2 #b01101) (= valin-2-1 valout-13-1)))
;(assert (=> (= in-2 #b01110) (= valin-2-1 valout-14-1)))
;(assert (=> (= in-2 #b01111) (= valin-2-1 valout-15-1)))
;(assert (=> (= in-2 #b10000) (= valin-2-1 valout-16-1)))
;(assert (=> (= in-2 #b10001) (= valin-2-1 valout-17-1)))
;(assert (=> (= in-2 #b10010) (= valin-2-1 valout-18-1)))
;(assert (=> (= in-2 #b10011) (= valin-2-1 valout-19-1)))
(assert (=> (= in-2 #b10100) (= valin-2-1 valout-20-1)))
(assert (=> (= in-2 #b10101) (= valin-2-1 valout-21-1)))
(assert (=> (= in-2 #b10110) (= valin-2-1 valout-22-1)))
(assert (=> (= in-2 #b10111) (= valin-2-1 valout-23-1)))

;(assert (=> (= in-3 #b00001) (= valin-3-1 valout-1-1)))
;(assert (=> (= in-3 #b00010) (= valin-3-1 valout-2-1)))
(assert (=> (= in-3 #b00011) (= valin-3-1 valout-3-1)))
;(assert (=> (= in-3 #b00100) (= valin-3-1 valout-4-1)))
(assert (=> (= in-3 #b00101) (= valin-3-1 valout-5-1)))
;(assert (=> (= in-3 #b00110) (= valin-3-1 valout-6-1)))
;(assert (=> (= in-3 #b00111) (= valin-3-1 valout-7-1)))
;(assert (=> (= in-3 #b01000) (= valin-3-1 valout-8-1)))
;(assert (=> (= in-3 #b01001) (= valin-3-1 valout-9-1)))
;(assert (=> (= in-3 #b01010) (= valin-3-1 valout-10-1)))
;(assert (=> (= in-3 #b01011) (= valin-3-1 valout-11-1)))
;(assert (=> (= in-3 #b01100) (= valin-3-1 valout-12-1)))
;(assert (=> (= in-3 #b01101) (= valin-3-1 valout-13-1)))
;(assert (=> (= in-3 #b01110) (= valin-3-1 valout-14-1)))
;(assert (=> (= in-3 #b01111) (= valin-3-1 valout-15-1)))
;(assert (=> (= in-3 #b10000) (= valin-3-1 valout-16-1)))
;(assert (=> (= in-3 #b10001) (= valin-3-1 valout-17-1)))
;(assert (=> (= in-3 #b10010) (= valin-3-1 valout-18-1)))
;(assert (=> (= in-3 #b10011) (= valin-3-1 valout-19-1)))
(assert (=> (= in-3 #b10100) (= valin-3-1 valout-20-1)))
(assert (=> (= in-3 #b10101) (= valin-3-1 valout-21-1)))
(assert (=> (= in-3 #b10110) (= valin-3-1 valout-22-1)))
(assert (=> (= in-3 #b10111) (= valin-3-1 valout-23-1)))

;(assert (=> (= in-4 #b00001) (= valin-4-1 valout-1-1)))
;(assert (=> (= in-4 #b00010) (= valin-4-1 valout-2-1)))
(assert (=> (= in-4 #b00011) (= valin-4-1 valout-3-1)))
;(assert (=> (= in-4 #b00100) (= valin-4-1 valout-4-1)))
(assert (=> (= in-4 #b00101) (= valin-4-1 valout-5-1)))
;(assert (=> (= in-4 #b00110) (= valin-4-1 valout-6-1)))
;(assert (=> (= in-4 #b00111) (= valin-4-1 valout-7-1)))
;(assert (=> (= in-4 #b01000) (= valin-4-1 valout-8-1)))
;(assert (=> (= in-4 #b01001) (= valin-4-1 valout-9-1)))
;(assert (=> (= in-4 #b01010) (= valin-4-1 valout-10-1)))
;(assert (=> (= in-4 #b01011) (= valin-4-1 valout-11-1)))
;(assert (=> (= in-4 #b01100) (= valin-4-1 valout-12-1)))
;(assert (=> (= in-4 #b01101) (= valin-4-1 valout-13-1)))
;(assert (=> (= in-4 #b01110) (= valin-4-1 valout-14-1)))
;(assert (=> (= in-4 #b01111) (= valin-4-1 valout-15-1)))
;(assert (=> (= in-4 #b10000) (= valin-4-1 valout-16-1)))
;(assert (=> (= in-4 #b10001) (= valin-4-1 valout-17-1)))
;(assert (=> (= in-4 #b10010) (= valin-4-1 valout-18-1)))
;(assert (=> (= in-4 #b10011) (= valin-4-1 valout-19-1)))
(assert (=> (= in-4 #b10100) (= valin-4-1 valout-20-1)))
(assert (=> (= in-4 #b10101) (= valin-4-1 valout-21-1)))
(assert (=> (= in-4 #b10110) (= valin-4-1 valout-22-1)))
(assert (=> (= in-4 #b10111) (= valin-4-1 valout-23-1)))

;(assert (=> (= in-5 #b00001) (= valin-5-1 valout-1-1)))
;(assert (=> (= in-5 #b00010) (= valin-5-1 valout-2-1)))
(assert (=> (= in-5 #b00011) (= valin-5-1 valout-3-1)))
;(assert (=> (= in-5 #b00100) (= valin-5-1 valout-4-1)))
(assert (=> (= in-5 #b00101) (= valin-5-1 valout-5-1)))
;(assert (=> (= in-5 #b00110) (= valin-5-1 valout-6-1)))
;(assert (=> (= in-5 #b00111) (= valin-5-1 valout-7-1)))
;(assert (=> (= in-5 #b01000) (= valin-5-1 valout-8-1)))
;(assert (=> (= in-5 #b01001) (= valin-5-1 valout-9-1)))
;(assert (=> (= in-5 #b01010) (= valin-5-1 valout-10-1)))
;(assert (=> (= in-5 #b01011) (= valin-5-1 valout-11-1)))
;(assert (=> (= in-5 #b01100) (= valin-5-1 valout-12-1)))
;(assert (=> (= in-5 #b01101) (= valin-5-1 valout-13-1)))
;(assert (=> (= in-5 #b01110) (= valin-5-1 valout-14-1)))
;(assert (=> (= in-5 #b01111) (= valin-5-1 valout-15-1)))
;(assert (=> (= in-5 #b10000) (= valin-5-1 valout-16-1)))
;(assert (=> (= in-5 #b10001) (= valin-5-1 valout-17-1)))
;(assert (=> (= in-5 #b10010) (= valin-5-1 valout-18-1)))
;(assert (=> (= in-5 #b10011) (= valin-5-1 valout-19-1)))
(assert (=> (= in-5 #b10100) (= valin-5-1 valout-20-1)))
(assert (=> (= in-5 #b10101) (= valin-5-1 valout-21-1)))
(assert (=> (= in-5 #b10110) (= valin-5-1 valout-22-1)))
(assert (=> (= in-5 #b10111) (= valin-5-1 valout-23-1)))

;(assert (=> (= in-6 #b00001) (= valin-6-1 valout-1-1)))
;(assert (=> (= in-6 #b00010) (= valin-6-1 valout-2-1)))
(assert (=> (= in-6 #b00011) (= valin-6-1 valout-3-1)))
;(assert (=> (= in-6 #b00100) (= valin-6-1 valout-4-1)))
(assert (=> (= in-6 #b00101) (= valin-6-1 valout-5-1)))
;(assert (=> (= in-6 #b00110) (= valin-6-1 valout-6-1)))
;(assert (=> (= in-6 #b00111) (= valin-6-1 valout-7-1)))
;(assert (=> (= in-6 #b01000) (= valin-6-1 valout-8-1)))
;(assert (=> (= in-6 #b01001) (= valin-6-1 valout-9-1)))
;(assert (=> (= in-6 #b01010) (= valin-6-1 valout-10-1)))
;(assert (=> (= in-6 #b01011) (= valin-6-1 valout-11-1)))
;(assert (=> (= in-6 #b01100) (= valin-6-1 valout-12-1)))
;(assert (=> (= in-6 #b01101) (= valin-6-1 valout-13-1)))
;(assert (=> (= in-6 #b01110) (= valin-6-1 valout-14-1)))
;(assert (=> (= in-6 #b01111) (= valin-6-1 valout-15-1)))
;(assert (=> (= in-6 #b10000) (= valin-6-1 valout-16-1)))
;(assert (=> (= in-6 #b10001) (= valin-6-1 valout-17-1)))
;(assert (=> (= in-6 #b10010) (= valin-6-1 valout-18-1)))
;(assert (=> (= in-6 #b10011) (= valin-6-1 valout-19-1)))
(assert (=> (= in-6 #b10100) (= valin-6-1 valout-20-1)))
(assert (=> (= in-6 #b10101) (= valin-6-1 valout-21-1)))
(assert (=> (= in-6 #b10110) (= valin-6-1 valout-22-1)))
(assert (=> (= in-6 #b10111) (= valin-6-1 valout-23-1)))

;(assert (=> (= in-7 #b00001) (= valin-7-1 valout-1-1)))
;(assert (=> (= in-7 #b00010) (= valin-7-1 valout-2-1)))
(assert (=> (= in-7 #b00011) (= valin-7-1 valout-3-1)))
;(assert (=> (= in-7 #b00100) (= valin-7-1 valout-4-1)))
(assert (=> (= in-7 #b00101) (= valin-7-1 valout-5-1)))
;(assert (=> (= in-7 #b00110) (= valin-7-1 valout-6-1)))
;(assert (=> (= in-7 #b00111) (= valin-7-1 valout-7-1)))
;(assert (=> (= in-7 #b01000) (= valin-7-1 valout-8-1)))
;(assert (=> (= in-7 #b01001) (= valin-7-1 valout-9-1)))
;(assert (=> (= in-7 #b01010) (= valin-7-1 valout-10-1)))
;(assert (=> (= in-7 #b01011) (= valin-7-1 valout-11-1)))
;(assert (=> (= in-7 #b01100) (= valin-7-1 valout-12-1)))
;(assert (=> (= in-7 #b01101) (= valin-7-1 valout-13-1)))
;(assert (=> (= in-7 #b01110) (= valin-7-1 valout-14-1)))
;(assert (=> (= in-7 #b01111) (= valin-7-1 valout-15-1)))
;(assert (=> (= in-7 #b10000) (= valin-7-1 valout-16-1)))
;(assert (=> (= in-7 #b10001) (= valin-7-1 valout-17-1)))
;(assert (=> (= in-7 #b10010) (= valin-7-1 valout-18-1)))
;(assert (=> (= in-7 #b10011) (= valin-7-1 valout-19-1)))
(assert (=> (= in-7 #b10100) (= valin-7-1 valout-20-1)))
(assert (=> (= in-7 #b10101) (= valin-7-1 valout-21-1)))
(assert (=> (= in-7 #b10110) (= valin-7-1 valout-22-1)))
(assert (=> (= in-7 #b10111) (= valin-7-1 valout-23-1)))

;(assert (=> (= in-8 #b00001) (= valin-8-1 valout-1-1)))
(assert (=> (= in-8 #b00010) (= valin-8-1 valout-2-1)))
;(assert (=> (= in-8 #b00011) (= valin-8-1 valout-3-1)))
(assert (=> (= in-8 #b00100) (= valin-8-1 valout-4-1)))
;(assert (=> (= in-8 #b00101) (= valin-8-1 valout-5-1)))
(assert (=> (= in-8 #b00110) (= valin-8-1 valout-6-1)))
(assert (=> (= in-8 #b00111) (= valin-8-1 valout-7-1)))
(assert (=> (= in-8 #b01000) (= valin-8-1 valout-8-1)))
(assert (=> (= in-8 #b01001) (= valin-8-1 valout-9-1)))
(assert (=> (= in-8 #b01010) (= valin-8-1 valout-10-1)))
(assert (=> (= in-8 #b01011) (= valin-8-1 valout-11-1)))
(assert (=> (= in-8 #b01100) (= valin-8-1 valout-12-1)))
(assert (=> (= in-8 #b01101) (= valin-8-1 valout-13-1)))
(assert (=> (= in-8 #b01110) (= valin-8-1 valout-14-1)))
(assert (=> (= in-8 #b01111) (= valin-8-1 valout-15-1)))
(assert (=> (= in-8 #b10000) (= valin-8-1 valout-16-1)))
(assert (=> (= in-8 #b10001) (= valin-8-1 valout-17-1)))
(assert (=> (= in-8 #b10010) (= valin-8-1 valout-18-1)))
(assert (=> (= in-8 #b10011) (= valin-8-1 valout-19-1)))
;(assert (=> (= in-8 #b10100) (= valin-8-1 valout-20-1)))
;(assert (=> (= in-8 #b10101) (= valin-8-1 valout-21-1)))
;(assert (=> (= in-8 #b10110) (= valin-8-1 valout-22-1)))
;(assert (=> (= in-8 #b10111) (= valin-8-1 valout-23-1)))

;(assert (=> (= in-9 #b00001) (= valin-9-1 valout-1-1)))
(assert (=> (= in-9 #b00010) (= valin-9-1 valout-2-1)))
;(assert (=> (= in-9 #b00011) (= valin-9-1 valout-3-1)))
(assert (=> (= in-9 #b00100) (= valin-9-1 valout-4-1)))
;(assert (=> (= in-9 #b00101) (= valin-9-1 valout-5-1)))
(assert (=> (= in-9 #b00110) (= valin-9-1 valout-6-1)))
(assert (=> (= in-9 #b00111) (= valin-9-1 valout-7-1)))
(assert (=> (= in-9 #b01000) (= valin-9-1 valout-8-1)))
(assert (=> (= in-9 #b01001) (= valin-9-1 valout-9-1)))
(assert (=> (= in-9 #b01010) (= valin-9-1 valout-10-1)))
(assert (=> (= in-9 #b01011) (= valin-9-1 valout-11-1)))
(assert (=> (= in-9 #b01100) (= valin-9-1 valout-12-1)))
(assert (=> (= in-9 #b01101) (= valin-9-1 valout-13-1)))
(assert (=> (= in-9 #b01110) (= valin-9-1 valout-14-1)))
(assert (=> (= in-9 #b01111) (= valin-9-1 valout-15-1)))
(assert (=> (= in-9 #b10000) (= valin-9-1 valout-16-1)))
(assert (=> (= in-9 #b10001) (= valin-9-1 valout-17-1)))
(assert (=> (= in-9 #b10010) (= valin-9-1 valout-18-1)))
(assert (=> (= in-9 #b10011) (= valin-9-1 valout-19-1)))
;(assert (=> (= in-9 #b10100) (= valin-9-1 valout-20-1)))
;(assert (=> (= in-9 #b10101) (= valin-9-1 valout-21-1)))
;(assert (=> (= in-9 #b10110) (= valin-9-1 valout-22-1)))
;(assert (=> (= in-9 #b10111) (= valin-9-1 valout-23-1)))

;(assert (=> (= in-10 #b00001) (= valin-10-1 valout-1-1)))
(assert (=> (= in-10 #b00010) (= valin-10-1 valout-2-1)))
;(assert (=> (= in-10 #b00011) (= valin-10-1 valout-3-1)))
(assert (=> (= in-10 #b00100) (= valin-10-1 valout-4-1)))
;(assert (=> (= in-10 #b00101) (= valin-10-1 valout-5-1)))
(assert (=> (= in-10 #b00110) (= valin-10-1 valout-6-1)))
(assert (=> (= in-10 #b00111) (= valin-10-1 valout-7-1)))
(assert (=> (= in-10 #b01000) (= valin-10-1 valout-8-1)))
(assert (=> (= in-10 #b01001) (= valin-10-1 valout-9-1)))
(assert (=> (= in-10 #b01010) (= valin-10-1 valout-10-1)))
(assert (=> (= in-10 #b01011) (= valin-10-1 valout-11-1)))
(assert (=> (= in-10 #b01100) (= valin-10-1 valout-12-1)))
(assert (=> (= in-10 #b01101) (= valin-10-1 valout-13-1)))
(assert (=> (= in-10 #b01110) (= valin-10-1 valout-14-1)))
(assert (=> (= in-10 #b01111) (= valin-10-1 valout-15-1)))
(assert (=> (= in-10 #b10000) (= valin-10-1 valout-16-1)))
(assert (=> (= in-10 #b10001) (= valin-10-1 valout-17-1)))
(assert (=> (= in-10 #b10010) (= valin-10-1 valout-18-1)))
(assert (=> (= in-10 #b10011) (= valin-10-1 valout-19-1)))
;(assert (=> (= in-10 #b10100) (= valin-10-1 valout-20-1)))
;(assert (=> (= in-10 #b10101) (= valin-10-1 valout-21-1)))
;(assert (=> (= in-10 #b10110) (= valin-10-1 valout-22-1)))
;(assert (=> (= in-10 #b10111) (= valin-10-1 valout-23-1)))

;(assert (=> (= in-11 #b00001) (= valin-11-1 valout-1-1)))
(assert (=> (= in-11 #b00010) (= valin-11-1 valout-2-1)))
;(assert (=> (= in-11 #b00011) (= valin-11-1 valout-3-1)))
(assert (=> (= in-11 #b00100) (= valin-11-1 valout-4-1)))
;(assert (=> (= in-11 #b00101) (= valin-11-1 valout-5-1)))
(assert (=> (= in-11 #b00110) (= valin-11-1 valout-6-1)))
(assert (=> (= in-11 #b00111) (= valin-11-1 valout-7-1)))
(assert (=> (= in-11 #b01000) (= valin-11-1 valout-8-1)))
(assert (=> (= in-11 #b01001) (= valin-11-1 valout-9-1)))
(assert (=> (= in-11 #b01010) (= valin-11-1 valout-10-1)))
(assert (=> (= in-11 #b01011) (= valin-11-1 valout-11-1)))
(assert (=> (= in-11 #b01100) (= valin-11-1 valout-12-1)))
(assert (=> (= in-11 #b01101) (= valin-11-1 valout-13-1)))
(assert (=> (= in-11 #b01110) (= valin-11-1 valout-14-1)))
(assert (=> (= in-11 #b01111) (= valin-11-1 valout-15-1)))
(assert (=> (= in-11 #b10000) (= valin-11-1 valout-16-1)))
(assert (=> (= in-11 #b10001) (= valin-11-1 valout-17-1)))
(assert (=> (= in-11 #b10010) (= valin-11-1 valout-18-1)))
(assert (=> (= in-11 #b10011) (= valin-11-1 valout-19-1)))
;(assert (=> (= in-11 #b10100) (= valin-11-1 valout-20-1)))
;(assert (=> (= in-11 #b10101) (= valin-11-1 valout-21-1)))
;(assert (=> (= in-11 #b10110) (= valin-11-1 valout-22-1)))
;(assert (=> (= in-11 #b10111) (= valin-11-1 valout-23-1)))

;(assert (=> (= in-12 #b00001) (= valin-12-1 valout-1-1)))
(assert (=> (= in-12 #b00010) (= valin-12-1 valout-2-1)))
;(assert (=> (= in-12 #b00011) (= valin-12-1 valout-3-1)))
(assert (=> (= in-12 #b00100) (= valin-12-1 valout-4-1)))
;(assert (=> (= in-12 #b00101) (= valin-12-1 valout-5-1)))
(assert (=> (= in-12 #b00110) (= valin-12-1 valout-6-1)))
(assert (=> (= in-12 #b00111) (= valin-12-1 valout-7-1)))
(assert (=> (= in-12 #b01000) (= valin-12-1 valout-8-1)))
(assert (=> (= in-12 #b01001) (= valin-12-1 valout-9-1)))
(assert (=> (= in-12 #b01010) (= valin-12-1 valout-10-1)))
(assert (=> (= in-12 #b01011) (= valin-12-1 valout-11-1)))
(assert (=> (= in-12 #b01100) (= valin-12-1 valout-12-1)))
(assert (=> (= in-12 #b01101) (= valin-12-1 valout-13-1)))
(assert (=> (= in-12 #b01110) (= valin-12-1 valout-14-1)))
(assert (=> (= in-12 #b01111) (= valin-12-1 valout-15-1)))
(assert (=> (= in-12 #b10000) (= valin-12-1 valout-16-1)))
(assert (=> (= in-12 #b10001) (= valin-12-1 valout-17-1)))
(assert (=> (= in-12 #b10010) (= valin-12-1 valout-18-1)))
(assert (=> (= in-12 #b10011) (= valin-12-1 valout-19-1)))
;(assert (=> (= in-12 #b10100) (= valin-12-1 valout-20-1)))
;(assert (=> (= in-12 #b10101) (= valin-12-1 valout-21-1)))
;(assert (=> (= in-12 #b10110) (= valin-12-1 valout-22-1)))
;(assert (=> (= in-12 #b10111) (= valin-12-1 valout-23-1)))

;(assert (=> (= in-13 #b00001) (= valin-13-1 valout-1-1)))
(assert (=> (= in-13 #b00010) (= valin-13-1 valout-2-1)))
;(assert (=> (= in-13 #b00011) (= valin-13-1 valout-3-1)))
(assert (=> (= in-13 #b00100) (= valin-13-1 valout-4-1)))
;(assert (=> (= in-13 #b00101) (= valin-13-1 valout-5-1)))
(assert (=> (= in-13 #b00110) (= valin-13-1 valout-6-1)))
(assert (=> (= in-13 #b00111) (= valin-13-1 valout-7-1)))
(assert (=> (= in-13 #b01000) (= valin-13-1 valout-8-1)))
(assert (=> (= in-13 #b01001) (= valin-13-1 valout-9-1)))
(assert (=> (= in-13 #b01010) (= valin-13-1 valout-10-1)))
(assert (=> (= in-13 #b01011) (= valin-13-1 valout-11-1)))
(assert (=> (= in-13 #b01100) (= valin-13-1 valout-12-1)))
(assert (=> (= in-13 #b01101) (= valin-13-1 valout-13-1)))
(assert (=> (= in-13 #b01110) (= valin-13-1 valout-14-1)))
(assert (=> (= in-13 #b01111) (= valin-13-1 valout-15-1)))
(assert (=> (= in-13 #b10000) (= valin-13-1 valout-16-1)))
(assert (=> (= in-13 #b10001) (= valin-13-1 valout-17-1)))
(assert (=> (= in-13 #b10010) (= valin-13-1 valout-18-1)))
(assert (=> (= in-13 #b10011) (= valin-13-1 valout-19-1)))
;(assert (=> (= in-13 #b10100) (= valin-13-1 valout-20-1)))
;(assert (=> (= in-13 #b10101) (= valin-13-1 valout-21-1)))
;(assert (=> (= in-13 #b10110) (= valin-13-1 valout-22-1)))
;(assert (=> (= in-13 #b10111) (= valin-13-1 valout-23-1)))

;(assert (=> (= in-14 #b00001) (= valin-14-1 valout-1-1)))
(assert (=> (= in-14 #b00010) (= valin-14-1 valout-2-1)))
;(assert (=> (= in-14 #b00011) (= valin-14-1 valout-3-1)))
(assert (=> (= in-14 #b00100) (= valin-14-1 valout-4-1)))
;(assert (=> (= in-14 #b00101) (= valin-14-1 valout-5-1)))
(assert (=> (= in-14 #b00110) (= valin-14-1 valout-6-1)))
(assert (=> (= in-14 #b00111) (= valin-14-1 valout-7-1)))
(assert (=> (= in-14 #b01000) (= valin-14-1 valout-8-1)))
(assert (=> (= in-14 #b01001) (= valin-14-1 valout-9-1)))
(assert (=> (= in-14 #b01010) (= valin-14-1 valout-10-1)))
(assert (=> (= in-14 #b01011) (= valin-14-1 valout-11-1)))
(assert (=> (= in-14 #b01100) (= valin-14-1 valout-12-1)))
(assert (=> (= in-14 #b01101) (= valin-14-1 valout-13-1)))
(assert (=> (= in-14 #b01110) (= valin-14-1 valout-14-1)))
(assert (=> (= in-14 #b01111) (= valin-14-1 valout-15-1)))
(assert (=> (= in-14 #b10000) (= valin-14-1 valout-16-1)))
(assert (=> (= in-14 #b10001) (= valin-14-1 valout-17-1)))
(assert (=> (= in-14 #b10010) (= valin-14-1 valout-18-1)))
(assert (=> (= in-14 #b10011) (= valin-14-1 valout-19-1)))
;(assert (=> (= in-14 #b10100) (= valin-14-1 valout-20-1)))
;(assert (=> (= in-14 #b10101) (= valin-14-1 valout-21-1)))
;(assert (=> (= in-14 #b10110) (= valin-14-1 valout-22-1)))
;(assert (=> (= in-14 #b10111) (= valin-14-1 valout-23-1)))

;(assert (=> (= in-15 #b00001) (= valin-15-1 valout-1-1)))
(assert (=> (= in-15 #b00010) (= valin-15-1 valout-2-1)))
;(assert (=> (= in-15 #b00011) (= valin-15-1 valout-3-1)))
(assert (=> (= in-15 #b00100) (= valin-15-1 valout-4-1)))
;(assert (=> (= in-15 #b00101) (= valin-15-1 valout-5-1)))
(assert (=> (= in-15 #b00110) (= valin-15-1 valout-6-1)))
(assert (=> (= in-15 #b00111) (= valin-15-1 valout-7-1)))
(assert (=> (= in-15 #b01000) (= valin-15-1 valout-8-1)))
(assert (=> (= in-15 #b01001) (= valin-15-1 valout-9-1)))
(assert (=> (= in-15 #b01010) (= valin-15-1 valout-10-1)))
(assert (=> (= in-15 #b01011) (= valin-15-1 valout-11-1)))
(assert (=> (= in-15 #b01100) (= valin-15-1 valout-12-1)))
(assert (=> (= in-15 #b01101) (= valin-15-1 valout-13-1)))
(assert (=> (= in-15 #b01110) (= valin-15-1 valout-14-1)))
(assert (=> (= in-15 #b01111) (= valin-15-1 valout-15-1)))
(assert (=> (= in-15 #b10000) (= valin-15-1 valout-16-1)))
(assert (=> (= in-15 #b10001) (= valin-15-1 valout-17-1)))
(assert (=> (= in-15 #b10010) (= valin-15-1 valout-18-1)))
(assert (=> (= in-15 #b10011) (= valin-15-1 valout-19-1)))
;(assert (=> (= in-15 #b10100) (= valin-15-1 valout-20-1)))
;(assert (=> (= in-15 #b10101) (= valin-15-1 valout-21-1)))
;(assert (=> (= in-15 #b10110) (= valin-15-1 valout-22-1)))
;(assert (=> (= in-15 #b10111) (= valin-15-1 valout-23-1)))

;(assert (=> (= in-16 #b00001) (= valin-16-1 valout-1-1)))
;(assert (=> (= in-16 #b00010) (= valin-16-1 valout-2-1)))
(assert (=> (= in-16 #b00011) (= valin-16-1 valout-3-1)))
;(assert (=> (= in-16 #b00100) (= valin-16-1 valout-4-1)))
(assert (=> (= in-16 #b00101) (= valin-16-1 valout-5-1)))
;(assert (=> (= in-16 #b00110) (= valin-16-1 valout-6-1)))
;(assert (=> (= in-16 #b00111) (= valin-16-1 valout-7-1)))
;(assert (=> (= in-16 #b01000) (= valin-16-1 valout-8-1)))
;(assert (=> (= in-16 #b01001) (= valin-16-1 valout-9-1)))
;(assert (=> (= in-16 #b01010) (= valin-16-1 valout-10-1)))
;(assert (=> (= in-16 #b01011) (= valin-16-1 valout-11-1)))
;(assert (=> (= in-16 #b01100) (= valin-16-1 valout-12-1)))
;(assert (=> (= in-16 #b01101) (= valin-16-1 valout-13-1)))
;(assert (=> (= in-16 #b01110) (= valin-16-1 valout-14-1)))
;(assert (=> (= in-16 #b01111) (= valin-16-1 valout-15-1)))
;(assert (=> (= in-16 #b10000) (= valin-16-1 valout-16-1)))
;(assert (=> (= in-16 #b10001) (= valin-16-1 valout-17-1)))
;(assert (=> (= in-16 #b10010) (= valin-16-1 valout-18-1)))
;(assert (=> (= in-16 #b10011) (= valin-16-1 valout-19-1)))
(assert (=> (= in-16 #b10100) (= valin-16-1 valout-20-1)))
(assert (=> (= in-16 #b10101) (= valin-16-1 valout-21-1)))
(assert (=> (= in-16 #b10110) (= valin-16-1 valout-22-1)))
(assert (=> (= in-16 #b10111) (= valin-16-1 valout-23-1)))

;(assert (=> (= in-17 #b00001) (= valin-17-1 valout-1-1)))
;(assert (=> (= in-17 #b00010) (= valin-17-1 valout-2-1)))
(assert (=> (= in-17 #b00011) (= valin-17-1 valout-3-1)))
;(assert (=> (= in-17 #b00100) (= valin-17-1 valout-4-1)))
(assert (=> (= in-17 #b00101) (= valin-17-1 valout-5-1)))
;(assert (=> (= in-17 #b00110) (= valin-17-1 valout-6-1)))
;(assert (=> (= in-17 #b00111) (= valin-17-1 valout-7-1)))
;(assert (=> (= in-17 #b01000) (= valin-17-1 valout-8-1)))
;(assert (=> (= in-17 #b01001) (= valin-17-1 valout-9-1)))
;(assert (=> (= in-17 #b01010) (= valin-17-1 valout-10-1)))
;(assert (=> (= in-17 #b01011) (= valin-17-1 valout-11-1)))
;(assert (=> (= in-17 #b01100) (= valin-17-1 valout-12-1)))
;(assert (=> (= in-17 #b01101) (= valin-17-1 valout-13-1)))
;(assert (=> (= in-17 #b01110) (= valin-17-1 valout-14-1)))
;(assert (=> (= in-17 #b01111) (= valin-17-1 valout-15-1)))
;(assert (=> (= in-17 #b10000) (= valin-17-1 valout-16-1)))
;(assert (=> (= in-17 #b10001) (= valin-17-1 valout-17-1)))
;(assert (=> (= in-17 #b10010) (= valin-17-1 valout-18-1)))
;(assert (=> (= in-17 #b10011) (= valin-17-1 valout-19-1)))
(assert (=> (= in-17 #b10100) (= valin-17-1 valout-20-1)))
(assert (=> (= in-17 #b10101) (= valin-17-1 valout-21-1)))
(assert (=> (= in-17 #b10110) (= valin-17-1 valout-22-1)))
(assert (=> (= in-17 #b10111) (= valin-17-1 valout-23-1)))

;(assert (=> (= in-18 #b00001) (= valin-18-1 valout-1-1)))
(assert (=> (= in-18 #b00010) (= valin-18-1 valout-2-1)))
;(assert (=> (= in-18 #b00011) (= valin-18-1 valout-3-1)))
(assert (=> (= in-18 #b00100) (= valin-18-1 valout-4-1)))
;(assert (=> (= in-18 #b00101) (= valin-18-1 valout-5-1)))
(assert (=> (= in-18 #b00110) (= valin-18-1 valout-6-1)))
(assert (=> (= in-18 #b00111) (= valin-18-1 valout-7-1)))
(assert (=> (= in-18 #b01000) (= valin-18-1 valout-8-1)))
(assert (=> (= in-18 #b01001) (= valin-18-1 valout-9-1)))
(assert (=> (= in-18 #b01010) (= valin-18-1 valout-10-1)))
(assert (=> (= in-18 #b01011) (= valin-18-1 valout-11-1)))
(assert (=> (= in-18 #b01100) (= valin-18-1 valout-12-1)))
(assert (=> (= in-18 #b01101) (= valin-18-1 valout-13-1)))
(assert (=> (= in-18 #b01110) (= valin-18-1 valout-14-1)))
(assert (=> (= in-18 #b01111) (= valin-18-1 valout-15-1)))
(assert (=> (= in-18 #b10000) (= valin-18-1 valout-16-1)))
(assert (=> (= in-18 #b10001) (= valin-18-1 valout-17-1)))
(assert (=> (= in-18 #b10010) (= valin-18-1 valout-18-1)))
(assert (=> (= in-18 #b10011) (= valin-18-1 valout-19-1)))
;(assert (=> (= in-18 #b10100) (= valin-18-1 valout-20-1)))
;(assert (=> (= in-18 #b10101) (= valin-18-1 valout-21-1)))
;(assert (=> (= in-18 #b10110) (= valin-18-1 valout-22-1)))
;(assert (=> (= in-18 #b10111) (= valin-18-1 valout-23-1)))

;(assert (=> (= in-19 #b00001) (= valin-19-1 valout-1-1)))
(assert (=> (= in-19 #b00010) (= valin-19-1 valout-2-1)))
;(assert (=> (= in-19 #b00011) (= valin-19-1 valout-3-1)))
(assert (=> (= in-19 #b00100) (= valin-19-1 valout-4-1)))
;(assert (=> (= in-19 #b00101) (= valin-19-1 valout-5-1)))
(assert (=> (= in-19 #b00110) (= valin-19-1 valout-6-1)))
(assert (=> (= in-19 #b00111) (= valin-19-1 valout-7-1)))
(assert (=> (= in-19 #b01000) (= valin-19-1 valout-8-1)))
(assert (=> (= in-19 #b01001) (= valin-19-1 valout-9-1)))
(assert (=> (= in-19 #b01010) (= valin-19-1 valout-10-1)))
(assert (=> (= in-19 #b01011) (= valin-19-1 valout-11-1)))
(assert (=> (= in-19 #b01100) (= valin-19-1 valout-12-1)))
(assert (=> (= in-19 #b01101) (= valin-19-1 valout-13-1)))
(assert (=> (= in-19 #b01110) (= valin-19-1 valout-14-1)))
(assert (=> (= in-19 #b01111) (= valin-19-1 valout-15-1)))
(assert (=> (= in-19 #b10000) (= valin-19-1 valout-16-1)))
(assert (=> (= in-19 #b10001) (= valin-19-1 valout-17-1)))
(assert (=> (= in-19 #b10010) (= valin-19-1 valout-18-1)))
(assert (=> (= in-19 #b10011) (= valin-19-1 valout-19-1)))
;(assert (=> (= in-19 #b10100) (= valin-19-1 valout-20-1)))
;(assert (=> (= in-19 #b10101) (= valin-19-1 valout-21-1)))
;(assert (=> (= in-19 #b10110) (= valin-19-1 valout-22-1)))
;(assert (=> (= in-19 #b10111) (= valin-19-1 valout-23-1)))


; Copy of above with in-->ina valin-->valina valout-->valouta


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
           (and (not (= in-1 #b00001))(not (= in-2 #b00001))(not (= in-3 #b00001))(not (= in-4 #b00001))(not (= in-5 #b00001))(not (= in-6 #b00001))(not (= in-7 #b00001))(not (= in-8 #b00001))(not (= in-9 #b00001))(not (= in-10 #b00001))(not (= in-11 #b00001))(not (= in-12 #b00001))(not (= in-13 #b00001))(not (= in-14 #b00001))(not (= in-15 #b00001))(not (= in-16 #b00001))(not (= in-17 #b00001))(not (= in-18 #b00001))(not (= in-19 #b00001)))))
(assert (= (= in-2 #b00000) (= in-3 #b00000)))

; out2 out3 in-4 in-5 in-18
(assert (= (= in-4 #b00000)
           (and (and (not (= in-1 #b00010))(not (= in-2 #b00010))(not (= in-3 #b00010))(not (= in-4 #b00010))(not (= in-5 #b00010))(not (= in-6 #b00010))(not (= in-7 #b00010))(not (= in-8 #b00010))(not (= in-9 #b00010))(not (= in-10 #b00010))(not (= in-11 #b00010))(not (= in-12 #b00010))(not (= in-13 #b00010))(not (= in-14 #b00010))(not (= in-15 #b00010))(not (= in-16 #b00010))(not (= in-17 #b00010))(not (= in-18 #b00010))(not (= in-19 #b00010)))
                (and (not (= in-1 #b00011))(not (= in-2 #b00011))(not (= in-3 #b00011))(not (= in-4 #b00011))(not (= in-5 #b00011))(not (= in-6 #b00011))(not (= in-7 #b00011))(not (= in-8 #b00011))(not (= in-9 #b00011))(not (= in-10 #b00011))(not (= in-11 #b00011))(not (= in-12 #b00011))(not (= in-13 #b00011))(not (= in-14 #b00011))(not (= in-15 #b00011))(not (= in-16 #b00011))(not (= in-17 #b00011))(not (= in-18 #b00011))(not (= in-19 #b00011))))))
(assert (= (= in-4 #b00000) (= in-5 #b00000)))
(assert (= (= in-4 #b00000) (= in-18 #b00000)))

; out4 out5 in-6 in-7 in-19
(assert (= (= in-6 #b00000)
           (and (and (not (= in-1 #b00100))(not (= in-2 #b00100))(not (= in-3 #b00100))(not (= in-4 #b00100))(not (= in-5 #b00100))(not (= in-6 #b00100))(not (= in-7 #b00100))(not (= in-8 #b00100))(not (= in-9 #b00100))(not (= in-10 #b00100))(not (= in-11 #b00100))(not (= in-12 #b00100))(not (= in-13 #b00100))(not (= in-14 #b00100))(not (= in-15 #b00100))(not (= in-16 #b00100))(not (= in-17 #b00100))(not (= in-18 #b00100))(not (= in-19 #b00100)))
                (and (not (= in-1 #b00101))(not (= in-2 #b00101))(not (= in-3 #b00101))(not (= in-4 #b00101))(not (= in-5 #b00101))(not (= in-6 #b00101))(not (= in-7 #b00101))(not (= in-8 #b00101))(not (= in-9 #b00101))(not (= in-10 #b00101))(not (= in-11 #b00101))(not (= in-12 #b00101))(not (= in-13 #b00101))(not (= in-14 #b00101))(not (= in-15 #b00101))(not (= in-16 #b00101))(not (= in-17 #b00101))(not (= in-18 #b00101))(not (= in-19 #b00101))))))
(assert (= (= in-6 #b00000) (= in-7 #b00000)))
(assert (= (= in-6 #b00000) (= in-19 #b00000)))

; out8 in-8 in-9
(assert (= (= in-8 #b00000)
           (and (not (= in-1 #b01000))(not (= in-2 #b01000))(not (= in-3 #b01000))(not (= in-4 #b01000))(not (= in-5 #b01000))(not (= in-6 #b01000))(not (= in-7 #b01000))(not (= in-8 #b01000))(not (= in-9 #b01000))(not (= in-10 #b01000))(not (= in-11 #b01000))(not (= in-12 #b01000))(not (= in-13 #b01000))(not (= in-14 #b01000))(not (= in-15 #b01000))(not (= in-16 #b01000))(not (= in-17 #b01000))(not (= in-18 #b01000))(not (= in-19 #b01000)))))
(assert (= (= in-8 #b00000) (= in-9 #b00000)))

; out9 in-10 in-11
(assert (= (= in-10 #b00000)
           (and (not (= in-1 #b01001))(not (= in-2 #b01001))(not (= in-3 #b01001))(not (= in-4 #b01001))(not (= in-5 #b01001))(not (= in-6 #b01001))(not (= in-7 #b01001))(not (= in-8 #b01001))(not (= in-9 #b01001))(not (= in-10 #b01001))(not (= in-11 #b01001))(not (= in-12 #b01001))(not (= in-13 #b01001))(not (= in-14 #b01001))(not (= in-15 #b01001))(not (= in-16 #b01001))(not (= in-17 #b01001))(not (= in-18 #b01001))(not (= in-19 #b01001)))))
(assert (= (= in-10 #b00000) (= in-11 #b00000)))

; out10 in-12 in-13
(assert (= (= in-12 #b00000)
           (and (not (= in-1 #b01010))(not (= in-2 #b01010))(not (= in-3 #b01010))(not (= in-4 #b01010))(not (= in-5 #b01010))(not (= in-6 #b01010))(not (= in-7 #b01010))(not (= in-8 #b01010))(not (= in-9 #b01010))(not (= in-10 #b01010))(not (= in-11 #b01010))(not (= in-12 #b01010))(not (= in-13 #b01010))(not (= in-14 #b01010))(not (= in-15 #b01010))(not (= in-16 #b01010))(not (= in-17 #b01010))(not (= in-18 #b01010))(not (= in-19 #b01010)))))
(assert (= (= in-12 #b00000) (= in-13 #b00000)))

; out11 in-14 in-15
(assert (= (= in-14 #b00000)
           (and (not (= in-1 #b01011))(not (= in-2 #b01011))(not (= in-3 #b01011))(not (= in-4 #b01011))(not (= in-5 #b01011))(not (= in-6 #b01011))(not (= in-7 #b01011))(not (= in-8 #b01011))(not (= in-9 #b01011))(not (= in-10 #b01011))(not (= in-11 #b01011))(not (= in-12 #b01011))(not (= in-13 #b01011))(not (= in-14 #b01011))(not (= in-15 #b01011))(not (= in-16 #b01011))(not (= in-17 #b01011))(not (= in-18 #b01011))(not (= in-19 #b01011)))))
(assert (= (= in-14 #b00000) (= in-15 #b00000)))

; out12-15 in-16
(assert (= (= in-16 #b00000)
           (and (and (not (= in-1 #b01100))(not (= in-2 #b01100))(not (= in-3 #b01100))(not (= in-4 #b01100))(not (= in-5 #b01100))(not (= in-6 #b01100))(not (= in-7 #b01100))(not (= in-8 #b01100))(not (= in-9 #b01100))(not (= in-10 #b01100))(not (= in-11 #b01100))(not (= in-12 #b01100))(not (= in-13 #b01100))(not (= in-14 #b01100))(not (= in-15 #b01100))(not (= in-16 #b01100))(not (= in-17 #b01100))(not (= in-18 #b01100))(not (= in-19 #b01100)))
                (and (not (= in-1 #b01101))(not (= in-2 #b01101))(not (= in-3 #b01101))(not (= in-4 #b01101))(not (= in-5 #b01101))(not (= in-6 #b01101))(not (= in-7 #b01101))(not (= in-8 #b01101))(not (= in-9 #b01101))(not (= in-10 #b01101))(not (= in-11 #b01101))(not (= in-12 #b01101))(not (= in-13 #b01101))(not (= in-14 #b01101))(not (= in-15 #b01101))(not (= in-16 #b01101))(not (= in-17 #b01101))(not (= in-18 #b01101))(not (= in-19 #b01101)))
                (and (not (= in-1 #b01110))(not (= in-2 #b01110))(not (= in-3 #b01110))(not (= in-4 #b01110))(not (= in-5 #b01110))(not (= in-6 #b01110))(not (= in-7 #b01110))(not (= in-8 #b01110))(not (= in-9 #b01110))(not (= in-10 #b01110))(not (= in-11 #b01110))(not (= in-12 #b01110))(not (= in-13 #b01110))(not (= in-14 #b01110))(not (= in-15 #b01110))(not (= in-16 #b01110))(not (= in-17 #b01110))(not (= in-18 #b01110))(not (= in-19 #b01110)))
                (and (not (= in-1 #b01111))(not (= in-2 #b01111))(not (= in-3 #b01111))(not (= in-4 #b01111))(not (= in-5 #b01111))(not (= in-6 #b01111))(not (= in-7 #b01111))(not (= in-8 #b01111))(not (= in-9 #b01111))(not (= in-10 #b01111))(not (= in-11 #b01111))(not (= in-12 #b01111))(not (= in-13 #b01111))(not (= in-14 #b01111))(not (= in-15 #b01111))(not (= in-16 #b01111))(not (= in-17 #b01111))(not (= in-18 #b01111))(not (= in-19 #b01111))))))

; out16-19 in-17
(assert (= (= in-17 #b00000)
           (and (and (not (= in-1 #b10000))(not (= in-2 #b10000))(not (= in-3 #b10000))(not (= in-4 #b10000))(not (= in-5 #b10000))(not (= in-6 #b10000))(not (= in-7 #b10000))(not (= in-8 #b10000))(not (= in-9 #b10000))(not (= in-10 #b10000))(not (= in-11 #b10000))(not (= in-12 #b10000))(not (= in-13 #b10000))(not (= in-14 #b10000))(not (= in-15 #b10000))(not (= in-16 #b10000))(not (= in-17 #b10000))(not (= in-18 #b10000))(not (= in-19 #b10000)))
                (and (not (= in-1 #b10001))(not (= in-2 #b10001))(not (= in-3 #b10001))(not (= in-4 #b10001))(not (= in-5 #b10001))(not (= in-6 #b10001))(not (= in-7 #b10001))(not (= in-8 #b10001))(not (= in-9 #b10001))(not (= in-10 #b10001))(not (= in-11 #b10001))(not (= in-12 #b10001))(not (= in-13 #b10001))(not (= in-14 #b10001))(not (= in-15 #b10001))(not (= in-16 #b10001))(not (= in-17 #b10001))(not (= in-18 #b10001))(not (= in-19 #b10001)))
                (and (not (= in-1 #b10010))(not (= in-2 #b10010))(not (= in-3 #b10010))(not (= in-4 #b10010))(not (= in-5 #b10010))(not (= in-6 #b10010))(not (= in-7 #b10010))(not (= in-8 #b10010))(not (= in-9 #b10010))(not (= in-10 #b10010))(not (= in-11 #b10010))(not (= in-12 #b10010))(not (= in-13 #b10010))(not (= in-14 #b10010))(not (= in-15 #b10010))(not (= in-16 #b10010))(not (= in-17 #b10010))(not (= in-18 #b10010))(not (= in-19 #b10010)))
                (and (not (= in-1 #b10011))(not (= in-2 #b10011))(not (= in-3 #b10011))(not (= in-4 #b10011))(not (= in-5 #b10011))(not (= in-6 #b10011))(not (= in-7 #b10011))(not (= in-8 #b10011))(not (= in-9 #b10011))(not (= in-10 #b10011))(not (= in-11 #b10011))(not (= in-12 #b10011))(not (= in-13 #b10011))(not (= in-14 #b10011))(not (= in-15 #b10011))(not (= in-16 #b10011))(not (= in-17 #b10011))(not (= in-18 #b10011))(not (= in-19 #b10011))))))

; Copy of above with in-->ina


;
; The system output must be connected. 
; 
(assert (not (= in-1 #b00000)))



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


;----------------------------------------------------------------------------
; The values printed depend on whether we are doing circuit synthesis
; or generating a distinguishing input. Additionally we essentially
; dump all variables in debug mode except for those not anticipated to  
; cause any bugs (eg values on internal nets) 
;----------------------------------------------------------------------------
(check-sat)
(get-value (in-1 in-2 in-3 in-4 in-5 in-6 in-7 in-8 in-9 in-10
            in-11 in-12 in-13 in-14 in-15 in-16 in-17 in-18 in-19))





;(get-unsat-core) 
(exit)
