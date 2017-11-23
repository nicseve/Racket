#lang racket
(require racket/trace)
; Wires and gates.

; A wire is identified by a Racket symbol, for example 'x, 'y0, or 'next.
; Strings (eg, "x" or "next") are not permitted wire names.

; A gate is a struct with three fields: 
; 1) a symbol indicating the type of gate, one of:
;       not, and, or, xor, nand, nor
; 2) a list of the wire identifiers of the inputs
; 3) the output wire identifier

(struct gate (type inputs output) #:transparent)

; Examples of gates:

(define gate1 (gate 'and '(x y) 'z))
(define gate2 (gate 'or '(x v) 'v))
(define gate3 (gate 'not '(s) 't))
(define gate4 (gate 'nand '(x x) 'z))

;**********************************************************

; Circuits.

; A circuit is a struct with three fields
; (1) a list of input wire identifiers
; (2) a list of output wire identifiers
; (3) a list of gates

(struct ckt (inputs outputs gates) #:transparent)

;**********************************************************
; Examples of circuits

; Here is a circuit to compare the values of its two inputs
; and output 1 if they are equal, 0 if they are unequal.
; This computes one-bit compare for equality, and implements
; the sum-of-products representation.  This is a combinational
; circuit (no cycle of wires and gates.)

(define eq1-ckt
  (ckt
   '(x y)
   '(z)
   (list
    (gate 'not '(x) 'cx)
    (gate 'not '(y) 'cy)
    (gate 'and '(x y) 't1)
    (gate 'and '(cx cy) 't2)
    (gate 'or '(t1 t2) 'z))))
 
; This is interpreted as follows:
; the inputs of the circuit are the wires x and y,
; the outputs of the circuit consist of just the wire z,
; there are five gates specified as follows:
; wire cx is the output of a NOT gate with input x,
; wire cy is the output of a NOT gate with input y,
; wire t1 is the output of an AND gate with inputs x and y,
; wire t2 is the output of an AND gate with inputs cx and cy,
; wire z is the output of an OR gate with inputs t1 and t2.

; Here is another implementation of comparing two bits for equality.
; This uses the implementation as the NOT of (x XOR y).
; This is also a combinational circuit.
; The inputs and output of this circuit are named as in eq1-ckt.

(define eq2-ckt
  (ckt
   '(x y)
   '(z)
   (list
    (gate 'xor '(x y) 'w)
    (gate 'not '(w) 'z))))

; Here is a two-bit selector whose Boolean expressions are as follows.

; z_1 = x_1 * s' + y_1 * s
; z_0 = x_0 * s' + y_0 * s

; For this circuit, z_1 and z_0 are
; equal to x_1 and x_0 if s = 0, and
; z_1 and z_0 are equal to y_1 and y_0
; if s = 1.

; This is also a combinational circuit.

(define sel-ckt
  (ckt
   '(x1 x0 y1 y0 s)
   '(z1 z0)
   (list
    (gate 'not '(s) 'sc)
    (gate 'and '(x1 sc) 'u1)
    (gate 'and '(y1 s) 'v1)
    (gate 'or '(u1 v1) 'z1)
    (gate 'and '(x0 sc) 'u0)
    (gate 'and '(y0 s) 'v0)
    (gate 'or '(u0 v0) 'z0))))

; This is a NAND latch, used to store one bit.
; It is a sequential (not combinational) circuit,
; because it has a loop from a wire to itself through
; other wires and gates.

(define latch-ckt
  (ckt
   '(x y)
   '(q u)
   (list
    (gate 'nand '(x u) 'q)
    (gate 'nand '(y q) 'u))))

; The following is also a sequential circuit, with
; an OR gate one of whose inputs is its output.
; (The "Garden of Eden" circuit.)

(define seq-or-ckt
  (ckt
   '(x)
   '(z)
   (list
    (gate 'or '(x z) 'z))))

; The next is also a sequential circuit.
; It could serve as a clock.
; Note that this circuit has *no* inputs, but
; does have an output.

(define clock-ckt
  (ckt
   '()
   '(z)
   (list
    (gate 'not '(z) 'z))))

; (good-gate? value)
; (good-circuit? value)

; (good-gate? value) takes an arbitrary value
; and returns #t if it is a well-formed gate,
; and #f otherwise.
; To be a well-formed gate, the value must be
; a gate struct whose three fields satisfy
; (1) the type field is one of the gate symbols:
;     'not, 'and, 'or, 'xor, 'nand, 'nor,
; (2) the inputs field is a list of wire identifiers
; (3) the output field is a single wire identifier

; (good-circuit? value) takes an arbitrary value and
; returns #t if value is a well-formed circuit, 
; and returns #f otherwise.

(define types '(not and or xor nand nor))

(define (symb-chk type lst)
  (cond
    [ (and (equal? type 'not) (symbol? lst)) #f]
    [ (list? lst) (andmap symbol? lst)]
    [else #f]))


(define (good-gate? value)
  (let* ([cur-type (gate-type value)])
    (if (and (member cur-type types) (symb-chk cur-type (gate-inputs value)) (symbol? (gate-output value)))
        (cond
          [(and (equal? 'not cur-type) (= 1 (length (list(gate-inputs value))))) #t]
          [(= 2 (length (gate-inputs value))) #t]
          [else #f])
        #f)))
              

(define (mem-check lst1 lst2)
  (cond
    [(empty? lst1) #f]
    [(member (car lst1) lst2) #t]
    [else (mem-check (cdr lst1) lst2)]))



(define (mem-check-list elem lst2 n)
  (cond
    [(= n 2) #t]
    [(empty? lst2) #f]
    [(member elem lst2) (mem-check-list elem (cdr (member elem lst2)) (+ 1 n))  ]
    [else (mem-check-list elem (cdr lst2) n)]))
                              
       

(define (inp-out lst1 lst2)
  (append lst1 lst2))


(define (member-aux lst1 lst2 lst3)
  (cond
    [(empty? lst1) #t]
    [(or (member (car lst1) lst2) (member (car lst1) lst3)) (member-aux (cdr lst1) lst2 lst3)]
    [else #f]))



(define (good-circuit? value)

  (cond
    [(not (struct? value)) #f]
    [(not (and (list? (ckt-inputs value)) (list? (ckt-outputs value)) (list? (ckt-gates value)) )) #f]
    [(and (empty? (ckt-inputs value)) (empty? (ckt-outputs value)) (empty? (ckt-gates value)) ) #t]
    [(not (or (empty? (ckt-gates value))  (andmap good-gate? (ckt-gates value)))) #f ]
    [ (mem-check (ckt-inputs value) (map (lambda (x) (gate-output x)) (ckt-gates value))) #f]
    [(not (or (ormap (lambda (x)
                       (mem-check (gate-inputs x) (ckt-inputs value)))
                     (ckt-gates value)) (ormap (lambda (x)  
                                                 (mem-check (gate-inputs x) (map (lambda (x) (gate-output x)) (ckt-gates value))))
                                               (ckt-gates value))  )) #f]
    [(member #t (map (lambda (x) (mem-check-list  x  (map (lambda (x) (gate-output x)) (ckt-gates value)) 0) ) (inp-out (ckt-inputs value) (ckt-outputs value))))  #f]
    
    [(not (member-aux (ckt-outputs value) (ckt-inputs value) (map (lambda (x) (gate-output x)) (ckt-gates value)))) #f] 

    [else #t]))
  



; (all-wires circuit) to return the list of all the wire names that appear
;      in the circuit, as circuit inputs, circuit outputs, gate
;      inputs or gate outputs, in that order, with duplicates removed.
; (find-gate wire circuit) to return the gate in the circuit with the given
;      output wire, or #f if there is no such gate.


(define (app-in lst)
  (cond
    [(empty? lst) null]
    [(list? (car lst)) (append (app-in (car lst)) (app-in (cdr lst)))]
    [(cons (car lst) (app-in (cdr lst)))]))
    

(define (all-wires circuit)
  (remove-duplicates (append (ckt-inputs circuit) (ckt-outputs circuit) (map (lambda (x) (gate-output x)) (ckt-gates circuit)) (app-in (map (lambda (x) (gate-inputs x)) (ckt-gates circuit)))  )))


(define (lookup key table)
  (cond
    [(empty? table) #f]
    [(equal? key (gate-output (car table))) (car table) ]
    [else (lookup key (cdr table))]))


(define (find-gate wire circuit)
  (let* ([table (ckt-gates circuit)])
    (lookup wire table)))



(define ex2-ckt
  (ckt
   '(x y)
   '(z)
   (list
    (gate 'xor '(x y) 'w)
    (gate 'not '(w) 'z))))



(define ha-ckt
    (ckt
         '(x y)
         '(z co)
         (list
          (gate 'xor '(x y) 'z)
          (gate 'and '(x y) 'co))))


(define fa-ckt
  (ckt
   '(x y ci)
   '(z co)
   (list
    (gate 'and  '(x y) 'w)
    (gate 'and '(y ci) 'q)
    (gate 'and '(x ci) 'p)
    (gate 'or  '(w q) 'v)
    (gate 'or '(v p) 'co)
    (gate 'xor '(x y) 'g)
    (gate 'xor '(g ci) 'z))))
    
   
;**********************************************************
; A configuration of a circuit is a table giving a value (0 or 1) for each wire in the circuit.  
; A table is a list of entries, each entry containing a key (the wire name) and a value (0 or 1).

(struct entry (key value) #:transparent)

; Examples
; Two configurations of the wires of the eq1-ckt
; Note that the order of wires in the configuration is that returned by (all-wires eq1-ckt).

(define eq1-config1
  (list
   (entry 'x 0)
   (entry 'y 1)
   (entry 'z 0)
   (entry 'cx 0)
   (entry 'cy 0)
   (entry 't1 0)
   (entry 't2 0)))

(define eq1-config2 
  (list
   (entry 'x 0)
   (entry 'y 0)
   (entry 'z 0)
   (entry 'cx 1)
   (entry 'cy 1)
   (entry 't1 0)
   (entry 't2 0)))

; Two configurations of the wires of the sel-ckt

(define sel-config1
  (list
   (entry 'x1 0)
   (entry 'x0 1)
   (entry 'y1 1)
   (entry 'y0 0)
   (entry 's 1)
   (entry 'z1 0)
   (entry 'z0 0)
   (entry 'sc 0)
   (entry 'u1 0)
   (entry 'v1 0)
   (entry 'u0 0)
   (entry 'v0 0)))


(define sel-config2
  (list
   (entry 'x1 1)
   (entry 'x0 1)
   (entry 'y1 0)
   (entry 'y0 0)
   (entry 's 0)
   (entry 'z1 0)
   (entry 'z0 0)
   (entry 'sc 1)
   (entry 'u1 0)
   (entry 'v1 0)
   (entry 'u0 0)
   (entry 'v0 0)))

; Two configurations of the wires of the latch-ckt

(define latch-config1
  (list
   (entry 'x 0)
   (entry 'y 0)
   (entry 'q 0)
   (entry 'u 0)))

(define latch-config2
  (list
   (entry 'x 0)
   (entry 'y 1)
   (entry 'q 1)
   (entry 'u 0)))


;(next-value wire circuit config)

; that returns the value on the given wire of the given circuit, *after one gate delay*
; starting with the given configuration config of the circuit.

(define (wire-val wire config)
  (cond
    [(empty? config) #f]
   [(equal? wire (entry-key (car config))) (entry-value(car config)) ]
    [else (wire-val wire (cdr config))]))



(define (reconverter bool)  ;converts boolean to binary
  (if (equal? bool #t)
      1
      0))

(define (converter exp)   ;converts binary to boolean
 (if (equal? exp 1)
     #t
     #f))

(define (flip-boo exp)      ;not function on a given boolean
  (if (equal? #f exp)
      #t
      #f))


(define (flip-dig val)      ;not function on a given binary digit
  (if (equal? 0 val)
      1
      0))


(define (next-value wire circuit config)

  (if (member wire (ckt-inputs circuit))
      (wire-val wire config)
  (let* ([gate (find-gate wire circuit)])
    (cond
      [(equal? 'not (gate-type gate)) (flip-dig (wire-val (car(gate-inputs gate)) config))]
      [(equal? 'and (gate-type gate)) (reconverter(and    (converter (wire-val (car(gate-inputs gate)) config))   (converter (wire-val (cadr(gate-inputs gate)) config))))]
      [(equal? 'nand (gate-type gate)) (flip-dig (reconverter(and (converter (wire-val (car(gate-inputs gate)) config)) (converter (wire-val (cadr(gate-inputs gate)) config)))))]
      [(equal? 'or (gate-type gate))  (reconverter(or (converter (wire-val (car(gate-inputs gate)) config))   (converter (wire-val (cadr(gate-inputs gate)) config))))]
      [(equal? 'nor (gate-type gate))  (flip-dig(reconverter(or (converter (wire-val (car(gate-inputs gate)) config))   (converter (wire-val (cadr(gate-inputs gate)) config)))))]
      [else (equal? 'xor (gate-type gate))  (reconverter
                                             (or
                                              (and (converter (wire-val (car(gate-inputs gate)) config))   (flip-boo(converter (wire-val (cadr(gate-inputs gate)) config))))
                                              (and (flip-boo(converter (wire-val (car(gate-inputs gate)) config)))   (converter (wire-val (cadr(gate-inputs gate)) config)))))]))))
    
     



; (next-config circuit config)

; that takes a circuit and a current configuration config
; and returns the "next" configuration of the circuit, after *one gate delay* has elapsed.


(define (next-config circuit config)
  (map (lambda (x)
         (entry (entry-key x) (next-value (entry-key x) circuit config)))
       config))



; (stable? circuit config)
; returns #t if the next configuration of the circuit after the configuration config
; is the same as config, ie, this configuration is stable for the circuit.

; (all-stable-configs circuit)
; returns a list of all the stable configurations of the circuit.
; The wires in the configurations should be listed in the same order as (all-wires circuit),
; and the values in the configurations list should be in increasing order, considered as
; binary numbers.

; (output-values circuit config)
; returns a list giving the Boolean values of each of the output wires of
; the circuit in the configuration config.
; The order is the same as the list of output wires of the circuit.

; (init-config circuit input-values)
; takes a circuit and a list input-values of Boolean values
; which has the same length as the number of inputs of the circuit
; and returns a configuration in which the circuit input wires have the values 
; specified (in order) by the list inputs, and all other wires have the value 0.

;**********************************************************

(define (stable? circuit config)
  (if (andmap equal? config (next-config circuit config))
      #t
      #f))

; A configuration of a circuit is a table giving a value (0 or 1) for each wire in the circuit.  
; A table is a list of entries, each entry containing a key (the wire name) and a value (0 or 1).


(define (all-combs n)  ;creates a list of 'wire-length' increasing binary digits
  (if (= 0 n)
      '(())
  (let* ([cur (all-combs (- n 1))])
   (append (map
            (lambda (x)
              (cons 0 x)
              )cur)
    (map
         (lambda (x)
           (cons 1 x)
           ) cur)))))


(define (config-mkr comb wires)   ;creates 'config from various combinations of 0's and 1's passed by mapping of all-combs function
 (cond
   [(empty? wires) null]
   [else (append (list (entry (car wires) (car comb))) (config-mkr (cdr comb) (cdr wires)))]))
   


(define (config-list circuit)   ;creates list of configurations based off all-combs
  (let* ([wires (all-wires circuit)])
        (map
         (lambda (x)
           (config-mkr x wires)) (all-combs (length wires)))))



(define (all-stable-configs circuit)
  (filter list? (map (lambda (x)
         (if (stable? circuit x)
             x
             1
             )) (config-list circuit))))


(define (output-values circuit config)
  (map (lambda (x)
         (wire-val x config))
       (ckt-outputs circuit)))


(define (init-config circuit input-values)
  (remove-duplicates (append (config-mkr input-values (ckt-inputs circuit))
          (config-mkr (build-list (length (ckt-outputs circuit)) (lambda (x) 0)) (ckt-outputs circuit))
          (config-mkr (build-list (length (map (lambda (x) (gate-output x)) (ckt-gates circuit))) (lambda (x) 0)) (map (lambda (x) (gate-output x)) (ckt-gates circuit))))))


; *********************************************************


; (simulate circuit config n)

; which simulates the given circuit from the given configuration 
; by repeatedly calling next-config until either
; the configuration reached is stable, or
; next-config has been called n times, whichever occurs first.


(define (simulate circuit config n)
    (cond
          [(= n 0) (list config)]
          [(stable? circuit config) (list config)]
          [else (append (list config) (simulate circuit (next-config circuit config) (- n 1)))]))


; (final-config circuit config)

; that takes a circuit and a configuration config for the circuit.
; If the circuit would eventually reach a stable configuration 
; from config, then (final-config circuit config) returns the
; stable configuration of the circuit that would be reached.

; Otherwise, (final-config circuit config) returns the symbol 'none.


(define (all-config-values config)
  (map (lambda (x)
         (entry-value x))
       config))

(define (final-config circuit config)
  (cond [(stable? circuit config) config]
        [else (sim-halt circuit (next-config circuit config) empty)]))

(define (sim-halt circuit config seen-configs)
  (cond 
    [(stable? circuit config) config]
    [(member (all-config-values config) seen-configs) 'none]
    [else (sim-halt circuit (next-config circuit config) (append (list(all-config-values config)) seen-configs))]))

 ;4-bit ripple-carry adder circuit 
  ;**********************************************************

(define add-ckt
  (ckt
   '(x3 x2 x1 x0 y3 y2 y1 y0)
   '(z4 z3 z2 z1 z0)
  (list
   (gate 'xor '(x0 y0) 'z0) ;half-adder for two least significant bits
   (gate 'and '(x0 y0) 'co)
   
   (gate 'and  '(x1 y1) 'w) ;full-adder
   (gate 'and '(y1 co) 'q)
   (gate 'and '(x1 co) 'p)
   (gate 'or  '(w q) 'v)
   (gate 'or '(v p) 'c1)
   (gate 'xor '(x1 y1) 'g)
   (gate 'xor '(g co) 'z1)
   
   (gate 'and  '(x2 y2) 'j) ;full-adder
   (gate 'and '(y2 c1) 'l)
   (gate 'and '(x2 c1) 'm)
   (gate 'or  '(j l) 's)
   (gate 'or '(s m) 'c2)
   (gate 'xor '(x2 y2) 't)
   (gate 'xor '(t c1) 'z2)

   (gate 'and  '(x3 y3) 'd) ;full-adder
   (gate 'and '(y3 c2) 'o)
   (gate 'and '(y3 c2) 'b)
   (gate 'or  '(d o) 'k)
   (gate 'or '(k b) 'z4)
   (gate 'xor '(x3 y3) 'i)
   (gate 'xor '(i c2) 'z3))))



;**********************************************************


; Define a D-flipflop 

(define dff-ckt
  (ckt
   '(s d)
   '(q qc)
   (list
    (gate 'and '(s d) 'p)
    (gate 'not '(p) 'r)
    (gate 'and '(r qc) 'x)
    (gate 'not '(x) 'q)
    (gate 'not '(d) 't)
    (gate 'and '(t s) 'z)
    (gate 'not '(z) 'm)
    (gate 'and '(m q) 'y)
    (gate 'not '(y) 'qc))))


circuit timing-ckt.

(define timing-ckt
  (ckt
   '()
   '(t)  
   (list
    (gate 'not '(a) 'b) 
    (gate 'and '(b b) 'c) 
    (gate 'and '(c c) 'd) 
    (gate 'and '(d d) 't)
    (gate 'nand '(t t) 'a))))


