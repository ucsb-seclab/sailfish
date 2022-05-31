#lang s-exp rosette
(require rosette/solver/smt/z3)
(require rosette/solver/smt/cvc4)
(require rosette/solver/smt/yices)
(define (set-solver str-solver)
	(cond
		[(equal? str-solver "z3") (current-solver (z3))]
		[(equal? str-solver "cvc4") (if (cvc4-available?) (current-solver (cvc4)) (print-and-exit (format "# set-solver: cvc4 is not available.\n")))]
		[(equal? str-solver "yices") (if (yices-available?) (current-solver (yices)) (print-and-exit (format "# set-solver: yices is not available.\n")))]
		[else (print-and-exit (format "# set-solver: unrecognized solver, got: ~a\n" str-solver))]
	)
)

(require json rosette/query/debug racket/sandbox racket/cmdline "solidity-parser.rkt" "inst.rkt" "zhash.rkt")
; ==== global init ==== ;
(define block-hash (new zhash [cap 5000]))
(define (block-has-key? pk) (zhash-has-key? block-hash pk))
(define (block-ref pk) (zhash-ref block-hash pk))
(define (block-set! pk pv) (zhash-set! block-hash pk pv))
(define register-hash (new zhash [cap 5000]))
(define (register-has-key? pk) (zhash-has-key? register-hash pk))
(define (register-ref pk) (zhash-ref register-hash pk))
(define (register-set! pk pv) (zhash-set! register-hash pk pv))
; ===================== ;
; ==== block execution count (bec) ==== ;
; (notice) bec only tracks the normal block executions
; since we assume no infinite loop needs bounding in range/global blocks
(define bec-hash (make-hash))
(define (bec-has-key? pk) (hash-has-key? bec-hash pk))
(define (bec-ref pk) (hash-ref bec-hash pk))
(define (bec-set! pk pv) (hash-set! bec-hash pk pv))
; ===================================== ;
; ==== storing types of register (for use of havoc/RESET operator) ==== ;
(define register-types (make-hash))
; ==== storing uninterpreted functions ==== ;
(define function-hash (make-hash))
; ===================================================================== ;

; =====>
; reg-make-? series
; create a symbolic variable of designated type and store it in the registers
; if there's already one, then triggers the assertion exception
; update: don't use constant, do it like this --- 
;   (eval `(define-symbolic ,(string->symbol "myname") integer?) ns)
;   (define var (string->symbol "myname"))
; =====>
; amazing :)
; the next-? procedures creat stream of symbolic variables (like define-symbolic* but they now works in a dynamic way
; in that they accept dynamic names)
; (important) this works differently as calling separate `dynamic` procedures as introduced in Rosette documentations
; (important, FIXME) haven't confirmed this is OK in both normal mode and U syntactic sugar explanation
(define (next-symbolic-boolean r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) boolean?))
	var
)
(define (next-symbolic-integer r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) integer?))
	var
)
(define (next-symbolic-function-1 r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) (~> integer? integer?)))
	var
)
(define (next-symbolic-function-2 r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) (~> integer? integer? integer?)))
	var
)
(define (next-symbolic-function-3 r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) (~> integer? integer? integer? integer?)))
	var
)
(define (next-symbolic-function-4 r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) (~> integer? integer? integer? integer? integer?)))
	var
)
(define (next-symbolic-function-5 r-name)
	(define var (constant (list (string->symbol r-name) ((current-oracle) (string->symbol r-name))) (~> integer? integer? integer? integer? integer? integer?)))
	var
)
(define (reg-make-boolean r-name #:store [store #t])
	(define var (next-symbolic-boolean r-name))
	(when store (register-set! r-name var))
	var
)
(define (reg-make-integer r-name #:store [store #t])
	(define var (next-symbolic-integer r-name))
	(when store (register-set! r-name var))
	var
)
(define (reg-make-unknown r-name #:store [store #t])
	(define u-indicator (next-symbolic-boolean "u-indicator"))
	(define u-integer (next-symbolic-integer r-name))
	(define u-boolean (next-symbolic-boolean r-name))
	; #f: boolean, #t: integer
	(define var (if u-indicator u-integer u-boolean))
	(when store (register-set! r-name var))
	var
)
(define (reg-make-vector r-name r-type #:vlen [vlen 10] #:store [store #t])
	; second distribution call
	(define var
		(list->vector
			(for/list ([i (range vlen)])
				; (notice) don't store to regs, for all second layers of vector this apply
				(if (list? r-type)
					(reg-make-type (format "~a#~a" r-name i) r-type #:store #f) ; r-type is end type
					(reg-make-type (format "~a#~a" r-name i) (list r-type) #:store #f) ; r-type is array type / array of arrays
				)
	)))
	(when store (register-set! r-name var))
	var
)
; make uninterpreted functions
(define (reg-make-function r-name r-type #:store [store #t])
	(define var
		(cond
			[(equal? r-type "function1") (next-symbolic-function-1 r-name)]
			[(equal? r-type "function2") (next-symbolic-function-2 r-name)]
			[(equal? r-type "function3") (next-symbolic-function-3 r-name)]
			[(equal? r-type "function4") (next-symbolic-function-4 r-name)]
			[(equal? r-type "function5") (next-symbolic-function-5 r-name)]
			[else (print-and-exit (format "# reg-make-function: unsupported function type, got ~a" r-type))]
		)
	)
	(when store (hash-set! function-hash r-name var))
	var
)
; procedure that distributes reg-make requests
(define (reg-make-type r-name r-type #:store [store #t] #:use-default [use-default #f])
	(define primary-type (list-ref r-type 0))
	(define secondary-type (list-ref (reverse r-type) 0)) ; only for array type for the present
	(cond
		[(equal? primary-type "unknown") (reg-make-unknown r-name #:store store)]
		[(equal? primary-type "boolean") 
			(if use-default
				; use default value
				(register-set! r-name #f)
				; use symbolic
				(reg-make-boolean r-name #:store store)
			)
		]
		[(equal? primary-type "integer") 
			(if use-default
				; use default value
				(register-set! r-name 0)
				; use symbolic
				(reg-make-integer r-name #:store store)
			)
		]
		[(equal? primary-type "array") 
			(if use-default
				; use default value
				; fixme: here for default init, vlen is fixed to 10
				(cond
					[(equal? secondary-type "integer")
						; integer
						(register-set! r-name (list->vector (for/list ([i (range 10)]) 0)))
					]
					[(equal? secondary-type "boolean")
						; boolean
						(register-set! r-name (list->vector (for/list ([i (range 10)]) #f)))
					]
					[else
						; use symbolic
						(reg-make-vector r-name secondary-type #:store store)
					]
				)
				; use symbolic
				(reg-make-vector r-name secondary-type #:store store)
			)
		]
		[(string-prefix? primary-type "function") (reg-make-function r-name primary-type)]
		; else, query the struct type
		[else 
			(if (hash-has-key? struct-constructors primary-type)
				; yes we have this type, call the constructors
				((hash-ref struct-constructors primary-type) r-name #:store store)
				; no such struct, error
				(print-and-exit (format "# reg-make-type: unsupported target type, got ~a\n" r-type))
			)
		]
	)
)

; ==== meta method for building struct constructor ==== ;
(define struct-constructors (make-hash)) ; stores struct constructors
(define (make-struct-constructor r-struct)
	(define r-name (hash-ref r-struct `name))
	(define r-fields (hash-ref r-struct `fields))

	; this is the constructor to return
	(define (g-constructor g-name #:store [store #t])
		; r-struct is the struct dict in json
		(define root-instance (new zhash [cap 100]))
		(for ([r-key (hash-keys r-fields)])
			(define r-type (hash-ref r-fields r-key)) ; list: type of the current r-key
			(define s-key (format "~a" r-key)) ; r-key is symbol, need to convert to str before use
			(define r-val (reg-make-type s-key r-type #:store #f))
			(zhash-set! root-instance s-key r-val)
		)
		(when store (register-set! g-name root-instance))
		root-instance
	)
	
	; store the constructor into the constructor dictionary
	(hash-set! struct-constructors r-name g-constructor)
	g-constructor
)
; ===================================================== ;

; =====>
; helper utilities
; =====>
; string to everything function
; (notice) aligning with Racket, if conversion fails, return #f
(define (string->? t-type t-str)
	(cond
		[(equal? t-type #\b) (cond
			[(equal? t-str "true") #t]
			[(equal? t-str "false") #f]
			[else (print-and-exit (format "# string->?: unknown boolean literal, got ~a\n" t-str))]
		)]
		[(equal? t-type #\i) 
			(if (string-prefix? t-str "0x") 
				(string->number (substring t-str 2) 16) ; hex
				(string->number t-str 10) ; dec
			)
		]
		[else (print-and-exit (format "# string->?: unsupported target type, got ~a\n" t-type))]
	)
)
; return the first n elements of a list (reverse version of list-tail)
(define (list-slice l s e)
	(for/list ([i (in-range s e)])
		(list-ref l i)
	)
)
(define (member? e l)
	(if (list? (member e l))
		#t
		#f
	)
)

; =====>
; any-?: main solver entrance
; =====>
(define (do-solve json-obj)
	; load and construct structs
	(printf "# building structs\n")
	(define json-global-structs (hash-ref json-obj `global_structs))
	(for ([d-struct json-global-structs])
		(make-struct-constructor d-struct)
	)

	; construct the global blocks
	(printf "# building global scope\n")
	(define json-global-vars (hash-ref json-obj `global_variables))
	; (define json-global-consts (hash-ref json-obj `global_constants))
	(define json-global-blocks (hash-ref json-obj `global_blocks))
	(register-set! "ANGELIC-FLAG" #f) ; add angelic field
	(printf "  > loading global blocks\n")
	(for ([d-block json-global-blocks])
		(define d-addr (hash-ref d-block `addr))
		(define d-scope (hash-ref d-block `scope))
		(define d-insts (hash-ref d-block `instructions))
		(assert (equal? d-scope "__GLOBAL__") (format "# do-solve: scope of global blocks must be __GLOBAL__, got ~a\n" d-scope))
		(define d-saddr (machine-get-saddr d-addr d-scope)) ; special address for __GLOBAL__
		(printf "    > adding global block: ~a\n" d-saddr)
		; (block-set! d-saddr d-block) ; add the whole block
		(block-set! d-saddr d-insts) ; only add the instructions
	)
	(printf "  > start adding and initializing global variables\n")
	(for ([d-var json-global-vars])
		(define d-name (hash-ref d-var `name))
		(printf "    > declaring global variable: ~a\n" d-name)
		(define d-type (hash-ref d-var `type)) ; this is also a list
		(define d-init (hash-ref d-var `init)) ; this is a list
		(reg-make-type d-name d-type #:use-default #t)
		(printf "    > initializing global variable: ~a\n" d-name)
		(for ([di d-init])
			(define d-saddr (machine-get-saddr di "__GLOBAL__"))
			(interpret-path "__GLOBAL__" null d-saddr #f) ; attack? off
			(printf "\n")
		)
	)

	(when arg-verbose (printf "  > current registers: ~a\n" register-hash))
	(when arg-verbose (printf "  > current functions: ~a\n" function-hash))
	; (printf "  > current blocks: ~a\n" block-hash)

	(when (|| (equal? arg-attack "range") (equal? arg-attack "path"))
		(printf "# building ranges\n")
		(printf "  > start adding range variables\n")
		(define json-range-vars (hash-ref json-obj `range_variables))
		(define range-entry-saddrs (list ))
		(for ([d-var json-range-vars])
			(define d-name (hash-ref d-var `name))
			(define d-addrs (hash-ref d-var `addrs))
			(define d-rads (for/list ([tmp d-addrs]) (machine-get-saddr tmp "__RANGE__")))
			(printf "    > adding: ~a -> ~a\n" d-name d-rads)
			; add the entry address
			; (notice) we don't tell apart which entry belongs to which variable here since there's no need
			(set! range-entry-saddrs (append range-entry-saddrs d-rads))
		)
		
		; remove duplicate addresses (if any)
		(set! range-entry-saddrs (set->list (list->set range-entry-saddrs)))

		; (assert (not (null? range-entry-saddrs)) (format "# do-solve: range entry address should not be empty, please at least provide one range attack entry point.\n"))
		(set! arg-range-address range-entry-saddrs) ; set the global range addresses
		(printf "  > range entry addresses: ~a\n" arg-range-address)
		(printf "  > loading range blocks\n")
		(define json-range-blocks (hash-ref json-obj `range_blocks))
		(for ([d-block json-range-blocks])
			(define d-addr (hash-ref d-block `addr))
			(define d-scope (hash-ref d-block `scope))
			(define d-insts (hash-ref d-block `instructions))
			(assert (equal? d-scope "__RANGE__") (format "# do-solve: scope of range blocks must be __RANGE__, got ~a\n" d-scope))
			(define d-saddr (machine-get-saddr d-addr d-scope)) ; special address for __RANGE__
			(printf "    > adding range block: ~a\n" d-saddr)
			(block-set! d-saddr d-insts) ; only add the instructions
		)
	)

	(when (equal? arg-attack "havoc")
		(printf "# building havoc\n")
		; havoc shares the same variables with range
		(printf "  > building havoc blocks\n")
		(define json-range-vars (hash-ref json-obj `range_variables))
		; stores the types of every declared global variable
		(define json-global-types (make-hash (for/list ([d-var json-global-vars])
			(cons (hash-ref d-var `name) (hash-ref d-var `type))
		)))
		; sync with the global hash
		(set! register-types json-global-types)
		(define havoc-tmp-insts (for/list ([j-var json-range-vars])
			(define j-name (hash-ref j-var `name))
			(define j-type (hash-ref json-global-types j-name))
			(printf "    > havoc variable detected: ~a\n" j-name)
			(if (hash-has-key? register-types j-name)
				(format "RESET ~a" j-name)
				(print-and-exit "# do-solve: havoc doesn't recognize the type of variable ~a\n" j-name)
			)
		))
		(define havoc-tmp-addr "0x00")
		(define havoc-tmp-scope "__HAVOC__")
		(define havoc-tmp-saddr (machine-get-saddr havoc-tmp-addr havoc-tmp-scope)) ; special address for __HAVOC__
		(printf "    > adding havoc block: ~a\n" havoc-tmp-saddr)
		(block-set! havoc-tmp-saddr havoc-tmp-insts) ; only add the instructions
	)

	(printf "# building normal scopes\n")
	(define json-root-addr (hash-ref json-obj `root_addr))
	(define json-dest-addrs (hash-ref json-obj `dest_addrs))
	(printf "  > root addr: ~a\n" json-root-addr)
	(printf "  > dest addrs: ~a\n" json-dest-addrs)
	(printf "  > loading normal blocks\n")
	(define json-normal-blocks (hash-ref json-obj `normal_blocks))
	(for ([d-block json-normal-blocks])
		(define d-addr (hash-ref d-block `addr))
		(define d-scope (hash-ref d-block `scope))
		(define d-insts (hash-ref d-block `instructions))
		; =========================== ;
		; ==== tod mode specific ==== ;
		; =========================== ;
		; 1. remove all ATTACK
		; 2. add an ATTACK at root
		(define tmp-insts (for/list ([ti d-insts] #:unless (equal? ti "ATTACK")) ti))
		(define tod-insts (if (equal? d-addr json-root-addr)
			(cons "ATTACK" tmp-insts)
			tmp-insts
		))

		; ================================ ;
		; ==== auto scoping extension ==== ;
		; ================================ ;
		; note/fixme: this is pretty bad practice modifying instructions from within the interpreter
		; this automatically switch the following variables with new symbolic variables
		; msg.value, block.timestamp, now
		(define scoped-insts 
			(for/fold ([tmp-list (list)]) ([tmp-elem tod-insts])
				(if (equal? tmp-elem "ATTACK")
					; yes, ATTACK, attach auto scoping
					(append tmp-list (list
						"msg_value_swap = msg.value"
						"tmp_msg_value = NEW_VAL integer"
						"msg.value = tmp_msg_value"

						"block_timestamp_swap = block.timestamp"
						"tmp_block_timestamp = NEW_VAL integer"
						"block.timestamp = tmp_block_timestamp"

						"now_swap = now"
						"tmp_now = NEW_VAL integer"
						"now = tmp_now"

						"ATTACK"

						"msg.value = msg_value_swap"
						"block.timestamp = block_timestamp_swap"
						"now = now_swap"
					))
					; else, not ATTACK, do nothing
					(append tmp-list (list tmp-elem))
				)
			)
		)

		; (printf "addr: ~a, original: ~a, tod: ~a\n" d-addr d-insts tod-insts)
		(define d-saddr (machine-get-saddr d-addr d-scope))
		(printf "    > adding normal block: ~a\n" d-saddr)
		; (block-set! d-saddr d-block) ; add the whole block
		; (block-set! d-saddr d-insts) ; only add the instructions
		; (block-set! d-saddr tod-insts) ; only add the instructions
		(block-set! d-saddr scoped-insts) ; only add the instructions
		; also add the block saddr to bec tracking
		(bec-set! d-saddr 0)
	)

	; then interpret the main body
	(printf "# start interpretation of normal blocks...\n")
	(interpret-path "" json-dest-addrs json-root-addr #t) ; empty scope, attack? on
	(printf "\n")
	(when arg-verbose (printf "# final registers: ~a\n" register-hash))
	(when arg-verbose (printf "# final functions: ~a\n" function-hash))

	(printf "# asserts size: ~a\n" (length (asserts)))
	(printf "# using solver: ~a\n" (current-solver))

	; ; then check for satisfiability ANGELIC-FLAG
	(define angelic-model (solve (assert (not (register-ref "ANGELIC-FLAG")))))
	(define is-solvable (sat? angelic-model))
	(printf "# result: ~a\n" is-solvable)
)

; =====>
; the interpreter
; =====>
; (notice) do not throw exception only in parse-code, since in branch execution Rosette supresses exceptions
;          so just directly print some info and exit so that I know there's something wrong in parser
(define parser (new solidity-parser%))
(define (parse-code inst-str)
	(define code
		(with-handlers ([
			(lambda (v) #t) 
			(lambda (v) (printf "# parser-error on ~a\n" (pretty-format inst-str)) (exit 0))])
			(send parser ir-from-string inst-str)
		)
	)
	code
)
; =====>
; machine-get-v: automatically return the corresponding value given a key or a literal value
;                if no key is found, a corresponding exception will be triggered
; r-pat: element of an op-pattern
;
; short names for type patterns: b/i/u, c/s, m, x (use the first first)
; b: boolean, i: integer, u: unknown
; c: collection, s: struct
; m: symbol (e.g., struct.symbol for doing struct field accessing), specifically, there's "rm" only
; x: could be b/i/u/c/s, lose track of types (notice: can't be m)
;
; r: register, l: literal
; =====>
(define (machine-get-v r-key r-pat)
	(define r-rl (string-ref r-pat 0)) ; r/l
	(define r-type (string-ref r-pat 1)) ; b/i/u, v/c/s, x
	(cond
		; register, r-type in r-key should match that in value (FIXME-ASSERT)
		[(equal? r-rl #\r) (begin
			(define tmp (register-ref r-key))
			(if (and (symbol? tmp) (zvoid? tmp))
				; (important) all paths are zvoid, critical syntax violation, this should stop immediately, not reporting #f
				; (print-and-exit (format "# machine-get-v: all paths are zvoid for ~a\n" (pretty-format r-key)))
				; surf/skip
				(assert #f (format "# surf/skip: all paths are zvoid for ~a\n" (pretty-format r-key)))
				tmp
			)
		)]
		[(equal? r-rl #\l) (string->? r-type r-key)] ; literal, where r-key should be of length 1 (FIXME-ASSERT)
		[else (print-and-exit (format "# machine-get-v: error parsing op-pattern, got ~a\n" r-pat))]
	)
)
(define (machine-get-saddr r-addr r-scope)
	(cond
		[(equal? r-scope "__GLOBAL__") (format "~a@~a" r-addr r-scope)]
		[(equal? r-scope "__RANGE__") (format "~a@~a" r-addr r-scope)]
		[(equal? r-scope "__HAVOC__") (format "~a@~a" r-addr r-scope)]
		[else (format "~a" r-addr)]
	)
)
(define (interpret-path i-scope i-dest-daddrs i-entry-daddr attack?)
	(when (not (zvoid? i-entry-daddr))
		(define dest? (member? i-entry-daddr i-dest-daddrs))
		(define i-insts (block-ref i-entry-daddr))
		(when arg-verbose (printf "\n>>> entering block (dest?:~a): ~a\n" (pretty-format dest?) (pretty-format i-entry-daddr)))
		(define i-next-daddr (interpret-block i-scope i-insts dest? attack?))
		; (printf "[debug]>>>>>>>>>> i-next-daddr: ~a\n" i-next-daddr)
		(when (not (zvoid? i-next-daddr))
			(interpret-path i-scope i-dest-daddrs i-next-daddr attack?)
		)
	)
)
(define (interpret-block i-scope i-insts dest? attack?)
	
	; (important) should use WHEN
	; if the current block is in the dest pool, dest? is true
	; otherwise, don't do anything
	(when dest? (register-set! "ANGELIC-FLAG" #t))

	; (printf "******debug: ~a\n" (pretty-format i-insts))

	; cool ;)
	; lifted core do-interpret procedure
	(define (do-interpret d-insts)
		(define rrret 
			(cond
				[(union? d-insts) (for/all ([dd d-insts])
					(do-interpret dd)
				)]
				[(list? d-insts) (list-ref (reverse (for/list ([dd d-insts])
					(do-interpret dd)
				)) 0)]
				[(string? d-insts) (interpret-inst i-scope (vector-ref (parse-code d-insts) 0) attack?)]
				[(zvoid? d-insts) zvoid] ; the current path is zvoid, propagate and return zvoid (this deals with nested unions of zvoid)
				[else (print-and-exit (format "# do-interpret: unsupported type to interpret, got: ~a\n" (pretty-format d-insts)))]
			)
		)
		; (printf "# [debug] >>>>rrret is: ~a\n" rrret)
		rrret
	)

	(do-interpret i-insts)

)
(define (interpret-inst i-scope i-inst attack?)
	(define i-op (inst-op i-inst))
	; secondary parsing
	(define tmp-op-list (string-split i-op "#" #:trim? #f))
	(define i-op-name (list-ref tmp-op-list 0))
	(define i-op-pattern (string-split (list-ref tmp-op-list 1) "-"))
	(define i-args (inst-args i-inst))

	; block execution count helper procedure
	; determine whether an saddr should be returned or not
	(define (bec-wrapper b-saddr)
		; (printf "# [debug] >>>>>> bec gets: ~a\n" b-saddr)
		(define bbrr 
			(if (<= arg-block-execution-bound 0)
				; no bound, just return 
				b-saddr
				; should detect bound
				(if (not (or (equal? i-scope "__GLOBAL__") (equal? i-scope "__RANGE__") (equal? i-scope "__HAVOC__")))
					; check for block execution count
					(begin
						; (printf "# [debug] >>>>>b0\n")
						(define b-scount (bec-ref b-saddr))
						; (notice) if condition is for next, which is (+ 1 b-scount)
						(if (> (+ 1 b-scount) arg-block-execution-bound)
							; reached the bound, return zvoid
							(begin
								; (printf "# [debug] >>>>b1\n")
								(when arg-verbose (printf "--- cutting block execution: ~a, reached execution bound, got: ~a\n" b-saddr b-scount))
								zvoid
							)
							; still not the bound, add one and return
							(begin
								; (printf "# [debug] >>>>b2\n")
								(bec-set! b-saddr (+ 1 b-scount))
								b-saddr
							)
						)
					)
					; not target block, just return
					b-saddr
				)
			)
		)
		; (printf "# [debug] >>>>>> bec returns: ~a\n" bbrr)
		bbrr
	)

	; syntactic sugar "U":
	; 1. U will be explained only once in the same instruction
	; 2. U will be inferred as a symbolic variable of type of its first appearance
	(define u-type null)
	(for ([k (in-range 0 (vector-length i-args))])
		#:break (not (null? u-type))
		(when (equal? (vector-ref i-args k) "U")
			(define k-type (string-ref (list-ref i-op-pattern k) 1))
			(cond
				[(equal? k-type #\i) (begin
					(reg-make-integer "U")
					(set! u-type "integer")
				)]
				[(equal? k-type #\b) (begin
					(reg-make-boolean "U")
					(set! u-type "boolean")
				)]
				[(equal? k-type #\u) (begin
					(reg-make-unknown "U")
					(set! u-type "unknown")
				)]
				[(equal? k-type #\x) (begin
					(reg-make-unknown "U")
					(set! u-type "unknown-x")
				)]
				[else (print-and-exit (format "# interpret-inst: unsupported type in pat when inferring U, got ~a\n" k-type))]
			)
		)
	)

	(when arg-verbose (printf ">>> interpreting (U=~a, scope=~a): ~a, ~a, ~a\n" u-type i-scope i-op-name i-op-pattern i-args))

	; attack operator needs a new symbolic pointer to the range block addresses every time
	; so you need the define-symbolic* 
	; range-pointer: range attack 
	(define (new-range-pointer)
		(define-symbolic* range-pointer integer?)
		range-pointer
	)
	(define (attack)
		(when attack?
			(cond
				[(equal? arg-attack "none") zvoid] ; do nothing
				[(equal? arg-attack "havoc") (begin
					(when arg-verbose (printf "||| launching havoc attacks\n"))
					(interpret-path "__HAVOC__" null (machine-get-saddr "0x00" "__HAVOC__") #f) ; attack? is off
				)]
				[(|| (equal? arg-attack "range") (equal? arg-attack "path")) (begin
					(define range-pointer (new-range-pointer)) ; this guards all possible range attacks
					(when arg-verbose (printf "||| launching range attacks: ~a\n" (pretty-format (list-ref arg-range-address range-pointer))))
					; __RANGE__ scope, null dest, all range entries
					(interpret-path "__RANGE__" null (list-ref arg-range-address range-pointer) #f) ; attack? is off
				)]
				; usually this branch won't happen since it's already checked during argument parsing
				[else (print-and-exit (format "# exit: attack type is not recognized, choose from none/havoc/range, got: ~a\n" arg-attack))]
			)
		)
		zvoid
	)

	(define (reset)
		(define reg (vector-ref i-args 0)) ; register name
		(if (hash-has-key? register-types reg)
			(reg-make-type reg (hash-ref register-types reg)) ; manually call the new type function
			(print-and-exit (format "# exit: can't find register and its type on top level, got: ~a\n" reg))
		)
		zvoid
	)

	(define (new-value)
		(define key-r (vector-ref i-args 1)) ; type
		(define key-l (vector-ref i-args 0)) ; name
		(reg-make-type key-l (list key-r))
		zvoid
	)

	(define (new-collection)
		(define key-r (vector-ref i-args 1)) ; type
		(define key-l (vector-ref i-args 0)) ; name
		(reg-make-type key-l (list "array" key-r))
		zvoid
	)

	(define (nop)
		zvoid
	)

	; this is pretty much the same as entry-point
	(define (jump)
		(define j-addr (vector-ref i-args 0))
		(bec-wrapper (machine-get-saddr j-addr i-scope))
	)

	(define (assign)
		(define key-l (vector-ref i-args 0))
		(define key-r (vector-ref i-args 1))
		(define pat-l (list-ref i-op-pattern 0))
		(define pat-r (list-ref i-op-pattern 1))

		(define val-r (machine-get-v key-r pat-r))
		(register-set! key-l val-r)
		zvoid
	)

	(define (struct-refer)
		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define key-r1 (vector-ref i-args 2)) ; key-r1 is treated as symbol/string, not key
		(define pat-l (list-ref i-op-pattern 0)) ; string / pat
		(define pat-r0 (list-ref i-op-pattern 1)) ; string / pat

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r (zhash-ref val-r0 key-r1))
		(register-set! key-l val-r)
		zvoid
	)

	(define (struct-assign)
		(define key-l0 (vector-ref i-args 0))
		(define key-l1 (vector-ref i-args 1)) ; key-l1 is treated as symbol/string, not key
		(define key-r (vector-ref i-args 2))
		(define pat-l0 (list-ref i-op-pattern 0)) ; string / pat
		(define pat-r (list-ref i-op-pattern 2)) ; string / pat

		(define val-l0 (machine-get-v key-l0 pat-l0))
		(define val-r (machine-get-v key-r pat-r))
		(zhash-set! val-l0 key-l1 val-r)
		zvoid
	)

	(define (collection-refer)
		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define key-r1 (vector-ref i-args 2))
		(define pat-l (list-ref i-op-pattern 0)) ; string / pat
		(define pat-r0 (list-ref i-op-pattern 1)) ; string / pat
		(define pat-r1 (list-ref i-op-pattern 2)) ; string / pat

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r1 (machine-get-v key-r1 pat-r1))
		; (define val-r (vector-ref val-r0 val-r1))
		; !!!!!!!! (important) enable overflow protection here !!!!!!!!
		(define val-r (vector-ref val-r0 (modulo val-r1 10)))
		(register-set! key-l val-r)
		zvoid
	)

	(define (collection-assign)
		(define key-l0 (vector-ref i-args 0))
		(define key-l1 (vector-ref i-args 1))
		(define key-r (vector-ref i-args 2))
		(define pat-l0 (list-ref i-op-pattern 0)) ; string / pat
		(define pat-l1 (list-ref i-op-pattern 1)) ; string / pat
		(define pat-r (list-ref i-op-pattern 2)) ; string / pat

		(define val-l0 (machine-get-v key-l0 pat-l0))
		(define val-l1 (machine-get-v key-l1 pat-l1))
		(define val-r (machine-get-v key-r pat-r))
		(vector-set! val-l0 val-l1 val-r)
		zvoid
	)

	(define (condition)
		(define key-r (vector-ref i-args 0))
		(define addr-t (vector-ref i-args 1))
		(define addr-f (vector-ref i-args 2))
		(define pat-r (list-ref i-op-pattern 0))

		(define val-r (machine-get-v key-r pat-r))
		(if val-r 
			(bec-wrapper (machine-get-saddr addr-t i-scope))
			(bec-wrapper (machine-get-saddr addr-f i-scope))
		)
	)

	(define (binary-op j-op)
		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define key-r1 (vector-ref i-args 2))
		(define pat-l (list-ref i-op-pattern 0)) ; string / pat
		(define pat-r0 (list-ref i-op-pattern 1)) ; string / pat
		(define pat-r1 (list-ref i-op-pattern 2)) ; string / pat

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r1 (machine-get-v key-r1 pat-r1))
		(define val-r (j-op val-r0 val-r1))
		(register-set! key-l val-r)
		zvoid
	)

	(define (bitwise-binary-op j-op)
		(define bv-size 128)

		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define key-r1 (vector-ref i-args 2))
		(define pat-l (list-ref i-op-pattern 0)) ; string / pat
		(define pat-r0 (list-ref i-op-pattern 1)) ; string / pat
		(define pat-r1 (list-ref i-op-pattern 2)) ; string / pat

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r1 (machine-get-v key-r1 pat-r1))
		(define bval-r0 (integer->bitvector val-r0 (bitvector bv-size)))
		(define bval-r1 (integer->bitvector val-r1 (bitvector bv-size)))

		(define bval-r (j-op bval-r0 bval-r1))
		(define val-r (bitvector->integer bval-r))
		(register-set! key-l val-r)
		zvoid
	)

	(define (unary-op j-op)
		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define pat-l (list-ref i-op-pattern 0))
		(define pat-r0 (list-ref i-op-pattern 1))

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r (j-op val-r0))
		(register-set! key-l val-r)
		zvoid
	)

	(define (bitwise-unary-op j-op)
		(define bv-size 128)

		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define pat-l (list-ref i-op-pattern 0))
		(define pat-r0 (list-ref i-op-pattern 1))

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define bval-r0 (integer->bitvector val-r0 (bitvector bv-size)))

		(define bval-r (j-op bval-r0))
		(define val-r (bitvector->integer bval-r))
		(register-set! key-l val-r)
		zvoid
	)

	(define (make-call)
		; (printf "args: ~a\n" i-args)
		; (printf "tail: ~a\n" (list-tail (vector->list i-args) 2))
		(define key-l (vector-ref i-args 0))
		(define j-func (hash-ref function-hash (vector-ref i-args 1)))
		(define key-tails (list-tail (vector->list i-args) 2))
		(define pat-tails (list-tail i-op-pattern 2))

		(define val-tails (for/list ([key-i key-tails] [pat-i pat-tails]) (machine-get-v key-i pat-i)))
		(define val-r (apply j-func val-tails))
		(register-set! key-l val-r)
		zvoid
	)

	(define (get-length)
		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define pat-l (list-ref i-op-pattern 0))
		(define pat-r0 (list-ref i-op-pattern 1))

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r (vector-length val-r0) )
		(register-set! key-l val-r)
		zvoid
	)

	(define (get-balance)
		(define key-l (vector-ref i-args 0))
		(define key-r0 (vector-ref i-args 1))
		(define pat-l (list-ref i-op-pattern 0))
		(define pat-r0 (list-ref i-op-pattern 1))

		(define val-r0 (machine-get-v key-r0 pat-r0))
		(define val-r (zhash-ref val-r0 "balance") )
		(register-set! key-l val-r)
		zvoid
	)

	(define (print-register)
		(printf "# print-registers: ~a\n" register-hash)
		zvoid
	)

	(define (print-pc)
		(printf "# print-pc: ~a\n" (pc))
		zvoid
	)

	(define (pause)
		(printf "# pause: ~a\n" (vector-ref i-args 0))
		(read-line)
		zvoid
	)

	(cond
		; operators for debugging
		[(equal? i-op-name "print-register") (print-register)] 
		[(equal? i-op-name "print-pc") (print-pc)] 
		[(equal? i-op-name "pause") (pause)] 

		[(equal? i-op-name "nop") (nop)]
		[(equal? i-op-name "jump") (jump)]
		[(equal? i-op-name "attack") (attack)]
		[(equal? i-op-name "reset") (reset)]
		[(equal? i-op-name "new-value") (new-value)]
		[(equal? i-op-name "new-collection") (new-collection)]
		[(equal? i-op-name "condition") (condition)]
		[(equal? i-op-name "add") (binary-op +)]
		[(equal? i-op-name "sub") (binary-op -)]
		[(equal? i-op-name "mul") (binary-op *)]
		[(equal? i-op-name "div") (binary-op /)]
		[(equal? i-op-name "pow") (binary-op expt)]
		[(equal? i-op-name "mod") (binary-op modulo)]
		; see the parser.rkt for notes about the shl/shr constructs
		[(equal? i-op-name "shl") (binary-op (lambda (x y) (assert (>= y 0)) (* x (expt 2 y)) ) )] ; x << y is x * 2**y
		[(equal? i-op-name "shr") (binary-op (lambda (x y) (assert (>= y 0)) (/ x (expt 2 y)) ) )] ; x >> y is x / 2**y
		[(equal? i-op-name "band") (bitwise-binary-op bvand)]
		[(equal? i-op-name "bior") (bitwise-binary-op bvor)]
		[(equal? i-op-name "bxor") (bitwise-binary-op bvxor)]
		[(equal? i-op-name "bneg") (bitwise-unary-op bvnot)]
		[(equal? i-op-name "neg") (unary-op not)]
		[(equal? i-op-name "and") (binary-op (lambda (x y) (and x y)))]
		[(equal? i-op-name "or") (binary-op (lambda (x y) (or x y)))]
		[(equal? i-op-name "lt") (binary-op <)]
		[(equal? i-op-name "lte") (binary-op <=)]
		[(equal? i-op-name "gt") (binary-op >)]
		[(equal? i-op-name "gte") (binary-op >=)]
		[(equal? i-op-name "eq") (binary-op equal?)]
		[(equal? i-op-name "neq") (binary-op (lambda (x y) (not (equal? x y))))]
		[(equal? i-op-name "assign") (assign)]
		[(equal? i-op-name "struct-refer") (struct-refer)]
		[(equal? i-op-name "struct-assign") (struct-assign)]
		[(equal? i-op-name "collection-refer") (collection-refer)]
		[(equal? i-op-name "collection-assign") (collection-assign)]
		[(equal? i-op-name "make-call") (make-call)]
		[(equal? i-op-name "get-length") (get-length)]
		[(equal? i-op-name "get-balance") (get-balance)]
		[else (assert #f (format "# exit: unsupported operator, got ~a\n" i-op))]
	)
)

; =====>
; parse commandline arguments
; =====>
(define arg-raw null)
(define arg-attack "none")
(define arg-solver "cvc4")
(define arg-block-execution-bound 10)
(define arg-verbose #f)
(define arg-debug #f)
(define arg-range-address null) ; "fake" arg to store global range address, set in do-solve
(command-line
	#:program "greg-surf-tod"
	#:once-any
	[("--file") p-file "input json by reading from file" 
		(begin
			(printf "# using file ~a\n" p-file)
			(set! arg-raw (file->string p-file))
		)
	]
	[("--raw") p-raw "input json by raw string" 
		(begin
			(printf "# using raw string\n")
			(set! arg-raw p-raw)
		)
	]
	#:once-each
	[("--attack") p-attack "set the attack type (none/havoc/range), default: none" 
		(cond
			[(equal? p-attack "none") (set! arg-attack "none")]
			[(equal? p-attack "havoc") (set! arg-attack "havoc")]
			[(equal? p-attack "range") (set! arg-attack "range")]
			[(equal? p-attack "path") (set! arg-attack "path")]
			[else (assert #f (format "# exit: attack type is not recognized, choose from none/havoc/range/path, got: ~a" p-attack))]
		)
	]
	[("--beb") p-beb "set the block execution bound: >=0, default: 0 (no bound)"
		(define n-beb (string->number p-beb))
		(if (and (integer? n-beb) (>= n-beb 0))
			(set! arg-block-execution-bound n-beb)
			(assert #f (format "# exit: block execution bound should be integer >= 0, got: ~a" p-beb))
		)
	]
	[("--solver") p-solver "set the backend solver used (z3/cvc4/yices), default: cvc4" 
		(cond
			[(equal? p-solver "z3") (set! arg-solver "z3")]
			[(equal? p-solver "cvc4") (set! arg-solver "cvc4")]
			[(equal? p-solver "yices") (set! arg-solver "yices")]
			[else (assert #f (format "# exit: solver is not recognized, choose from z3/cvc4/yices, got: ~a" p-solver))]
		)
	]
	[("--verbose") "whether or not to show more info" 
		(begin
			(set! arg-verbose #t)
		)
	]
	; (notice) this option is currently unavailable
	[("--debug") "whether or not to enable debug operator interpretation" 
		(begin
			(set! arg-debug #t)
		)
	]
)
(if (null? arg-raw)
	(assert #f (format "# exit: no json file/string specified\n"))
	(printf "")
)
(printf "# attack type: ~a\n" arg-attack)
(printf "# solver type: ~a\n" arg-solver)
(set-solver arg-solver) ; set the solver
(printf "# block execution bound: ~a\n" arg-block-execution-bound)
(printf "# verbose: ~a\n" arg-verbose)
(printf "# debug: ~a\n" arg-debug)

; =====>
; main entrance
; =====>
(define (pause msg)
	(printf (format "PAUSE: ~a" msg))
	(read-line)
)
; find an angelic path
(do-solve (string->jsexpr arg-raw))

