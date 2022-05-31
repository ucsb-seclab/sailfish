#lang rosette
; ==== general notice ==== ;
; zhash is a lifted symbolic hash table, there are some restrictions:
; 1. only strings, union of strings are accepted as keys
; 2. values can be arbitrary types
; 3. (internal design) zval is an alias type of integer, but is unsolvable
;    zval is only used for lifting vector-ref and vector-set! (that solves the vector redundancy issue)
; ======================== ;
; ==== develop notice ==== ;
; 1. if there are fundamental errors that violate the design, use print-and-exit
; 2. ???
; ======================== ;
(provide zhash zhash?)
(provide zhash-has-key? zhash-ref zhash-set!)
; (provide zval zval?)
(provide zvoid zvoid?)
(provide print-and-exit)

; ==== short-cuts ==== ;
; for better debugging, the helper methods are set here not inside the class
; ==================== ;
; (important) zvoid? is lifted because it's comparing values, not recognizing types (unlike string?)
; (define zvoid 'zvoid)
; (define (zvoid? obj) (equal? obj zvoid))
; (define (zval? obj) (is-a? obj zval))
; (define (zhash? obj) (is-a? obj zhash))
; (define (zhash-has-key? obj key) (send obj zhash-has-key? key))
; (define (zhash-ref obj key) (send obj zhash-ref key))
; (define (zhash-set! obj key val) (send obj zhash-set! key val))
(define zvoid 'zvoid)
(define (zvoid? obj) 
	(cond
		[(union? obj) (for/all ([pp obj]) (zvoid? pp))]
		[else (equal? obj zvoid)]
	)
)
(define (zval? obj)
	(cond
		[(union? obj) (for/all ([pp obj]) (zval? pp))]
		[else (is-a? obj zval)]
	)
)
(define (zhash? obj)
	(cond
		[(union? obj) (for/all ([pp obj]) (zhash? pp))]
		[else (is-a? obj zhash)]
	)
)
(define (zhash-has-key? obj key)
	(cond
		[(union? obj) (for/all ([pp obj]) (zhash-has-key? pp key))]
		[else (send obj zhash-has-key? key)]
	)
)
(define (zhash-ref obj key)
	(cond
		[(union? obj) (for/all ([pp obj]) (zhash-ref pp key))]
		[else (send obj zhash-ref key)]
	)
)
(define (zhash-set! obj key val)
	(cond
		[(union? obj) (for/all ([pp obj]) (zhash-set! pp key val))]
		[else (send obj zhash-set! key val)]
	)
)

; ==== helper methods ==== ;
; for better debugging, the helper methods are set here not inside the class
; ======================== ;

(define (print-and-exit msg)
	(printf msg)
	(exit 0)
)

(define (hash->ass h-table)
	(foldl 
		(λ (x result) 
			(append 
				result 
				(list (cons x (hash-ref h-table x)))
			)
		)
		`() (hash-keys h-table)
	)
)

(define (union-of-string? qk)
	(for ([tok (union-contents qk)])
		(when (not (string? (cdr tok))) #f)
	)
	#t
)

(define (ass-has-key? list key)
	(cond
		; [(and (symbol? key) (zvoid? key)) #f]
		[(string? key) (begin
			(match list
				[(list) #f]
				[(list cur rest ...)
					(if (equal? (car cur) key) #t (ass-has-key? rest key))
				]
			)
		)]
		[(union? key) (begin
			(for/all ([pp key])
				(ass-has-key? list pp)
			)
		)]
		[else #f]
	)
)

; must call ass-has-key? before calling ass-ref
(define (ass-ref list key) 
	(cond
		[(string? key) (match list
			[(list cur rest ...)
				(if (equal? (car cur) key) (cdr cur) (ass-ref rest key))
			]
			; otherwise just let it throw an error/exception, and rosette will cut this
		)]
		[(union? key) (for/all ([pp key])
			(ass-ref list pp)
		)]
		[else zvoid]
	)
)

; (define (zvector-ref svec sk)
; 	(cond
; 		; only accepts zval type as true index
; 		; this solves the vector-ref redundancy problem
; 		[(zval? sk) (vector-ref svec (send sk get-val))]
; 		[(union? sk) (for/all ([pp sk])
; 			(zvector-ref svec pp)
; 		)]
; 		[else zvoid]
; 	)
; )
(define (zvector-ref svec sk)
	(cond
		[(union? svec) (for/all ([pp svec]) (zvector-ref pp sk))]
		[else 
			(cond
				; only accepts zval type as true index
				; this solves the vector-ref redundancy problem
				[(union? sk) (for/all ([pp sk])
					(zvector-ref svec pp)
				)]
				[(zval? sk) (vector-ref svec (send sk get-val))]
				[else zvoid]
			)
		]
	)
)

; (define (zvector-set! svec sk sv)
; 	(cond
; 		; only accepts zval type as true index
; 		; this solves the vector-set! redundancy problem
; 		[(zval? sk) (vector-set! svec (send sk get-val) sv)]
; 		[(union? sk) (for/all ([pp sk])
; 			(zvector-set! svec pp sv)
; 		)]
; 		; else supress: do nothing
; 	)
; )
(define (zvector-set! svec sk sv)
	(cond
		[(union? svec) (for/all ([pp svec]) (zvector-set! pp sk sv))]
		[else
			(cond
				; only accepts zval type as true index
				; this solves the vector-set! redundancy problem
				[(union? sk) (for/all ([pp sk])
					(zvector-set! svec pp sv)
				)]
				[(zval? sk) (vector-set! svec (send sk get-val) sv)]
				; else supress: do nothing
			)
		]
	)
)

; this provides a unsolvable type for better control of construct lifting
; (notice) zval is designed to only be an unsolvable integer alias, and it doesn't support other types
(define zval
	(class* object% (printable<%>)
		(init val)
		; check for val types, currently only supports limited types
		(when (not (integer? val))
			(print-and-exit "#zval-init: val should be integer, got: ~a" (pretty-format val)))
		(when (or (term? val) (expression? val) (constant? val) (union? val))
			(print-and-exit "#zval-init: val should not be symbolic, got: ~a" (pretty-format val)))
		(super-new)
		(define ~val val)
		(define/public (get-val) ~val)

		; printable interface
		; (define/public (custom-print port quoting-depth)
		; 	(print (string->symbol (format "%zval<~a>" ~val)) port))
		; (define/public (custom-write port)
		; 	(write (string->symbol (format "%zval<~a>" ~val)) port))
		; (define/public (custom-display port)
		; 	(display (string->symbol (format "%zval<~a>" ~val)) port))
		(define/public (custom-print port quoting-depth)
			(fprintf port "#zval(~a)" ~val))
		(define/public (custom-write port)
			(fprintf port "#zval(~a)" ~val))
		(define/public (custom-display port)
			(fprintf port "#zval(~a)" ~val))
	)
)

(define zhash
	(class* object% (printable<%>)
		(init cap) ; max capacity of the internal vector storage
		(super-new) ; superclass initialization

		; ==== fields ==== ;
		(define ~cap cap)
		(define ~key-hash (make-hash)) ; key -> ind
		(define ~keys (hash->ass ~key-hash)) ; list of (key,ind)
		(define ~vals (make-vector ~cap zvoid)) ; ind -> content

		; ==== public methods ==== ;
		(define/public (get-cap) ~cap)
		; ==== only for debug ==== ;
		(define/public (get-key-hash) ~key-hash)
		(define/public (get-keys) ~keys)
		(define/public (get-vals) ~vals)

		(define/public (zhash-has-key? pk)
			(if (ass-has-key? ~keys pk)
				(if (zvoid? (zvector-ref ~vals (ass-ref ~keys pk)))
					#f
					#t
				)
				#f
			)
		)

		; (notice) behavior of zhash-ref is like a hash-ref with default value zvoid
		; 1. if pk is string and has key, return the val
		; 2. if pk is string and no key, return zvoid
		; 3. if pk is a union of strings, return val/zvoid union
		(define/public (zhash-ref pk)
			(if (zhash-has-key? pk)
				(zvector-ref ~vals (ass-ref ~keys pk))
				zvoid
			)
		)

		(define/public (zhash-add-key! pk)
			(cond
				[(string? pk) (when (not (ass-has-key? ~keys pk))
					(hash-set! ~key-hash pk (new zval [val (hash-count ~key-hash)]) ) ; update key-hash
					(set! ~keys (hash->ass ~key-hash)) ; propagate key-hash to update keys
				)]
				[(union? pk) 
					; add all potential zval keys
					(for ([u (union-contents pk)])
						(zhash-add-key! (cdr u))
					)
				]
				; else supress: do nothing
			)
		)

		(define/public (zhash-set! pk pv)
			; make sure all potential keys exist (if not, add)
			; this is not symbolic
			(zhash-add-key! pk)

			; then proceed to the set! procedure
			(define pid (ass-ref ~keys pk)) ; pid can be union of zval
			(zvector-set! ~vals pid pv) ; (notice) zvector-set! will deal with the zvoid case, don't worry ;)
		)

		; printable helper
		(define (zhash->string)
			(string-append 
				"#zhash("
				(string-join
					(filter
						(lambda (x) (> (string-length x) 0))
						(for/list ([qk ~keys])
							(format "(~a . ~a)" (pretty-format (car qk)) (pretty-format (zhash-ref (car qk))))
						)
					)
					" "
				)
				")"
			)
		)

		; printable interface
		(define/public (custom-print port quoting-depth)
			(fprintf port (zhash->string)))
		(define/public (custom-write port)
			(fprintf port (zhash->string)))
		(define/public (custom-display port)
			(fprintf port (zhash->string)))

	)
)

