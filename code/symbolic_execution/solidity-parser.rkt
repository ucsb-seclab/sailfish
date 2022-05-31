#lang racket

(require parser-tools/lex (prefix-in re- parser-tools/lex-sre) parser-tools/yacc "parser.rkt" "inst.rkt")
(provide solidity-parser%)

;; This is a Racket Lex Yacc parser.
;; Refer to the follow resources to complete this file.
;; - Lexer:   http://docs.racket-lang.org/parser-tools/Lexers.html
;; - Parser:  http://docs.racket-lang.org/parser-tools/LALR_1__Parsers.html
;; - Example: https://gist.github.com/danking/1068185
(define solidity-parser%
	(class parser%
		(super-new)
		(inherit-field asm-parser asm-lexer)
		(init-field [compress? #f])
		
		(define-tokens a (VAR WORD NUM REG BOOL)) ;; add more tokens
		(define-empty-tokens b (
			EOF ASSIGN EQ NEQ CONDITION NOP LBRACKET RBRACKET JUMP NEW-COL NEW-VAL ATTACK
			LT LTE GT GTE ADD SUB MUL DIV MOD NEG AND OR POW
			ACCESS RESET
			CALL1 CALL2 CALL3 CALL4 CALL5
			LENGTH BALANCE
			BAND BIOR BXOR BNEG SHL SHR
			; operator for debugging
			PRINT-REGISTER PRINT-PC PAUSE
		)) ;; add more tokens

		(define-lex-abbrevs
			(digit10 (char-range "0" "9"))
			(number10 (number digit10))
			(snumber10 (re-or number10 (re-seq "-" number10))) ; WATCH: fix and watch

			(number16 (re-or (char-range "0" "9") (char-range "a" "f")))
			(snumber16 (re-+ "0x" number16))

			; extended address representation, this can't be converted to number
			(number00 (re-or (char-range "0" "9") (char-range "A" "Z") (char-range "a" "z") "_"))
			(snumber00 (re-+ "0x" number00))

			(boolean2 (union "false" "true"))

			; (notice) also includes "." in the identifier
			; (identifier-characters (re-or (char-range "A" "Z") (char-range "a" "z") "_" ".")) 
			(identifier-characters (re-or (char-range "A" "Z") (char-range "a" "z") "_")) 

			(identifier (re-seq identifier-characters (re-* (re-or identifier-characters digit10))))
		)

		;; Complete lexer
		(set! asm-lexer
			(lexer-src-pos
				; operators for debugging
				("PRINT_REGISTER"	(token-PRINT-REGISTER))
				("PRINT_PC"			(token-PRINT-PC))
				("PAUSE"			(token-PAUSE))

				; (important) this is order-sensitive
				("["				(token-LBRACKET))
				("]"				(token-RBRACKET))

				("="				(token-ASSIGN))

				; ("CLEAR_SCOPE"		(token-CLEAR-SCOPE))
				("CONDITION"		(token-CONDITION))
				("NOP"				(token-NOP))
				("JUMP"				(token-JUMP))
				("ATTACK"			(token-ATTACK))
				("NEW_VAL"			(token-NEW-VAL))
				("NEW_COL"			(token-NEW-COL))
				("RESET"			(token-RESET))
				("CALL1"			(token-CALL1))
				("CALL2"			(token-CALL2))
				("CALL3"			(token-CALL3))
				("CALL4"			(token-CALL4))
				("CALL5"			(token-CALL5))

				; special operator
				("LENGTH"			(token-LENGTH))
				("BALANCE"			(token-BALANCE))

				("."				(token-ACCESS))

				; debug related operator
				; ("PROBE"			(token-PROBE))
				; ("PAUSE"			(token-PAUSE))

				("**"				(token-POW))
				("+"				(token-ADD))
				("-"				(token-SUB))
				("*"				(token-MUL))
				("/"				(token-DIV))
				("%"				(token-MOD))
				("<<"				(token-SHL))
				(">>"				(token-SHR))

				; bitwise operations
				("&"				(token-BAND))
				("|"				(token-BIOR))
				("^"				(token-BXOR))
				("~"				(token-BNEG))

				; unary op
				("!"				(token-NEG))

				("&&"				(token-AND))
				("||"				(token-OR))

				("<"				(token-LT))
				("<="				(token-LTE))
				(">"				(token-GT))
				(">="				(token-GTE))
				("=="				(token-EQ))
				("!="				(token-NEQ))
				(boolean2			(token-BOOL lexeme)) ; (important) this should be before identifier


				(identifier			(token-REG lexeme))
				(snumber10			(token-NUM lexeme))
				(snumber16			(token-NUM lexeme))
				(snumber00			(token-NUM lexeme)) ; extended address representation, this can't be converted to number
				(identifier			(token-WORD lexeme))
				(identifier			(token-VAR lexeme))
				(whitespace			(position-token-token (asm-lexer input-port)))
				((eof)				(token-EOF))
			)
		)

		;; Complete parser
		(set! asm-parser
			(parser
			 (start program)
			 (end EOF)
			 (error
				(lambda (tok-ok? tok-name tok-value start-pos end-pos)
					(raise-syntax-error 'parser
															(format "syntax error at '~a' in src l:~a c:~a"
																			tok-name
																			(position-line start-pos)
																			(position-col start-pos)))))
			 (tokens a b)
			 (src-pos)
			 (grammar

				; ? ;; add more grammar rules
				;;; (arg  ((REG) $1)
				;;;       ((NUM) $1))

				;;; (args ((arg) (list $1))
				;;;       ((arg args) (cons $1 $2))
				;;;       ((arg COMMA args) (cons $1 $3)))
				(instruction
					;;; ((NUM COLON WORD args)    (inst $3 (list->vector $4)))
					;;; when parsing ?, return (inst #f #f) as an unknown instruction
					;;; (a place holder for synthesis)
					;;; ((HOLE)         (inst #f #f))

					; operators for debugging
					( (PRINT-REGISTER) (inst "print-register#" (vector ) ) )
					( (PRINT-PC) (inst "print-pc#" (vector ) ) )
					( (PAUSE REG) (inst "pause#" (vector $2) ) )

					( (CONDITION REG NUM NUM) (inst "condition#rb" (vector $2 $3 $4 ) ) )
					( (CONDITION BOOL NUM NUM) (inst "condition#lb" (vector $2 $3 $4 ) ) )

					( (NOP) (inst "nop#" (vector ) ) )
					( (JUMP NUM) (inst "jump#" (vector $2) ) )
					( (ATTACK) (inst "attack#" (vector ) ) )
					( (RESET REG) (inst "reset#" (vector $2) ) )

					; here the last REG is interpreted as type
					( (REG ASSIGN NEW-COL REG) (inst "new-collection#rc-rm" (vector $1 $4 ) ) )
					( (REG ASSIGN NEW-VAL REG) (inst "new-value#ru-rm" (vector $1 $4 ) ) )

					( (REG ASSIGN REG ADD REG) (inst "add#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG ADD NUM) (inst "add#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM ADD REG) (inst "add#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM ADD NUM) (inst "add#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG SUB REG) (inst "sub#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG SUB NUM) (inst "sub#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM SUB REG) (inst "sub#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM SUB NUM) (inst "sub#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG MUL REG) (inst "mul#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG MUL NUM) (inst "mul#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM MUL REG) (inst "mul#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM MUL NUM) (inst "mul#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG DIV REG) (inst "div#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG DIV NUM) (inst "div#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM DIV REG) (inst "div#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM DIV NUM) (inst "div#ri-li-li" (vector $1 $3 $5 ) ) )

					; expt doesn't support (expt ?? symbolic), it's equiv. to a loop without upper bound
					; in which case there will be contract violation
					; see https://github.com/emina/rosette/issues/116
					( (REG ASSIGN REG POW REG) (inst "pow#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG POW NUM) (inst "pow#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM POW REG) (inst "pow#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM POW NUM) (inst "pow#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG MOD REG) (inst "mod#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG MOD NUM) (inst "mod#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM MOD REG) (inst "mod#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM MOD NUM) (inst "mod#ri-li-li" (vector $1 $3 $5 ) ) )

					; x SHL/SHR y
					; shift doesn't support symbolic variable for the y arg
					; it's the same reason with expt case
					; we don't disable here since REG can store a concrete value
					; but once you see contract violation, it's due to expt
					( (REG ASSIGN REG SHL REG) (inst "shl#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG SHL NUM) (inst "shl#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM SHL REG) (inst "shl#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM SHL NUM) (inst "shl#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG SHR REG) (inst "shr#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG SHR NUM) (inst "shr#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM SHR REG) (inst "shr#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM SHR NUM) (inst "shr#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG BAND REG) (inst "band#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG BAND NUM) (inst "band#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM BAND REG) (inst "band#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM BAND NUM) (inst "band#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG BIOR REG) (inst "bior#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG BIOR NUM) (inst "bior#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM BIOR REG) (inst "bior#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM BIOR NUM) (inst "bior#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG BXOR REG) (inst "bxor#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG BXOR NUM) (inst "bxor#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM BXOR REG) (inst "bxor#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM BXOR NUM) (inst "bxor#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN BNEG REG) (inst "neg#ri-ri" (vector $1 $4 ) ) ) ; i
					( (REG ASSIGN BNEG NUM) (inst "neg#ri-li" (vector $1 $4 ) ) ) ; i

					( (REG ASSIGN REG LT REG) (inst "lt#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG LT NUM) (inst "lt#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM LT REG) (inst "lt#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM LT NUM) (inst "lt#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG LTE REG) (inst "lte#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG LTE NUM) (inst "lte#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM LTE REG) (inst "lte#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM LTE NUM) (inst "lte#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG GT REG) (inst "gt#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG GT NUM) (inst "gt#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM GT REG) (inst "gt#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM GT NUM) (inst "gt#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG GTE REG) (inst "gte#ri-ri-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN REG GTE NUM) (inst "gte#ri-ri-li" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM GTE REG) (inst "gte#ri-li-ri" (vector $1 $3 $5 ) ) )
					( (REG ASSIGN NUM GTE NUM) (inst "gte#ri-li-li" (vector $1 $3 $5 ) ) )

					( (REG ASSIGN REG EQ REG) (inst "eq#ru-ru-ru" (vector $1 $3 $5 ) ) ) ; u
					( (REG ASSIGN REG EQ NUM) (inst "eq#ri-ri-li" (vector $1 $3 $5 ) ) ) ; i
					( (REG ASSIGN NUM EQ REG) (inst "eq#ri-li-ri" (vector $1 $3 $5 ) ) ) ; i
					( (REG ASSIGN NUM EQ NUM) (inst "eq#ri-li-li" (vector $1 $3 $5 ) ) ) ; i
					( (REG ASSIGN REG EQ BOOL) (inst "eq#rb-rb-lb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL EQ REG) (inst "eq#rb-lb-rb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL EQ BOOL) (inst "eq#rb-lb-lb" (vector $1 $3 $5 ) ) ) ; b

					( (REG ASSIGN REG NEQ REG) (inst "neq#ru-ru-ru" (vector $1 $3 $5 ) ) ) ; u
					( (REG ASSIGN REG NEQ NUM) (inst "neq#ri-ri-li" (vector $1 $3 $5 ) ) ) ; i
					( (REG ASSIGN NUM NEQ REG) (inst "neq#ri-li-ri" (vector $1 $3 $5 ) ) ) ; i
					( (REG ASSIGN NUM NEQ NUM) (inst "neq#ri-li-li" (vector $1 $3 $5 ) ) ) ; i
					( (REG ASSIGN REG NEQ BOOL) (inst "neq#rb-rb-lb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL NEQ REG) (inst "neq#rb-lb-rb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL NEQ BOOL) (inst "neq#rb-lb-lb" (vector $1 $3 $5 ) ) ) ; b

					( (REG ASSIGN NEG REG) (inst "neg#rb-rb" (vector $1 $4 ) ) ) ; b
					( (REG ASSIGN NEG BOOL) (inst "neg#rb-lb" (vector $1 $4 ) ) ) ; b

					( (REG ASSIGN LENGTH REG) (inst "get-length#ri-rc" (vector $1 $4 ) ) ) ; ri = LENGTH rc
					( (REG ASSIGN BALANCE REG) (inst "get-balance#ri-rs" (vector $1 $4 ) ) ) ; ri = BALANCE rs

					( (REG ASSIGN REG AND REG) (inst "and#ru-ru-ru" (vector $1 $3 $5 ) ) ) ; u
					( (REG ASSIGN REG AND BOOL) (inst "and#rb-rb-lb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL AND REG) (inst "and#rb-lb-rb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL AND BOOL) (inst "and#rb-lb-lb" (vector $1 $3 $5 ) ) ) ; b

					( (REG ASSIGN REG OR REG) (inst "or#ru-ru-ru" (vector $1 $3 $5 ) ) ) ; u
					( (REG ASSIGN REG OR BOOL) (inst "or#rb-rb-lb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL OR REG) (inst "or#rb-lb-rb" (vector $1 $3 $5 ) ) ) ; b
					( (REG ASSIGN BOOL OR BOOL) (inst "or#rb-lb-lb" (vector $1 $3 $5 ) ) ) ; b
					
					; struct series
					( (REG ASSIGN REG ACCESS REG) (inst "struct-refer#rx-rs-rm" (vector $1 $3 $5) ) ) ; rx = rs.rm
					( (REG ACCESS REG ASSIGN REG) (inst "struct-assign#rs-rm-rx" (vector $1 $3 $5) ) ) ; rs.rm = rx
					( (REG ACCESS REG ASSIGN NUM) (inst "struct-assign#rs-rm-li" (vector $1 $3 $5) ) ) ; rs.rm = li
					( (REG ACCESS REG ASSIGN BOOL) (inst "struct-assign#rs-rm-lb" (vector $1 $3 $5) ) ) ; rs.rm = lb
					; special
					; ( (REG ACCESS REG ASSIGN NEW-COL REG) (inst "struct-new-collection#rs-rm-rm" (vector $1 $3 $6) ) ) ; rs.rm = NEW-COL rm
					; ( (REG ACCESS REG ASSIGN NEW-VAL REG) (inst "struct-new-value#rs-rm-rm" (vector $1 $3 $6) ) ) ; rs.rm = NEW-VAL rm

					; normal identifiers
					( (REG ASSIGN REG) (inst "assign#ru-ru" (vector $1 $3 ) ) )
					( (REG ASSIGN BOOL) (inst "assign#rb-lb" (vector $1 $3 ) ) )
					( (REG ASSIGN NUM) (inst "assign#ri-li" (vector $1 $3 ) ) )

					; array series
					( (REG ASSIGN REG LBRACKET REG RBRACKET) (inst "collection-refer#rx-rc-ri" (vector $1 $3 $5 ) ) ) ; rx = rc[ri]
					( (REG ASSIGN REG LBRACKET NUM RBRACKET) (inst "collection-refer#rx-rc-li" (vector $1 $3 $5 ) ) ) ; rx = rc[li]
					; ---
					( (REG LBRACKET REG RBRACKET ASSIGN REG) (inst "collection-assign#rc-ri-rx" (vector $1 $3 $6 ) ) ) ; rc[ri] = rx
					( (REG LBRACKET REG RBRACKET ASSIGN NUM) (inst "collection-assign#rc-ri-li" (vector $1 $3 $6 ) ) ) ; rc[ri] = li
					( (REG LBRACKET REG RBRACKET ASSIGN BOOL) (inst "collection-assign#rc-ri-lb" (vector $1 $3 $6 ) ) ) ; rc[ri] = lb
					( (REG LBRACKET NUM RBRACKET ASSIGN REG) (inst "collection-assign#rc-li-rx" (vector $1 $3 $6 ) ) ) ; rc[li] = rx
					( (REG LBRACKET NUM RBRACKET ASSIGN NUM) (inst "collection-assign#rc-li-li" (vector $1 $3 $6 ) ) ) ; rc[li] = li
					( (REG LBRACKET NUM RBRACKET ASSIGN BOOL) (inst "collection-assign#rc-li-lb" (vector $1 $3 $6 ) ) ) ; rc[li] = lb
					; special
					; ( (REG LBRACKET REG RBRACKET ASSIGN NEW-COL REG) (inst "collection-new-collection#rc-ri-rm" (vector $1 $3 $6 ) ) ) ; rc[ri] = NEW-COL rm
					; ( (REG LBRACKET REG RBRACKET ASSIGN NEW-VAL REG) (inst "collection-new-value#rc-ri-rm" (vector $1 $3 $6 ) ) ) ; rc[ri] = NEW-VAL rm
					; ( (REG LBRACKET NUM RBRACKET ASSIGN NEW-COL REG) (inst "collection-new-collection#rc-li-rm" (vector $1 $3 $6 ) ) ) ; rc[li] = NEW-COL rm
					; ( (REG LBRACKET NUM RBRACKET ASSIGN NEW-VAL REG) (inst "collection-new-value#rc-li-rm" (vector $1 $3 $6 ) ) ) ; rc[li] = NEW-VAL rm

					; uninterpreted function series
					( (REG ASSIGN CALL1 REG REG) (inst "make-call#ri-rm-ri" (vector $1 $4 $5) ) ) ; ri = CALL1 rm ri
					( (REG ASSIGN CALL1 REG NUM) (inst "make-call#ri-rm-ri" (vector $1 $4 $5) ) ) ; ri = CALL1 rm li

					( (REG ASSIGN CALL2 REG REG REG) (inst "make-call#ri-rm-ri-ri" (vector $1 $4 $5 $6) ) ) ; ri = CALL1 rm ri ri
					( (REG ASSIGN CALL3 REG REG REG REG) (inst "make-call#ri-rm-ri-ri-ri" (vector $1 $4 $5 $6 $7) ) ) ; ri = CALL1 rm ri ri ri
					( (REG ASSIGN CALL4 REG REG REG REG REG) (inst "make-call#ri-rm-ri-ri-ri-ri" (vector $1 $4 $5 $6 $7 $8) ) ) ; ri = CALL1 rm ri ri ri ri
					( (REG ASSIGN CALL5 REG REG REG REG REG REG) (inst "make-call#ri-rm-ri-ri-ri-ri-ri" (vector $1 $4 $5 $6 $7 $8 $9) ) ) ; ri = CALL1 rm ri ri ri ri ri
				 ) 
				
				(code   
				 (() (list))
				 ((instruction code) (cons $1 $2)))

				(program
				 ((code) (list->vector $1)))
			 )))

		))

