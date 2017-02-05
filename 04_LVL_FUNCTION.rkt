#lang racket
(require (except-in eopl #%module-begin))
(provide (all-from-out eopl))
(define init-env 
  (lambda ()
    (extend-env 'a (num-val 10)
                (extend-env 'b (num-val 20)
                            (extend-env 'c (num-val 30)
                                        (empty-env))))))
; ENVIRONMENT
(define empty-env
  (lambda ()
    '()))

(define empty-env? 
  (lambda (x)
    (null? x)))

(define extend-env
  (lambda (sym val old-env)
    (extended-env-record sym val old-env)))

(define apply-env
  (lambda (env search-sym)
    (if (eqv? search-sym 'stop)
        (exit 1)
        (if (empty-env? env)
            (eopl:error 'apply-env "No binding for ~s" search-sym)
            (let ((sym (extended-env-record->sym env))
                  (val (extended-env-record->val env))
                  (old-env (extended-env-record->old-env env)))
              (if (eqv? search-sym sym)
                  val
                  (apply-env old-env search-sym))))
        )))

(define extended-env-record
  (lambda (sym val old-env)
    (cons (list sym val) old-env)))

(define extended-env-record->sym
  (lambda (r)
    (car (car r))))

(define extended-env-record->val
  (lambda (r) 
    (cadr (car r))))

(define extended-env-record->old-env
  (lambda (r)
    (cdr r)))

; SYNTAX AND GRAMMER
(define the-lexical-spec
  '(
    (whitespace (whitespace) skip)
    (comment ("%" (arbno(not #\newline))) skip)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    (num (digit (arbno digit)) number)
    )
  )

(define the-grammar
  '(
    (program ("begin" (separated-list expression ";") "end") a-program)
    (expression (num) lit-exp)
    (expression (identifier) var-exp)
    (expression (primitive "(" (separated-list expression ",") ")") primapp-exp)
    (expression ("dec" identifier "=" expression) dec-exp)
    (expression ("write" identifier "=" expression) write-exp)
    (expression ("assign" identifier assignment-prim expression) assign-exp) 
    (expression ("zero?" "("expression")" ) zero?-exp)
    (expression ("show" "("expression")" ) show-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("for" "(" expression ";" expression ";" expression ")" "{" (separated-list expression ";") "}") for-exp)
    (expression ("while" "(" expression ")" "{" (separated-list expression ";") "}") while-exp)
    (expression ("(" "code" num ")") code-exp)
    (expression ("function" "(" (separated-list identifier ",") ")" "{" (separated-list expression ";") "}") func-expr)
    (expression ("call" expression "(" (separated-list expression ",") ")") call-expr)

    
    ; Math Primitive
    (primitive ("+") add-prim)
    (primitive ("-") sub-prim)
    (primitive ("*") mult-prim)
    (primitive ("/") div-prim)
    (primitive ("mod") mod-prim)
    (primitive ("++") incr-prim)
    (primitive ("--") decr-prim)

    ; Logical Primitives
    (primitive ("==") comp-equals)
    (primitive (">") comp-greater)
    (primitive ("<") comp-less)
    (primitive (">=") comp-greatEq)
    (primitive ("<=") comp-lessEq)
    (primitive ("||") comp-or)
    (primitive ("&&") comp-and)
    (primitive ("!") comp-not)

    ; TODO: Assignment Primitive
    (assignment-prim ("+=") plus-equals)
    (assignment-prim ("-=") sub-equals)
    (assignment-prim ("*=") mult-equals)
    (assignment-prim ("/=") div-equals)
    (assignment-prim ("mod=") mod-equals)
    )
  )

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val  (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?)))

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

(define-datatype proc proc?
  (procedure
   (var (list-of symbol?))
   (body (list-of expression?))
   (env environment?)))

(define environment?
  (lambda (x)
    #t))

; BIOLERPLATE
(sllgen:make-define-datatypes the-lexical-spec the-grammar)
(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))
(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))
(define run
  (lambda(str)
    (eval-program (scan&parse str) (init-env))))

; INTERPRETER
(define eval-program
  (lambda(pgm env)
    (cases program pgm
      (a-program (body) (control-program body env)))
    ))
(define control-program
  (lambda (body env)
    (if(null? body)
       (display "\n")
       (let ((new-env (eval-exp (car body) env)))
         (display "\n")
         (control-program (cdr body) new-env)
         )
       )
    )
  )
(define eval-exp
  (lambda (exp env)
    (cases expression exp
      (lit-exp (num) (num-val num))
      (var-exp (id) (apply-env env id))
      (primapp-exp (prim rands)
                   (let ((args (eval-rands rands env)))
                     (apply-primitive prim args)))
      (if-exp (test-exp true-exp false-exp)
              (if (eqv? (expval->bool (eval-exp test-exp env)) #t)
                  (eval-exp true-exp env)
                  (eval-exp false-exp env))
              )
      
      (zero?-exp (expr)
                 (let ((val (eval-exp expr env)))
                   (if (zero? (expval->num val)) (bool-val #t) (bool-val #f)))
                 )
      
      (dec-exp (id expr)
               (let ((val (eval-exp expr env)))
                 (extend-env id val env)
                 )
               )
      (write-exp (id expr)
                 (let ((pos (find-element-pos id env 0)))
                   (if (eqv? pos "ERROR")
                       (eopl:error "No binding for ~s" id)
                       (let ((left (left-sub-list env '() pos))
                             (right (right-sub-list env '() pos)))
                         (let ((val (eval-exp expr env)))
                           (append left (list (list id  val)) right) ; returns a new environment
                           )
                         )
                       )
                   )
                 )
      
      (assign-exp (id assign-prim expr)
                  (let ((val (eval-exp expr env)))
                    (let ((pos (find-element-pos id env 0)))
                      (let ((res (apply-assign-primitive assign-prim val (apply-env env id))))
                        (if (eqv? pos "ERROR")
                            (eopl:error "No binding for ~s" id)
                            (append
                             (left-sub-list env '() pos)
                             (list (list id res))
                             (right-sub-list env '() pos)
                             )
                            )
                        )
                      )
                    )
                  )
      
      (show-exp (id)
                (let ((val (eval-exp id env)))
                  (print val)
                  (display "\n")
                  env
                  )
                )
      
      (for-exp (init-exp1 comp-exp2 prim-exp3 body)
               (let ((new-env1 (eval-exp init-exp1 env)))
                 (let ((new-env2 (for-looper (car(car new-env1)) comp-exp2 prim-exp3 body new-env1))) 
                   new-env2
                   )
                 )
               )
      (while-exp (cond-exp lo-exp)
                 (while-looper cond-exp lo-exp env)
                 )
      
      (code-exp (num)
                (if (eqv? num 1)
                    env
                    (if (eqv? num 0)
                        (append (list(list 'break (num-val -1))) env)
                        (eopl:error "Unknow program code ~c" num)
                        )
                    )
                )
      (func-expr (lo-arg lo-exp)
                 (proc-val (procedure lo-arg lo-exp env))
                 )
      (call-expr (fname lo-rands)
                 (let ((proc1 (expval->proc (eval-exp fname env)))
                       (list-args (value-of-rands lo-rands env)))
                   (apply-procedure proc1 list-args)
                   )
                 )
      )
    )
  )
(define value-of-rands
  (lambda (rands env)
    (map (lambda(x) (eval-exp x env)) rands)
    )
  )

(define apply-procedure
  (lambda (proc1 list-args)
    (cases proc proc1
      (procedure (list-var body saved-env)
                 (if (not (eqv? (length list-args) (length list-var)))
                     (eopl:error 'apply-procedure "Wrong count of arguments")
                     (let ((new-env (create-new-env list-var list-args saved-env)))
                       (eval-body body new-env new-env)
                       )
                     )
                 )
      )
    )
  )
(define create-new-env
  (lambda(var val env)
    (if (null? var)
        env
        (create-new-env (cdr var) (cdr val) (append (list (list (car var) (car val))) env))
        )
    )
  )
(define for-looper
  (lambda(id comp-exp prim-exp body env)
    (let ((cond-val (eval-exp comp-exp env)))
      (if(eqv? (expval->bool cond-val) #f)
         env
         (let ((new-id-val (eval-exp prim-exp env)))
           (let ((new-env-val (eval-body body (append (list(list id new-id-val)) (cdr env)) (cdr env))))
             (if (eqv? (car (car new-env-val)) 'break)
                 (cdr new-env-val)
                 (for-looper id comp-exp prim-exp body new-env-val)
                 )
             )
           )
         )
      )
    )
  )
(define while-looper
  (lambda (cond body env)
    (if(eqv? (expval->bool (eval-exp cond env)) #f)
       env
       (let ((new-env (eval-body body env env)))
         (if (eqv? (car (car new-env)) 'break)
             (cdr new-env)
             (while-looper cond body new-env)
             )
         )
       )
    )
  )

(define eval-body
  (lambda (body env old-env)
    (if (or (null? body) (eqv? (car (car env)) 'break))
        env
        (eval-body (cdr body) (eval-exp (car body) env) old-env)
        )
    )
  )

(define find-element-pos
  (lambda(id env pos)
    (if (null? env)
        "ERROR"
        (if (eqv? (car (car env)) id) (+ pos 1)
            (find-element-pos id (cdr env) (+ pos 1))
            )
        )
    )
  )
(define left-sub-list
  (lambda(lst new-lst cnt)
    (if(= 1 cnt) new-lst
       (left-sub-list (cdr lst) (append new-lst (list (car lst))) (- cnt 1))
       )
    )
  )
(define right-sub-list
  (lambda(lst new-lst cnt)
    (if(zero? cnt) new-lst
       (right-sub-list (cdr lst) (cdr lst) (- cnt 1))
       )
    )
  )
(define apply-primitive
  (lambda (prim args)
    (cases primitive prim
      (add-prim  () (num-val (+ (expval->num (car args)) (expval->num (cadr args))) ))
      (sub-prim () (num-val (- (expval->num (car args)) (expval->num (cadr args))) ))
      (mult-prim  () (num-val (* (expval->num (car args)) (expval->num (cadr args))) ))
      (div-prim ()
                (if (zero? (expval->num (cadr args)))
                    (eopl:error 'apply-primitive "divide by zero error")
                    (num-val (/ (expval->num (car args)) (expval->num (cadr args))))
                    )
                )
      (mod-prim ()
                (if (zero? (expval->num (cadr args)))
                    (eopl:error 'apply-primitive "modulo by zero error")
                    (num-val (remainder (expval->num (car args)) (expval->num (cadr args))))
                    ))
      (incr-prim  () (num-val (+ (expval->num (car args)) 1) ))
      (decr-prim  () (num-val (- (expval->num (car args)) 1) ))
      (comp-equals () (if(eqv? (expval->num (car args)) (expval->num (cadr args))) (bool-val #t) (bool-val #f)))
      (comp-greater () (if(> (expval->num (car args)) (expval->num (cadr args))) (bool-val #t) (bool-val #f)))
      (comp-less () (if(< (expval->num (car args)) (expval->num (cadr args))) (bool-val #t) (bool-val #f)))
      (comp-greatEq () (if(>= (expval->num (car args)) (expval->num (cadr args))) (bool-val #t) (bool-val #f)))
      (comp-lessEq () (if(<= (expval->num (car args)) (expval->num (cadr args))) (bool-val #t) (bool-val #f)))
      (comp-or ()
               (if(or (eqv? (expval->bool (car args)) #t) (eqv? (expval->bool (cadr args)) #t)) (bool-val #t) (bool-val #f))) 
      (comp-and ()
                (if(and (eqv? (expval->bool (car args)) #t) (eqv? (expval->bool (cadr args)) #t)) (bool-val #t) (bool-val #f))) 
      (comp-not ()
                (if(eqv? (expval->bool (car args)) #t) (bool-val #f) (bool-val #t))) 
      )
    )
  )

(define apply-assign-primitive
  (lambda (assign-prim args id-val)
    (cases assignment-prim assign-prim
      (plus-equals () (num-val (+ (expval->num id-val) (expval->num args))))
      (sub-equals () (num-val (- (expval->num id-val) (expval->num args))))
      (mult-equals () (num-val (* (expval->num id-val) (expval->num args))))
      (div-equals () (num-val (/ (expval->num id-val) (expval->num args))))
      (mod-equals () (num-val (remainder (expval->num id-val) (expval->num args))))
      )
    )
  )
(define eval-rands
  (lambda(rands env)
    (map (lambda(x) (eval-rand x env)) rands)
    ))
(define eval-rand
  (lambda(rand env)
    (eval-exp rand env)
    ))


