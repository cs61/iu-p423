#lang racket
(require racket/fixnum)
(require racket/format)
(require "interp.rkt")
(require "utilities.rkt")

;; This exports r0-passes, defined below, to users of this file.
(provide r1-passes)

(define new-id
  (let ([idx 0])
    (lambda(pfix)
      (set! idx (+ idx 1))
      (string->symbol (~a pfix "." idx)))))

(define (uniquify alist)
  (lambda (e)
    (match e
      [(? symbol?) (lookup e alist)]
      [(? integer?) e]
      [`(let ([,x ,e]) ,body)
       (let* ([id (new-id x)]
              [new-alist (cons `(,x . ,id) alist)])
         `(let ([,id ,((uniquify new-alist) e)])
            ,((uniquify new-alist) body)))]
      [`(program ,e)
       `(program ,((uniquify alist) e))]
      [`(,op ,es ...)
       `(,op ,@(map (uniquify alist) es))]
      )))

(define (flatten e)
  (define (flatten1 is-let e)
    (match e
      [(? symbol?) (values e '() '())]
      [(? integer?) (values e '() '())]
      [`(let ([,x ,e]) ,body)
       (let-values ([(r1 sl1 vl1) (flatten1 #t e)]
                    [(r2 sl2 vl2) (flatten1 #f body)])
         (values r2
                 (append sl1 (cons `(assign ,x ,r1) sl2))
                 (append vl1 (cons x vl2))))]
      [`(program ,e)
       (let-values ([(r sl vl) (flatten1 #f e)])
         (values r sl vl))]
      [`(read) (if is-let
                   (values '(read) '() '())
                   (let ([id (new-id 'x)])
                     (values id `((assign ,id (read))) `(,id))))]
      [`(,op ,es)
       (let-values ([(r sl vl) (flatten1 #f es)])
         (if is-let
             (values `(,op ,r)
                     sl
                     vl)
             (let ([id (new-id 'x)])
               (values id
                       `(,@sl (assign ,id (,op ,r)))
                       (cons id vl)))))]
      [`(,op ,e1 ,e2)
       (let-values ([(r1 sl1 vl1) (flatten1 #f e1)]
                    [(r2 sl2 vl2) (flatten1 #f e2)])
         (if is-let
             (values `(,op ,r1 ,r2)
                     `(,@sl1 ,@sl2)
                     `(,@vl1 ,@vl2))
             (let ([id (new-id 'x)])
               (values id
                       `(,@sl1 ,@sl2 (assign ,id (,op ,r1 ,r2)))
                       `(,@vl1 ,@vl2 ,id)))))
       ]))
  (let-values ([(r sl vl) (flatten1 #f e)])
    (let ([sl1 `(,@sl (return ,r))])
      `(program ,vl ,@sl1))))

;; (flatten '(program 42))
;; (flatten '(let ([a 42]) (let ([b a]) b)))
;; (flatten '(program (+ (- (read)) (read))))
;; (flatten '(program (+ 52 (- 10))))
;; (flatten '(+ 52 (- 10)))
;; (flatten '(- 10))
;; (flatten '(let ([x (+ (- 10) 11)]) (+ x 41)))

(define op-instr-table
  '((+ addq)
    (- subq)))

(define (select-instr e)
  (letrec ([get-op
            (lambda(op)
              (cond
                [(assoc op op-instr-table) => cadr]
                [else #f]))]
           [atom-instr
            (lambda(ee)
              (match ee
                [(? symbol?) `(var ,ee)]
                [(? integer?) `(int ,ee)]
                ))])
    (match e
      [`(assign ,v ,ee)
       (match ee
         [(? integer?)
          `((movq (int ,ee) (var ,v)))]
         [(? symbol?)
          `((movq (var ,ee) (var ,v)))]
         [`(,op ,e1 ,e2)
          (let ([av1 (atom-instr e1)]
                [av2 (atom-instr e2)])
            (cond
              [(eq? (cadr av2) v) `((,(get-op op) ,av1 ,(atom-instr v)))]
              [(eq? (cadr av1) v) `((,(get-op op) ,av2 ,(atom-instr v)))]
              [else `((movq ,av1 ,(atom-instr v))
                      (,(get-op op) ,av2 ,(atom-instr v)))]))
          ]
         [`(read)
          `((callq read_int)
            (movq (reg rax) ,(atom-instr v)))]
         [`(- ,e1)
          (let ([av (atom-instr e1)])
            (if (eq? v (cadr av))
                `((negq ,(atom-instr v)))
                `((movq ,av ,(atom-instr v))
                  (negq ,(atom-instr v)))))
          ])]
      [`(return ,v)
       `((movq ,(atom-instr v) (reg rax)))]
      [`(program ,vl ,sl ...)
       (let ([ls (map select-instr sl)])
         `(program (,(* (length vl) 8)) ,@(foldr append '() ls)))]))
  )

;; (select-instr '(program (x)
;;                         (assign x (+ 10 32))
;;                         (assign x (+ 10 x))))
(define (assign-homes e)
  (letrec ([mem-idx 0]
           [env '()]
           [var->stack
            (lambda(ee)
              (cond
                [(and (pair? ee) (eq? (car ee) 'var))
                 (cond
                   [(assq (cadr ee) env) =>
                    (lambda(entry)
                      `(deref rbp ,(cadr entry))
                      )]
                   [else
                    (set! mem-idx (- mem-idx 8))
                    (set! env (cons `(,(cadr ee) ,mem-idx) env))
                    `(deref rbp ,mem-idx)
                    ])
                 ]
                [else ee]))]
           [inner
            (lambda(ee)
              (match ee
                [`(program ,size ,instrs ...)
                 `(program ,size ,@(map inner instrs))]
                [`(,op ,es ...)
                 `(,op ,@(map var->stack es))]
                ))])
    (inner e)))

(define (patch-instr e)
  (match e
    [`(program ,size ,instrs ...)
     (let* ([patched (map patch-instr instrs)]
            [lst (foldr append '() patched)])
       `(program ,size ,@lst))]
    [`(,op ,e1 ,e2)
     (if (and (eq? 'deref (car e1))
              (eq? 'deref (car e2)))
         `((movq ,e1 (reg rax))
           (,op (reg rax) ,e2))
         `((,op ,e1 ,e2)))]
    [else `(,e)]))

(define (print-x86 e)
  #f)

;; Define the passes to be used by interp-tests and the grader
;; Note that your compiler file (or whatever file provides your passes)
;; should be named "compiler.rkt"
(define r1-passes
  `(("uniquify" ,(uniquify '()) ,interp-scheme)
    ("flatten" ,flatten, interp-C)
    ("select-instructions" ,select-instr, interp-x86)
    ("assign-homes" ,assign-homes, interp-x86)
    ("patch-instr" ,patch-instr, interp-x86)
    ))
