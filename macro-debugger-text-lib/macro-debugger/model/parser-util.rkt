#lang racket/base
(require (for-syntax racket/base racket/syntax syntax/parse racket/promise
                     racket/dict syntax/id-table racket/list)
         (prefix-in yacc: parser-tools/yacc)
         (prefix-in yacc: parser-tools/lex))
(provide (all-defined-out))

(begin-for-syntax
  (require (only-in syntax/parse [attribute $])))

(define-syntax-rule (expression/begin-for-syntax e)
  (#%expression (let-syntaxes ([() (begin0 (#%plain-app values) e)]) (#%plain-app void))))

;; ------------------------------------------------------------

(begin-for-syntax
  (define implicit-etokens (make-hasheq)) ;; mutated
  (define implicit-vtokens (make-hasheq)) ;; mutated
  (struct token-group (enames vnames))

  (define-syntax-class etoken
    (pattern ref:id #:attr tg (hash-ref implicit-etokens (syntax-e #'ref) #f) #:when (attribute tg)))
  (define-syntax-class vtoken
    (pattern ref:id #:attr tg (hash-ref implicit-vtokens (syntax-e #'ref) #f) #:when (attribute tg)))

  (define (empty-token? ref) (hash-ref implicit-etokens (syntax-e ref) #f))

  (define (check-top-level stx)
    (unless (memq (syntax-local-context) '(module top-level))
      (raise-syntax-error #f "bad context; must be used at top level or module top level" stx)))

  )

(define-syntax (define-tokens stx)
  (check-top-level stx)
  (syntax-parse stx
    [(_ name (~alt (~seq #:tokens (vtoken:id ...)) (~seq #:empty-tokens (etoken:id ...))) ...)
     ;; Because of yacc bug, token-group names must have lctx w/ normal #%datum binding!
     ;; So use (format-id #'here _) instead of (generate-temporaries _).
     (with-syntax ([yacc-ename (format-id #'here "~a-empty-tokens" #'name)]
                   [yacc-vname (format-id #'here "~a-value-tokens" #'name)])
       #'(begin (yacc:define-empty-tokens yacc-ename (etoken ... ...))
                (yacc:define-tokens yacc-vname (vtoken ... ...))
                (define-syntax name
                  (token-group (let ([egroup #'yacc-ename])
                                 (hasheq (~@ 'etoken egroup) ... ...))
                               (let ([vgroup #'yacc-vname])
                                 (hasheq (~@ 'vtoken vgroup) ... ...))))))]))

(define-syntax (use-tokens! stx)
  (check-top-level stx)
  (syntax-parse stx
    [(_ (~var tg (static token-group? "token group")) ...)
     (for ([tg (in-list (attribute tg.value))])
       (for ([(token ytg) (in-hash (token-group-enames tg))])
         (hash-set! implicit-etokens token ytg))
       (for ([(token ytg) (in-hash (token-group-vnames tg))])
         (hash-set! implicit-vtokens token ytg)))
     #'(begin)]))

;; ------------------------------------------------------------

(begin-for-syntax

  ;; A NonterminalInfo is (nonterminal Symbol (Listof Production))
  (struct nonterminal (name productions) #:transparent)

  ;; A Production is (production (Promise (Listof Elem)) (Listof Nat) Syntax[Expr])
  (struct production (pattern0 indexes action) #:transparent)

  (define (production-pattern p) (force (production-pattern0 p)))

  ;; An Elem is either (t-ref Id Boolean Id) or (nt-ref Id Nonterminal)
  (struct t-ref (name val? tg) #:transparent)
  (struct nt-ref (name info) #:transparent)

  (define-syntax-class prod #:attributes ([ast 1] [bind 1] [index 1] rhs)
    #:description "production"
    (pattern [(e:elem ...) rhs:expr]
             #:with (ast ...) #'(e.ast ...)
             #:with ([bind index] ...)
             (for/list ([e (in-list (attribute e.bind))]
                        [ref (in-list (attribute e.ref))]
                        [k (in-naturals 1)]
                        #:when e)
               (e k (format-id ref "$~a" k)))))

  (define-syntax-class elem #:attributes (ref ast bind)
    #:description "terminal or nonterminal element"
    #:literals (_)
    (pattern :base-elem #:attr bind (and ($ val?) (lambda (k kid) (list kid k))))
    (pattern [_ :base-elem] #:attr bind #f)
    (pattern [name:id :base-elem] #:when ($ val?) #:attr bind (lambda (k kid) (list #'name k))))

  (define-syntax-class base-elem #:attributes (ref ast val?)
    #:description "terminal or nonterminal reference"
    (pattern ref:etoken #:attr val? #f #:with ast #'[#:t ref #f ref.tg])
    (pattern ref:vtoken #:attr val? #t #:with ast #'[#:t ref #t ref.tg])
    (pattern ref:id     #:attr val? #t #:with ast #'[#:nt ref]))

  (define (check-nonterminal ntinfo)
    (for ([p (in-list (nonterminal-productions ntinfo))])
      (production-pattern p)))

  (define (lookup-nonterminal nt)
    (let ([v (syntax-local-value nt (lambda () #f))])
      (if (nonterminal? v) v (raise-syntax-error #f "not defined as nonterminal" nt))))

  (define (resolve-elems elems)
    (for/list ([elem (in-list (syntax->list elems))])
      (syntax-case elem ()
        [[#:t t v? tg] (t-ref #'t (syntax-e #'v?) #'tg)]
        [[#:nt nt] (nt-ref #'nt (lookup-nonterminal #'nt))]))))

(define-syntax define-nt
  (syntax-parser
    [(_ nt:id p:prod ...)
     (with-syntax ([(action ...)
                    (generate-temporaries
                     (for/list ([_i (in-list (syntax->list #'(p ...)))]) #'nt))])
       #'(begin
           (define (action p.bind ...) p.rhs) ...
           (define-syntax nt
             (nonterminal 'nt
                          (list (production (delay (resolve-elems (quote-syntax (p.ast ...))))
                                            (quote (p.index ...))
                                            (quote-syntax action))
                                ...)))
           (expression/begin-for-syntax
            (check-nonterminal (lookup-nonterminal (quote-syntax nt))))))]))

(define-syntax parser
  (syntax-parser
    [(_ (~alt (~once (~seq #:start start-nt:id ...))
              (~once (~seq #:end (~or* end-token:etoken end-token:vtoken) ...))
              (~once (~seq #:error error-handler:expr))
              (~optional (~seq #:debug debug-file:string)))
        ...)
     (define ntdefs null) ;; mutated
     (define token-groups (make-free-id-table)) ;; Id => #t
     (define start-nts
       (let ()
         (define seen (make-hasheq)) ;; Symbol => (U nonterminal token-group-id)
         (define (register-symbol! id sym v)
           (cond [(hash-ref seen sym #f)
                  => (lambda (w)
                       (or (equal? v w)
                           (raise-syntax-error #f "symbol conflict" this-syntax id)))]
                 [else (hash-set! seen sym v) #f]))
         (define (handle-nonterminal nt info) ;; => Void
           (unless (register-symbol! nt (nonterminal-name info) info)
             (set! ntdefs
                   (cons (cons (nt->stx nt info)
                               (for/list ([p (in-list (nonterminal-productions info))])
                                 (production->stx p)))
                         ntdefs))))
         (define (production->stx p)
           (list (for/list ([e (in-list (production-pattern p))])
                   (elem->stx e))
                 (cons (production-action p)
                       (for/list ([k (in-list (production-indexes p))])
                         (format-id this-syntax "$~a" k)))))
         (define (elem->stx e)
           (cond [(t-ref? e)
                  (let ([t (t-ref-name e)] [tg (t-ref-tg e)])
                    (register-symbol! t (syntax-e t) tg)
                    (free-id-table-set! token-groups tg #t)
                    (t->stx t))]
                 [(nt-ref? e)
                  (let ([nt (nt-ref-name e)] [info (nt-ref-info e)])
                    (nt->stx nt info))]))
         (define (t->stx t)
           (datum->syntax this-syntax (syntax-e t) t))
         (define (nt->stx nt info)
           (handle-nonterminal nt info)
           (datum->syntax this-syntax (nonterminal-name info) nt))
         (for ([tg (in-list (syntax->list #'(end-token.tg ...)))])
           (free-id-table-set! token-groups tg #t))
         (for/list ([nt (in-list (syntax->list #'(start-nt ...)))])
           (nt->stx nt (lookup-nonterminal nt)))))
     (with-syntax ([(shadow-nt ...) (map car ntdefs)]
                   [(ntdef ...) ntdefs]
                   [(start-nt* ...) start-nts]
                   [(token-group ...) (dict-keys token-groups)])
       #'(let ([shadow-nt '#f] ...)
           (yacc:parser
            (tokens token-group ...)
            (grammar ntdef ...)
            (start start-nt* ...)
            (end end-token ...)
            (error error-handler)
            (~? (debug debug-file)))))]))

;; ------------------------------------------------------------

(begin-for-syntax

  (define-syntax-class ?nt #:attributes (name okay skip fail)
    (pattern name:id
             #:attr okay (let ([m (regexp-match #rx"^[?](.*)$" (symbol->string (syntax-e #'name)))])
                           (and m (datum->syntax #'name (string->symbol (cadr m)) #'name)))
             #:when ($ okay)
             #:attr skip (and ($ okay) (format-id #'name "~a/Skipped" ($ okay)))
             #:attr fail (and ($ okay) (format-id #'name "~a/Interrupted" ($ okay)))))

  (define (process-okay-elem e)
    (syntax-parse e
      #:literals (! !!)
      [[#:nt !] #'[#:nt !/OK]]
      [[#:nt !!] #f]
      [[#:nt nt:?nt] #'[#:nt nt.okay]]
      [_ e]))

  (define (process-skip-elem e)
    (syntax-parse e
      #:literals (! !!)
      [[#:nt !] #'[#:nt !/OK]]
      [[#:nt !!] #'[#:nt !/OK]]
      [[#:nt nt:?nt] #'[#:nt nt.skip]]
      [[#:t t _ _] #'[#:nt t/Skipped]]))

  (define (process-fail-elem e)
    (syntax-parse e
      #:literals (! !!)
      [[#:nt !] #'[#:nt !/Interrupted]]
      [[#:nt !!] #'[#:nt !/Interupted]]
      [[#:nt nt:?nt] #'[#:nt nt.fail]]
      [_ #f]))

  (define ((make-nt*-transformer process-X-ast) stx)
    (syntax-case stx ()
      [(_ nt/X ([ast indexes action] ...))
       (with-syntax ([([ast* indexes* action*] ...)
                      (append* (map process-X-ast
                                    (syntax->list #'(ast ...))
                                    (syntax->list #'(indexes ...))
                                    (syntax->list #'(action ...))))])
         #'(define-syntax nt/X
             (nonterminal 'nt/X
                          (list (production (delay (resolve-elems (quote-syntax ast*)))
                                            (quote indexes*)
                                            (quote-syntax action*))
                                ...))))]))

  (define (process-okay-ast ast indexes action)
    (define ast* (map process-okay-elem (syntax->list ast)))
    (cond [(andmap values ast*)
           (list (list ast* indexes action))]
          [else null]))

  (define (process-fail-ast ast indexes action)
    ;; {fail,skip}-loop : (Listof ElemStx) (Listof ElemStx) -> (Listof (Listof ElemStx))
    (define (fail-loop es acc)
      (cond [(pair? es)
             (define okay-e (process-okay-elem (car es)))
             (define fail-e (process-fail-elem (car es)))
             (append (if okay-e (fail-loop (cdr es) (cons okay-e acc)) null)
                     (if fail-e (skip-loop (cdr es) (cons fail-e acc)) null))]
            [else null]))
    (define (skip-loop es acc)
      (list (append (reverse acc) (map process-skip-elem es))))
    (map (lambda (ast*) (list ast* indexes action))
         (fail-loop (syntax->list ast) null))))

(define-syntax define-nt*
  (syntax-parser
    [(_ nt:id
        (~alt (~optional (~seq #:args args))
              (~optional (~seq #:skipped skipped:expr))) ...
              p:prod ...)
     (with-syntax ([nt/Skip (format-id #'nt "~a/Skipped" #'nt)]
                   [nt/Fail (format-id #'nt "~a/Interrupted" #'nt)]
                   [(action ...)
                    (generate-temporaries
                     (for/list ([_i (in-list (syntax->list #'(p ...)))]) #'nt))]
                   [(skipped-action)
                    (generate-temporaries '(skipped))])
       #'(begin
           (define (action p.bind ...) (~? (lambda args p.rhs) p.rhs)) ...
           (define (skipped-action) (~? skipped #f))
           (define-nt/Okay nt      ([(p.ast ...) (p.index ...) action] ...))
           (define-nt/Fail nt/Fail ([(p.ast ...) (p.index ...) action] ...))
           (define-syntax nt/Skip
             (nonterminal 'nt/Skip (list (production null null #'skipped-action))))
           (expression/begin-for-syntax
            (begin (check-nonterminal (lookup-nonterminal (quote-syntax nt)))
                   (check-nonterminal (lookup-nonterminal (quote-syntax nt/Fail)))))))]))

(define-syntax define-nts*
  (syntax-parser
    [(_ [nt:id part ...] ...)
     #'(begin (define-nt* nt part ...) ...)]))

(define-syntax define-nt/Okay (make-nt*-transformer process-okay-ast))
(define-syntax define-nt/Fail (make-nt*-transformer process-fail-ast))

(define-syntax ! #f)
(define-syntax !! #f)

(define-tokens basic-tokens #:tokens (ERROR))
(use-tokens! basic-tokens)

(define-nt !/OK [() #f])
(define-nt !/Interrupted [(ERROR) $1])
(define-nt t/Skipped [() #f])
