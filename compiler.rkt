#lang racket
(require racket/set racket/stream)
(require graph)
(require "multigraph.rkt")
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "priority_queue.rkt")
;; additional files for L-if
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
;;additional files for L-fun
(require "interp-Cfun.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(provide (all-defined-out))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uniquify : R1 -> R1
(define (uniquify p)
  
  (define (check-key my-dict key)
  (define key-set (dict-keys my-dict))
  (define (check-it lst key)
    (cond
      [(empty? lst) (error "Variable used before declaring : " key)]
      [(equal? (car lst) key) (dict-ref my-dict key)]
      [else (check-it (cdr lst) key)]))
  (check-it key-set key))

  (define (doit env prog)
    (match prog
      [(Int n) (Int n)]
      [(Bool n) (Bool n)]
      [(Prim op es)
       (Prim op (for/list ([e es]) (doit env e)))]
      [(Var x)  (Var (check-key env x))] 
      [(Let x y body) (set! env (dict-set env x (gensym)))
                      (Let
                          (dict-ref env x)
                          (doit env y)
                          (doit env body))]
      [(If e1 e2 e3) (If (doit env e1) (doit env e2) (doit env e3))]
      ;for each function definition create a new env.
      [(Def var lst type info exp)
       (define new-env '())
       (define new-lst '())
       (for ([i (dict-keys lst)])
         (set! new-env (dict-set new-env i (gensym)))
         (set! new-lst (dict-set new-lst (dict-ref new-env i) (dict-ref lst i))))
       (Def var new-lst type info (doit new-env exp))]
      [(Apply var lst)
       ;for each expression also we need to create new env.
       (Apply var (for/list ([i lst]) (doit env i)))]
      ))
  
  (match p
    [(ProgramDefs '() defs)
     (ProgramDefs '() (for/list ([i defs]) (doit '() i)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;reveal_functions pass
;; this pass is being run as per ProgramDefs syntax and not ProgramDefsExp
(define (reveal_functions prog)

  (define (doit func)
    (match func
      [(Int x) (Int x)]
      [(Var var) (Var var)]
      [(Bool b) (Bool b)]
      [(Prim op (list e1 e2)) (Prim op (list (doit e1) (doit e2)))]
      [(Prim op (list e1)) (Prim op (list (doit e1)))]
      [(Let var e1 e2) (Let var (doit e1) (doit e2))]
      [(If e1 e2 e3) (If (doit e1) (doit e2) (doit e3))]
      [(Def var lst type lst2 exp) (Def var lst type lst2 (doit exp))]
      [(Apply (Var fname) lst)
       (Apply (FunRef fname (length lst)) (for/list ([i lst]) (doit i)))]
      [else func]))
  
  (match prog
    [(ProgramDefs info defs)
     (ProgramDefs info (for/list ([i defs]) (doit i)))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* prog)

  (define (atom? exp)
    (match exp
      [(Var x) #t]
      [(Int n) #t]
      [(Bool b) #t]
      ;[(FunRef label int) #t]
      [_ #f]))

  (define (atomise env prog)
    (match prog
      [(Prim op es)
       (cond
         [(andmap (lambda (x) (atom? x)) es) (Prim op es)]
         [else
          (define flag 0)
          (define newargs
            (for/list ([i es])
                 (cond
                   [(atom? i) i]
                   [(equal? flag 1) i]
                   [(equal? (atom? i) #f)
                    (set! env (dict-set env i (gensym)))
                    (set! flag 1) (Var (dict-ref env i))])))
          (define temp (list-ref (dict-keys env) 0))         
          
          (doit '() (Let (dict-ref env temp) temp (Prim op newargs)))])]
      [(Apply var lst)
       (cond
         [(and (atom? var)(andmap (lambda (x) (atom? x)) lst)) (Apply var lst)]
         [(equal? (atom? var) #f)
          (define temp (gensym))
          (doit '() (Let temp var (Apply (Var temp) lst)))]
         [else
          (define flag 0)
          (define newargs
            (for/list ([i lst])
                 (cond
                   [(atom? i) i]
                   [(equal? flag 1) i]
                   [(equal? (atom? i) #f)
                    (set! env (dict-set env i (gensym)))
                    (set! flag 1) (Var (dict-ref env i))])))
          (define temp (list-ref (dict-keys env) 0))         
          
          (doit '() (Let (dict-ref env temp) temp (Apply var newargs)))])]))

  (define (doit env prog)
    (match prog
      [(Int n) (Int n)]
      [(Var x) (Var x)]
      [(Bool b) (Bool b)]
      [(FunRef name num) (FunRef name num)]
      [(Let var exp1 exp2) (Let var (doit env exp1) (doit env exp2))]
      [(Prim op es) (atomise env prog)]
      [(If e1 e2 e3) (If (doit env e1) (doit env e2) (doit env e3))]
      [(Def var lst1 type info exp) (Def var lst1 type info (doit env exp))]
      [(Apply funref lst) (atomise env prog)]))

  (define (sort-it lstdefs ret exp)
    (cond
      [(empty? lstdefs) (values ret exp)]
      [else
       (match (car lstdefs)
         ;[(Def 'main lst1 'Integer lst2 e) (sort-it (cdr lstdefs) ret (doit '() e))]
         [(Def label lst1 type lst2 e)
          (sort-it (cdr lstdefs)
                   (append ret (list (Def label lst1 type lst2 (doit '() e))))
                   exp)])]))
  
  (match prog
    [(ProgramDefs '() lstdefs)
     (define-values (newlst exp) (sort-it lstdefs '() 0))
     (ProgramDefs '() newlst)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)

  (define basic-block empty) ;dictionary label : tail pair.
  
  (define (create-block tail)
    (match tail
      [(Goto label) (Goto label)]
      [else
       (let ([label (gensym 'block)])
         (set! basic-block (dict-set basic-block label tail))
         (Goto label))]))

  (define (explicate-pred cnd thn els)
    (match cnd
      [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool '#t))) (create-block thn) (create-block els))]
      [(Bool b) (IfStmt (Prim 'eq? (list (Bool b) (Bool '#t))) (create-block thn) (create-block els))]
      ;[(Var x) (if x (create-block thn) (create-block els))]
      ;[(Bool x) (if x (create-block thn) (create-block els))]
      [(Let x rhs body) (explicate_assign rhs x (explicate-pred body thn els))]
      [(Prim 'not (list e)) (IfStmt (Prim 'eq? (list e (Bool '#f))) (create-block thn) (create-block els))]
      [(Prim op es) (IfStmt cnd (create-block thn) (create-block els))]
      [(If ncnd nthn nels)
       (define label-thn (create-block thn))
       (define label-els (create-block els))
       (explicate-pred ncnd
         (explicate-pred nthn label-thn label-els) ;label-thn is already of format (Goto label)
         (explicate-pred nels label-thn label-els))]
      [(Apply atm lst) (IfStmt (Prim 'eq? (list (Call atm lst) (Bool '#t)))
                               (create-block thn) (create-block els))]
      [else (error "explicate-pred unhandled case")]))
  
  (define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(If cnd thn els) (explicate-pred cnd (explicate_tail thn) (explicate_tail els))]
    [(Apply atm lst) (TailCall atm lst)]
    ;function is treated like a datatype.
    [(FunRef name num) (Return (FunRef name num))]
    [else (error "unhandled case in explicate_tail")]))
  
  (define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) e)  cont)]
    [(If cnd thn els)
     (define cont_block (create-block cont))
     (explicate-pred cnd (explicate_assign thn x cont_block) (explicate_assign els x cont_block))]
    [(Apply fun lst) (Seq (Assign (Var x) (Call fun lst)) cont)]
    [(FunRef name num) (Seq (Assign (Var x) (FunRef name num)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

  (define (explicate_fun fun)
    (match fun
      [(Def label params type info body)
       (set! basic-block '())
       (define start (explicate_tail body))
       (define final-label (symbol-append label 'start))
       (set! basic-block (dict-set basic-block final-label start))
       (Def label params type info basic-block)]))
  
  (match p
    [(ProgramDefs info listdefs)
     ;(define dict-body empty)
     ;(define start (explicate_tail body))
     ;(set! basic-block (dict-set basic-block 'start start))
     ;(CProgram info basic-block)
     (ProgramDefs info (for/list ([i listdefs]) (explicate_fun i)))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Select instructions Cvar -> Xvar

(define (select-instructions p)

  ;This function is just to test whether the param is atomic or not.
  (define (atomic? exp)
    (match exp
      [(Int n) #t]
      [(Var x) #t]
      [(Bool b) #t]
      [else #f]))

  ;dict for num to param passing register
  ; rdi, rsi, rdx, rcx, r8, r9
  (define param-dict '((0 . rdi) (1 . rsi) (2 . rdx) (3 . rcx) (4 . r8) (5 . r9)))  
  
  (define (handle_atm body)
    (match body
      [(Var x) (Var x)]
      [(Int x) (Imm x)]
      [(Bool '#t) (Imm 1)]
      [(Bool '#f) (Imm 0)]
      [else (error "unhandled case in handle_atm")]))

  (define (get-cc cmp)
    (match cmp
      ['eq? 'e]
      ['< 'l]
      ['<= 'le]
      ['> 'g]
      ['>= 'ge]))
  
  (define (handle_prim var body)
    (match body
      [(Prim '+ args) (list (Instr 'movq (list (handle_atm (car args)) var)) (Instr 'addq (list (handle_atm (car (cdr args))) var)))]
      [(Prim '- args)
       (cond [(equal? 2 (length args)) (list (Instr 'movq (list (handle_atm (car args)) var)) (Instr 'subq (list (handle_atm (car (cdr args))) var)))]
             [else (list (Instr 'movq (list (Imm 0) var)) (Instr 'subq (list (handle_atm (car args)) var)))])]
      [(Prim 'read args)
       (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) var)))]
      [(Prim 'not (list arg))
       (list (Instr 'movq (list (handle_atm arg) var)) (Instr 'xorq (list (Imm 1) var)))]
      [(Prim cmp (list arg1 arg2))
       (list (Instr 'cmpq (list (handle_atm arg2) (handle_atm arg1)))
             (Instr 'set (list (get-cc cmp) (ByteReg 'al)))
             (Instr 'movzbq (list (ByteReg 'al) var)))]
      [(FunRef label int) (list (Instr 'leaq (list (Global label) (Reg 'rax)))
                                (Instr 'movq (list (Reg 'rax) var)))]
      [(Call atm lst)
       (append
        (append
        (push-caller-saved)
        (append
         (move-params lst 0 '())
         (list
          (IndirectCallq atm (length lst))
          (Instr 'movq (list (Reg 'rax) var)))))
        (pop-caller-saved))]))
  
  (define (push-caller-saved)
    (list (Instr 'pushq (list (Reg 'rax)))
          (Instr 'pushq (list (Reg 'rcx)))
          (Instr 'pushq (list (Reg 'rdx)))
          (Instr 'pushq (list (Reg 'rsi)))
          (Instr 'pushq (list (Reg 'rdi)))
          (Instr 'pushq (list (Reg 'r8)))
          (Instr 'pushq (list (Reg 'r9)))
          (Instr 'pushq (list (Reg 'r10)))
          (Instr 'pushq (list (Reg 'r11)))))

  (define (pop-caller-saved)
    (list (Instr 'popq (list (Reg 'r11)))
          (Instr 'popq (list (Reg 'r10)))
          (Instr 'popq (list (Reg 'r9)))
          (Instr 'popq (list (Reg 'r8)))
          (Instr 'popq (list (Reg 'rdi)))
          (Instr 'popq (list (Reg 'rsi)))
          (Instr 'popq (list (Reg 'rdx)))
          (Instr 'popq (list (Reg 'rcx)))
          (Instr 'popq (list (Reg 'rax)))))
  
  (define (handle_stmt stmt)
    (match stmt
      [(Assign var exp)
       (cond
         [(atomic? exp) (list (Instr 'movq (list (handle_atm exp) var)))]
         [else (handle_prim var exp)])]))

 
  (define (move-params lst num ret)
    (cond
      [(empty? lst) ret]
      [else (move-params (cdr lst)
                         (+ num 1)
                         (append ret (list (Instr 'movq (list (handle_atm (car lst)) (Reg (dict-ref param-dict num)))))))]
      ))
  
  (define (handle_tail body)
    (match body
      [(Return exp)
       (cond [(atomic? exp) (list (Instr 'movq (list (handle_atm exp) (Reg 'rax))) (Jmp 'conclusion))]
             [else (append (handle_prim (Reg 'rax) exp) (list (Jmp 'conclusion)))])]
      [(Seq stmt tail)
       (append (handle_stmt stmt) (handle_tail tail))]
      [(Goto label) (list (Jmp label))]
      [(IfStmt (Prim cmp (list arg1 arg2)) (Goto l1) (Goto l2))
       (list (Instr 'cmpq (list (handle_atm arg2) (handle_atm arg1)))
             (JmpIf (get-cc cmp) l1)
             (Jmp l2))]
      [(TailCall atm lst)
       (append (move-params lst 0 '()) (list (TailJmp atm (length lst))))]
      [else (println body)(error "unhandled case in handle_tail")]))
  
  (define (get_block info body)
    (match body
      [(Return exp) (Block info (handle_tail body))]
      [(Seq stml tail) (Block info (handle_tail body))];it shd return list of instructions
      [else (Block info (handle_tail body))])) ;for all body: output = (handle_tail body) 

  (define (symbol-append s1 s2)
    (define st1 (symbol->string s1))
    (define st2 (symbol->string s2))
    (string->symbol (string-append st1 st2)))

  (define (move-to-vars args ret num)
    (cond
      [(empty? args) ret]
      [else (move-to-vars (cdr args)
                          (append ret (list (Instr 'movq (list (Reg (dict-ref param-dict num)) (Var (car args))))))
                          (+ 1 num))]
       ))
  
  (define (modify_start info args instrs)
    ; modify the instructions to move params to local variables
    ; then call get_block info on newinstrs
    
    (define newinstrs (append (move-to-vars args '() 0) instrs))
    newinstrs)

  (define (bmodify_start info args instrs)
    (match instrs
      [(Block inf instrs) (Block inf (modify_start inf args instrs))]))
  (define (modify-def fun)
    (match fun
      [(Def label args type info lstblocks)
       ;; out will have Xfun instructions.
       (define out
         (for/list ([i (dict-keys lstblocks)])
           (cons i (get_block info (dict-ref lstblocks i)))))
       (define newinfo (dict-set info 'num-params (length args)))
       ;;newout is for copying params from registers to local variables.
       (define newout
         (for/list ([i (dict-keys out)])
           (if (equal? i (symbol-append label 'start))
               (cons i (bmodify_start info (dict-keys args) (dict-ref out i)))
               ;(cons i (dict-ref out i))
               (cons i (dict-ref out i)))))
       (Def label '() type newinfo newout)]))
  
  (match p
    [(ProgramDefs info lstdefs)
     (define mlstdefs
       (for/list ([i lstdefs]) (modify-def i)))
     (X86Program info mlstdefs)]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;uncover-live pass

(define (uncover-live p)
  (define lbefore-block empty)
  
  (define caller-saved (set 'rax 'rcx 'rdx 'rsi 'rdi 'r8 'r9 'r10 'r11))
  (define callee-saved (set 'rsp 'rbp 'rbx 'r12 'r13 'r14 'r15))

  (define (get-it int ret)
    (cond
      [(equal? int 0) ret]
      [(equal? int 1) (set-union ret (set 'rdi))]
      [(equal? int 2) (set-union ret (set 'rsi))]
      [(equal? int 3) (set-union ret (set 'rdx))]
      [(equal? int 4) (set-union ret (set 'rcx))]
      [(equal? int 5) (set-union ret (set 'r8))]
      [(equal? int 6) (set-union ret (set 'r9))]))
  
  (define (check-it a b)
    (match* (a b)
      [((Imm x) (Var y)) (set y)]
      [((Var x) (Var y)) (set x y)]
      [((Reg x) (Var y)) (set x y)]
      [((Imm x) (Reg y)) (set y)]
      [((Var x) (Reg y)) (set x y)]
      [((Reg x) (Reg y)) (set x y)]
      [((ByteReg 'al) _) (set 'rax)]
      [(_ _) (set)]))
  ;get-set should return a set of Lbefore for given instr.
  (define (get-set inst prev-set base-set)
    (match inst
      [(Instr 'addq (list a1 a2))
       (set-union prev-set (check-it a1 a2))]
      [(Instr 'subq (list a1 a2))
       (set-union prev-set (check-it a1 a2))]
      [(Instr 'negq (list a1))
       prev-set]
      [(Instr 'movq (list a1 a2)) ;remove a2 and add a1
       (set-union (set-subtract prev-set (check-it (Imm 8) a2)) (check-it (Imm 8) a1) )]
      [(Instr 'pushq (list a1)) ; a1 shd be added
       (set-union prev-set (check-it (Imm 8) a1))]
      [(Instr 'popq (list a1)) ; a1 shd be subtracted
       (set-subtract prev-set (check-it (Imm 8) a1))]
      [(Callq label num)
       (set-subtract prev-set caller-saved)]
      ;we shd add argument passing registers depending on arity
      ;but only function we have is read which takes no argument
      [(Retq)
       (set-subtract prev-set callee-saved)]
      [(Jmp label) base-set]
      [(Instr 'xorq (list a1 a2)) (set-union prev-set (check-it a1 a2))]
      [(Instr 'cmpq (list a1 a2)) (set-union prev-set (check-it a1 a2))]
      ;%al is essentially lower 1 byte of rax register.
      [(Instr 'set (list cc arg)) (set-subtract prev-set (check-it arg (Imm 8)))]
      [(Instr 'movzbq (list a1 a2))
       (set-union (set-subtract prev-set (check-it (Imm 8) a2)) (check-it a1 (Imm 8)))]
      [(JmpIf cc label) base-set]
      [(IndirectCallq arg int)
       (set-union (set-union (set-subtract prev-set caller-saved) (check-it (Imm 8) arg)) (get-it int (set)))]
      [(TailJmp arg int)
       (set-union (set-union base-set (check-it (Imm 8) arg)) (get-it int (set)))]
      [(Instr 'leaq (list label reg))
       (set-subtract prev-set (check-it (Imm 8) reg))]))
  
  (define (traverse instrs ret base-set)
      (cond
        [(empty? instrs) ret]
        [else (traverse (cdr instrs) (cons
                                      (get-set (car instrs) (if (empty? ret)
                                                        (set)
                                                        (car ret)) base-set)
                                      ret) base-set)]))

  ; get set-union of all lbefore sets of children blocks
  (define (get-base-set ret-set n-lst)
    (cond
      [(empty? n-lst) ret-set]
      [else (get-base-set
             (set-union ret-set (dict-ref lbefore-block (car n-lst)))
             (cdr n-lst))]))
  
  ; need to get the lbefore set of the child block
  (define (get-live-set instrs cfg label)
    (define rev-instrs (reverse instrs))
    (define base-set (get-base-set (set) (get-neighbors cfg label)))
    (traverse rev-instrs '() base-set))
 
  
  (define (get-liveness a cfg label)
    (match a
      [(Block info instrs)
       (define new-info (dict-set info 'live-after-set (get-live-set instrs cfg label)))
       (set! lbefore-block
             (dict-set lbefore-block label (car (dict-ref new-info 'live-after-set))))
       ;(println 1)
       (Block  new-info instrs)]))  

  (define (make-cfg mydict)
    (define cfg (make-multigraph empty))
    ;will return list of labels to which control jumps.
    (define (get-nodes instrs ret)
      (if (empty? instrs)
          ret
          (match (car instrs)
            [(JmpIf cc label) (get-nodes (cdr instrs) (append ret (list label)))]
            [(Jmp label) (get-nodes (cdr instrs) (append ret (list label)))]
            [(TailJmp arg int) (get-nodes (cdr instrs) (append ret (list 'conclusion)))]
            [else (get-nodes (cdr instrs) ret)])))
    ;will add edges between i and the given list
    (define (add-edges parent child-lst)
      (cond
        [(empty? child-lst) cfg]
        [else
         (add-vertex! cfg (car child-lst))
         (add-vertex! cfg parent)
         (add-directed-edge! cfg parent (car child-lst))
         (add-edges parent (cdr child-lst))]))
    ;(Block info instrs)
    (define (get-instrs block)
      (match block
        [(Block info instrs) instrs]))
    
    (for/list ([i (dict-keys mydict)])
      (define lst (get-nodes (get-instrs (dict-ref mydict i)) empty))
      (add-edges i lst)
      )
    cfg)

  (define (sort-it-out def)
    (match def
      [(Def label args type info block-dict)
       (set! lbefore-block empty)
       
       (define cfg (make-cfg block-dict))  ;cfg is a multigraph
       
       (define mcfg (tsort (transpose cfg)))
       
       ;mcfg is list of blocks, in traversal order + conclusion block.
       (set! lbefore-block (dict-set lbefore-block 'conclusion (set 'rax 'rsp)))
       ;get-liveness needs (Block info instrs), cfg, label of block.
        
       (define newbody
         (for/list ([i mcfg])
           (cond
             [(equal? i 'conclusion) (cons i empty)]
             [else (cons i (get-liveness (dict-ref block-dict i) cfg i))])))
       
       (Def label args type (dict-set info 'cfg cfg)
                            (dict-remove newbody 'conclusion))
       ]))
  
  (match p
    [(X86Program info deflst)
     (define newdeflst (for/list ([i deflst]) (sort-it-out i)))    
     (X86Program info newdeflst)]))


;; build_interference

(define (build-interference p)

  (define (doit lst1 lst2 graph)
    (cond
      [(empty? lst2) graph]
      [else
       (add-edge! graph (car lst1) (car lst2))
       (doit lst1 (cdr lst2) graph)]))
  
  (define (get-set a1 a2)
    (match* (a1 a2)
      [((Imm x) (Imm y)) (set)]
      [((Imm x) (Var y)) (set y)]
      [((Var x) (Var y)) (set x y)]
      [((Reg x) (Var y)) (set x y)]
      [((Imm x) (Reg y)) (set y)]
      [((Var x) (Reg y)) (set x y)]
      [((Reg x) (Reg y)) (set x y)]      
      [((ByteReg 'al) (Reg y)) (set 'rax y)]
      [((ByteReg 'al) (Var y)) (set 'rax y)]
      [((ByteReg 'al) _) (set 'rax)]))

  ; construction rules of graph are given in pg no 43 of EoC
  (define (add-edges instr live-set graph)
    (match instr
      [(Instr 'addq (list a1 a2))
       (doit (set->list (get-set (Imm 3) a2))
             (set->list (set-subtract live-set (get-set (Imm 8) a2)))
             graph)]
      [(Instr 'subq (list a1 a2))
       (doit (set->list (get-set (Imm 3) a2))
             (set->list (set-subtract live-set (get-set (Imm 8) a2)))
             graph)]
      [(Instr 'negq (list a1))
       (doit (set->list (get-set (Imm 3) a1))
             (set->list (set-subtract live-set (get-set (Imm 3) a1)))
             graph)]
      [(Instr 'movq (list a1 a2))
       
       (doit (set->list (get-set (Imm 3) a2))
             (set->list (set-subtract live-set (get-set a1 a2)))
             graph)]
      [(Instr 'pushq (list a1))
       graph] ; its not writing to any var or register.
      [(Instr 'popq (list a1)) 
       (doit (set->list (get-set (Imm 3) a1))
             (set->list (set-subtract live-set (get-set (Imm 3) a1)))
             graph)]
      [(Callq label num)
       graph] ; any registers being read will be present in later live sets.   
      [(Retq)
       graph]
      [(Instr 'xorq (list a1 a2))
       (doit (set->list (get-set (Imm 1) a2))
             (set->list (set-subtract live-set (get-set (Imm 1) a2)))
             graph)]
      ;cmpq is lite as it has no write set.
      [(Instr 'set (list cc arg))
       (doit (set->list (get-set arg (Imm 1)))
             (set->list (set-subtract live-set (get-set arg (Imm 1))))
             graph)]
      [(Instr 'movzbq (list a1 a2))
       (doit (set->list (get-set (Imm 1) a2))
             (set->list (set-subtract live-set (get-set a1 a2)))
             graph)]
      [(IndirectCallq arg int)
       graph]; has no write-set.
      [(Instr 'leaq (list label reg))
       (doit (set->list (get-set (Imm 1) reg))
             (set->list (set-subtract live-set (get-set (Imm 1) reg)))
             graph)]
      [else   ; else if for possible jmp instructions.
       graph])) 
  
  (define (traverse instrs lst graph)
    (cond
      [(empty? lst) graph]
      [else (traverse (cdr instrs) (cdr lst) (add-edges (car instrs) (car lst) graph))]))
  
  (define (get-graph instrs lst)
    (traverse instrs (cdr lst) (undirected-graph '())))
  
  (define (get-interference a)
    (match a
      [(Block info instrs)
       (define new-info
         (dict-set info 'conflicts (get-graph instrs (dict-ref info 'live-after-set))))
       (define new-info2
         (dict-set new-info 'list-edges (get-edges (dict-ref new-info 'conflicts))))
       (Block  new-info2 instrs)]))

  (define (sort-it def)
    (match def
      [(Def label args type info body-dict)
       (define new-body
         (for/list ([i (dict-keys body-dict)]) (cons i (get-interference (dict-ref body-dict i)))))
       (Def label args type info new-body)
       ]))
  
  (match p
    [(X86Program info deflist)
     (define new-deflist
       (for/list ([i deflist]) (sort-it i)))
     (X86Program info new-deflist)]))

;;;;;;
;; allocate-registers pass.
(define (allocate-registers p)
  (define global-col-dict empty)
  (struct satnode (name satv) #:transparent) ; varname, it saturation value
  (define reg-num
    '( (rax . -1) (rsp . -2) (rbp . -3) (r11 . -4) (r15 . -5)
       (rcx . 0) (rdx . 1) (rsi . 2) (rdi . 3) (r8 . 4) (r9 . 5) (r10 . 6)
       (rbx . 7) (r12 . 8) (r13 . 9) (r14 . 10)))

  (define num-reg
    '( (-1 . rax) (-2 . rsp) (-3 . rbp) (-4 . r11) (-5 . r15 )
       ( 0 . rcx ) ( 1 . rdx) ( 2 . rsi ) ( 3 . rdi) ( 4 . r8) ( 5 . r9 ) ( 6 . r10)
       (7 . rbx ) (8 . r12) (9 . r13 ) ( 10 . r14 )))

  (define callee-saved (set -2 -3 7 8 9 10 -5))
  ; comperator for pq.
  (define (cmp? a b)
  (cond
    [(>= (satnode-satv a) (satnode-satv b)) #t]
    [else #f]))   

  ;following are set of alias for commands
  (define push pqueue-push!)
  (define pop pqueue-pop!)
  (define make-pq make-pqueue)
  (define heapify pqueue-decrease-key!)
  (define pqcount pqueue-count)
  (define set-it set-node-key!)
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; helper functions
  
  (define (init-pq vars myq handle-dict)
    (for ([i vars])
      (define mynode (satnode i 0))
      (set! handle-dict
            (dict-set handle-dict i (push myq mynode))))
    handle-dict)

  (define (init-sat-dict vars sat-dict)
    (for ([i vars])
      (set! sat-dict
            (dict-set sat-dict i (set))))
    sat-dict)

  (define registers (set 'rax 'rbx 'rcx 'rdx 'rdi 'rsi 'rbp 'rsp 'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))
  
  (define (is-reg? i) (set-member? registers i))

  (define (get-colour myset)
    (define (get-colour1 myset x)
      (cond
        [(set-member? myset x) (get-colour1 myset (+ x 1))]
        [else x]))
    (get-colour1 myset 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (modify mygraph)
    (define vars (get-vertices mygraph))
    (define col-dict '())  ;dictionary var - colour
    (define sat-dict '())  ; dictionary var - saturation set
    (define handle-dict '())  ; dictionary var -handle set
    (define myq (make-pq cmp?))  ; priority queue which has satnode as nodes.
    (define var-done (set))  ; contains the variables who have been coloured already.
    
    (set! handle-dict (init-pq vars myq handle-dict))
    (set! sat-dict (init-sat-dict vars sat-dict))

    ;colour the variables and registers which are already coloured in other blocks first.
    (for ([i (dict-keys global-col-dict)])
      (set! col-dict (dict-set col-dict i (dict-ref global-col-dict i)))
      (define col (dict-ref col-dict i))
      (cond
        [(equal? (has-vertex? mygraph i) #f) 0]
        [else
         (define neigh (get-neighbors mygraph i))
         (set! var-done (set-union var-done (set i)))
         (for ([j neigh])
           (cond
                [(set-member? var-done j) 0]
                [else
                 (set! sat-dict (dict-set sat-dict j (set-union (dict-ref sat-dict j) (set col))))
                 (define n (length (set->list (dict-ref sat-dict j))))
                 (set-it (dict-ref handle-dict j) (satnode j n))
                 (heapify myq (dict-ref handle-dict j))]))]))
    
    ;colour the registers first.
    (for ([i vars])
      (cond
        [(is-reg? i)
         (set! col-dict (dict-set col-dict i (dict-ref reg-num i)))
         (define neigh (get-neighbors mygraph i))
         (set! var-done (set-union var-done (set i)))
         (for ([j neigh])
           (cond
             [(set-member? var-done j) 0]
             [else
               (set! sat-dict (dict-set sat-dict j (set-union (dict-ref sat-dict j) (set (dict-ref reg-num i)))))
               (define n (length (set->list (dict-ref sat-dict j))))
               (set-it (dict-ref handle-dict j) (satnode j n))
               (heapify myq (dict-ref handle-dict j))]))]))
    
    ; now color the remaining variables.
    (define (final-step myq)
      (cond
        [(equal? (pqcount myq) 0) 0]
        [else
         (define temp (pop myq))
         (cond
           [(is-reg? (satnode-name temp)) (final-step myq)]
           [(set-member? var-done (satnode-name temp)) (final-step myq)]
           [else
            (define varname (satnode-name temp))
            (define col (get-colour (dict-ref sat-dict varname)))
            (set! col-dict (dict-set col-dict varname col))
            (set! var-done (set-union var-done (set varname)))
            (define neigh (get-neighbors mygraph varname))
            (for ([j neigh])
              ;do this to only those variables which are not coloured already.
              (cond
                [(set-member? var-done j) 0]
                [else
                 (set! sat-dict (dict-set sat-dict j (set-union (dict-ref sat-dict j) (set col))))
                 (define n (length (set->list (dict-ref sat-dict j))))
                 (set-it (dict-ref handle-dict j) (satnode j n))
                 (heapify myq (dict-ref handle-dict j))]))
            (final-step myq)])]))

    (final-step myq)
    col-dict)

  ; now the coloring is done we need to calculate how many callee-saved registers are used.
  (define ( check-callee lst cset ret )
    (cond
      [(empty? lst) ret]
      [else (cond
              [(set-member? cset (car lst)) (check-callee (cdr lst) cset (append ret (list (dict-ref num-reg (car lst)))))]
              [else (check-callee (cdr lst) cset ret)])]))

  
  (define (assign-home instrs colours skip)
    (set! skip (if (equal? (remainder skip 2) 0) skip (+ 1 skip)))
    
    (define (change-it x)
      (match x
        [(Reg reg) (Reg reg)]
        [(Imm int) (Imm int)]
        [(Var t)
         (define num (dict-ref colours t))
         (cond
           [(< num 11) (Reg (dict-ref num-reg num))]  ; if less than 11(registers)
           [else              
                 (set! num (* 8 (+ (- num 10) skip)))
                 (Deref 'rbp (- num))])]))
    
    (define (change-vars lst ret)
      (cond
        [(empty? lst) ret]
        [else (change-vars (cdr lst) (append ret (list (change-it (car lst)))))]))  
    
    
    (define (doit instr)
      (match instr
        [(Jmp label) (list instr)]
        [(JmpIf cc label) (list instr)]
        [(Retq) (list instr)]
        [(Callq label int) (list instr)]
        [(Instr 'set (list cc arg)) (list instr)]
        [(Instr 'movzbq (list arg1 arg2)) (list (Instr 'movzbq (append (list arg1) (change-vars (list arg2) empty))))]
        [(Instr 'leaq lst) (list instr)]
        [(Instr com lst) (list (Instr com (change-vars lst '())))]
        [(TailJmp arg int) (list (TailJmp (change-it arg) int))]
        [(IndirectCallq arg int) (list (IndirectCallq (change-it arg) int))]))
    
    (define (eval-body body lst)
    (cond
      [(empty? body) lst]
      [else (eval-body (cdr body) (append lst (doit (car body))))]))
    
    (eval-body instrs '()))
  

  (define (doit a)
    (match a
      [(Block info instrs)
       (define mygraph (dict-ref info 'conflicts))  ;graph
       (define newinfo (dict-set info 'colours (modify mygraph))) ;this is colour filling
       (define callee-used (check-callee (dict-values (dict-ref newinfo 'colours)) callee-saved '()))
       (set! callee-used (set->list (list->set callee-used))) ;removing duplicates.
       (define skip (length callee-used))       
       (set! global-col-dict (dict-ref newinfo 'colours))
       (define new-instrs (assign-home instrs (dict-ref newinfo 'colours) (- skip 1))) ; this is register allocation

       (define lst (dict-values (dict-ref newinfo 'colours)))
       (define max 0)
       (for ([i lst]) (if ( i . > . max ) (set! max i) (set! max max)))
       (if (max . > . 10) (set! max (- max 10)) (set! max 0))
       (if (equal? (remainder max 2) 0) (set! max (* 8 max)) (set! max (* 8 (+ 1 max))))
       ;(if (equal? (remainder skip 2) 0) (set! skip (* 8 skip)) (set! skip (* 8 (+ 1 skip))))
       
       ;callee-saved will be pushed so rsp will be moved cos of pushq so no need to subtract it explicitly.
       (define newinfo2 (dict-set newinfo 'stack-space (- (+ max 16))))
       (define newinfo3 (dict-set newinfo2 'used-callee callee-used))
       
       (Block newinfo3 new-instrs)]))  

  (define (sort-it def)
    (match def
      [(Def label args type info body-dict)
       (define cfg (dict-ref info 'cfg))
       (define mycfg (reverse (cdr (reverse (tsort cfg)))))
       (define newbody (for/list ([i mycfg]) (cons i (doit (dict-ref body-dict i)))))
       (Def label args type info newbody)]))
  (match p
    [(X86Program info listdefs)
     (define new-listdefs (for/list ([i listdefs]) (sort-it i)))
     (X86Program info new-listdefs)]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; patch-instructions pass

(define (patch-instructions p)

  (define (is-wrong? e)
    (match e
      [(Deref reg int) #t]
      [(Imm int) #t]
      [else #f]))
  
  (define (check-it instr)
    (match instr
      [(Instr com (list e1)) (list instr)]
      [(Instr 'cmpq (list e1 e2))
       (if (is-wrong? e2)
           (list (Instr 'movq (list e2 (Reg 'rax)))
                 (Instr 'cmpq (list e1 (Reg 'rax))))
           (list instr))]
      [(Instr 'movzbq (list e1 e2))
       (if (is-wrong? e2)
           (list (Instr 'movzbq (list e1 (Reg 'rax)))
                 (Instr 'movq (list (Reg 'rax) e2)))
           (list instr))]
      [(Instr com (list e1 e2))
       (cond
         [(and (equal? e1 e2) (equal? com 'movq)) (list)]  ; updated to remove redundant instruction.
         [(and (is-wrong? e1) (is-wrong? e2))
          (list (Instr 'movq (list e1 (Reg 'rax))) (Instr com (list (Reg 'rax) e2)))]
         [else (list instr)])]
      [(TailJmp arg int) (cond
                           [(equal? arg (Reg 'rax)) (TailJmp arg int)]
                           [else (list (Instr 'movq (list arg (Reg 'rax)))
                                       (TailJmp (Reg 'rax) int))])]
      [else (list instr)]))
  
  (define (eval-body lst retlst)
    (cond
      [(empty? lst) retlst]
      [else (eval-body (cdr lst) (append retlst (check-it (car lst))))]))

  (define (get_block info body)
   (match body
     [(Block info abody)
      (Block info (eval-body abody empty))])) ;it shd return list of instructions

  (define (handle-it x)
    (match x
      [(Def label '() type info body)
       (define new-body (for/list ([i (dict-keys body)]) (cons i (get_block info (dict-ref body i)))))
       (Def label '() type info new-body)]))
  
  (match p
    [(X86Program info lstdefs)
     (define newlst (for/list ([i lstdefs]) (handle-it i)))     
     (X86Program info newlst) ]))

;adding prelude and conclude to the final code.
(define (prelude-and-conclude p)

  (define (push-callee-saved used-callee)
    (define (doit lst ret)
      (cond
        [(empty? lst) ret]
        [(equal? (car lst) 'rsp) (doit (cdr lst) ret)]
        [else (doit (cdr lst) (append ret (list (Instr 'pushq (list (Reg (car lst)))))))]))
    (define retlst (doit used-callee '()))
    (cond
      [(equal? 0 (remainder (- (length used-callee) 1) 2)) retlst]
      [else (append retlst (list (Instr 'subq (list (Imm 8) (Reg 'rsp)))))])
    )

  (define (pop-callee-saved used-callee)
    (define (doit lst ret)
      (cond
        [(empty? lst) ret]
        [(equal? (car lst) 'rsp) (doit (cdr lst) ret)]
        [else (doit (cdr lst) (append ret (list (Instr 'popq (list (Reg (car lst)) )))))]))
    (define retlst (cond
      [(equal? 0 (remainder (- (length used-callee) 1) 2)) '()]
      [else (list (Instr 'addq (list (Imm 8) (Reg 'rsp))))]))
    (append retlst (doit (reverse used-callee) '()))   
    )
  
  (define (main_body info label)
    (append
     (list
     (Instr 'pushq (list (Reg 'rbp)))
     (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
     (push-callee-saved (dict-ref info 'used-callee))
     (list
     (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))) ;stack-space is -ve so adding it
     (Jmp (symbol-append label 'start)))))

  (define (conc_body info num reg label)
    (append
     (list
     (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))  ; stack-space is -ve so subtracting it
     (pop-callee-saved (dict-ref info 'used-callee))
     (list
      (Instr 'popq (list (Reg 'rbp)))
      (Retq))))

  (define (new_conc_body info num reg label)
    (append
     (list
     (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))  ; stack-space is -ve so subtracting it
     (pop-callee-saved (dict-ref info 'used-callee))
     (list
      (Instr 'popq (list (Reg 'rbp)))
      (IndirectJmp reg))))
  
  (define (get_main info label)
    (Block '() (main_body info label)))

  (define (get_conclusion info num reg label)
    (cond
      [(equal? num 0) (Block '() (conc_body info num reg label))]
      [else (Block '() (new_conc_body info num reg label))])
    )

  (define (get-info body)
    (match body
      [(Block info lst) info]))
  
  (define (symbol-append s1 s2)
    (define st1 (symbol->string s1))
    (define st2 (symbol->string s2))
    (string->symbol (string-append st1 st2)))

  (define (search-it2 lst ret num reg label)
    (cond
      [(empty? lst) (values num reg ret)]
      [else
       (match (car lst)
         [(Jmp 'conclusion) (search-it2 (cdr lst) (append
                                                   ret
                                                   (list (Jmp (symbol-append label 'conclusion)))) num reg label)]
         [(TailJmp arg int) (search-it2 (cdr lst) (append
                                                   ret
                                                   (list (Jmp (symbol-append label 'conclusion2)))) 1 arg label)]
         [else (search-it2 (cdr lst) (append ret (list (car lst))) num reg label)])]))

  (define (search-it body label)
    (define-values (num reg) (values 0 0))
    (define new-body
      (for/list ([i body])
        
      (match (cdr i)
        [(Block info lstinstrs)
         (define-values (num1 arg1 body2) (search-it2 lstinstrs empty 0 0 label))
         (cond
           [(equal? num1 0) 0]
           [else (set! num num1) (set! reg arg1)])
         
         (cons (car i) (Block info body2))])))
    (values num reg new-body))
  
  (define (handle-it x)
    (match x
      [(Def label '() type info body)
       (define callee-used (set))
       (define stack-space 0)
       (for ([i (dict-keys body)])
        (define temp-dict (get-info (dict-ref body i)))
        (set! callee-used (set-union callee-used (list->set
                                                  (dict-ref temp-dict 'used-callee))))
        (set! stack-space (+ stack-space (dict-ref temp-dict 'stack-space))))
     
       (define my-dict (get-info (cdr (car body))))
       (set! my-dict (dict-set my-dict 'stack-space stack-space))
       (set! my-dict (dict-set my-dict 'used-callee (set->list callee-used)))

       (define-values (num reg upbody) (search-it body label))
       
       (define newbody (append upbody (list (cons label (get_main my-dict label))
                                          (cons (symbol-append label 'conclusion) (get_conclusion my-dict 0 reg label))
                                          (cons (symbol-append label 'conclusion2) (get_conclusion my-dict num reg label)))))
       
       newbody]))
  
  (match p
    [(X86Program info lstdef)
     ;update the start's stackspace to sum of all stack-spaces.
      (define newlst empty)
      (for ([i lstdef]) (set! newlst (append newlst (handle-it i))))
      
      (X86Program info newlst)
    ]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; L-if language passes :

;; shrink pass.
(define (shrink p)
  (define (doit instr)
    (match instr
      [(Prim 'and (list e1 e2)) (If (modify-exp e1) (modify-exp e2) (Bool '#f))]
      [(Prim 'or (list e1 e2)) (If (modify-exp e1) (Bool '#t) (modify-exp e2))]
      [(Prim op lst) (Prim op (for/list ([i lst]) (modify-exp i)))]
      [else instr]))
  
  (define (modify-exp instr)
    (match instr
      [(Int int) (Int int)]
      [(Var var) (Var var)]
      [(Prim op lst) (doit instr)]
      [(Let var exp1 exp2) (Let var (modify-exp exp1) (modify-exp exp2))]
      [(Bool bool) (Bool bool)]
      [(If e1 e2 e3) (If (modify-exp e1) (modify-exp e2) (modify-exp e3))]
      [(Apply fname lst)
       (Apply (modify-exp fname) (for/list ([i lst]) (modify-exp i)))]
      ;[else instr]
      ))

  (define (dodef func)
    (match func
      [(Def label args type info exp)
       (Def label args type info (modify-exp exp))]))
  
  (match p
    [(ProgramDefsExp info defs instr)
     (define mainfunc (Def 'main '() 'Integer '() (modify-exp instr)))
     (define newdefs (for/list ([i defs]) (dodef i)))
     (ProgramDefs info (append newdefs (list mainfunc)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
        ("shrink", shrink, interp-Lfun, type-check-Lfun)
        ("uniquify", uniquify, interp-Lfun, type-check-Lfun)
        ("reveal functions", reveal_functions, interp-Lfun-prime, type-check-Lfun)
        ;("remove-complex-opera*", remove-complex-opera*, interp-Lfun-prime, type-check-Lfun)
        ;("explicate control", explicate-control , interp-Cfun, type-check-Cfun)
        ;("select instructions", select-instructions, #f)
        ;("uncover live", uncover-live, #f)
        ;("build interference", build-interference, #f)
        ;("assign registers", allocate-registers, #f)
        ;("patch instructions", patch-instructions, #f)
        ;("prelude and conclude", prelude-and-conclude, #f)      
     ))
