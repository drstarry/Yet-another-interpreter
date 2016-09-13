#lang plai-typed

(require "class.rkt"
         "inherit.rkt")

(define-type ClassT
  [classT (name : symbol)
          (super-name : symbol)
          (fields : (listof FieldT))
          (methods : (listof MethodT))])

(define-type FieldT
  [fieldT (name : symbol)
          (type : Type)])

(define-type MethodT
  [methodT (name : symbol)
           (arg-type : Type)
           (result-type : Type)
           (body-expr : ExprI)])

(define-type Type
  [numT]
  [objT (class-name : symbol)]
  [nullT])

(module+ test
  (print-only-errors true))

;; ----------------------------------------

(define find-classT
  (make-find classT-name))

(define find-fieldT
  (make-find fieldT-name))

(define find-methodT
  (make-find methodT-name))

(define (type-error a msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string a)
                      (string-append " not "
                                     msg)))))

(define (get-all-field-types class-name t-classes)
  (if (equal? class-name 'object)
      empty        
      (type-case ClassT (find-classT class-name t-classes)
        [classT (name super-name fields methods)
                (append 
                 (get-all-field-types super-name t-classes)
                 (map fieldT-type fields))])))

;; ----------------------------------------

(define (make-find-in-tree find-in-list extract)
  (lambda (name t-class t-classes)
    (local [(define items (extract t-class))
            (define super-name 
              (classT-super-name t-class))]
      (if (equal? super-name 'object)
          (find-in-list name items)
          (try (find-in-list name items)
               (lambda ()
                 ((make-find-in-tree find-in-list extract)
                  name 
                  (find-classT super-name t-classes)
                  t-classes)))))))

(define find-field-in-tree
  (make-find-in-tree find-fieldT classT-fields))

(define find-method-in-tree
  (make-find-in-tree find-methodT classT-methods))

;; ----------------------------------------

(define (is-subclass? name1 name2 t-classes)
  (cond
    [(equal? name1 name2) true]
    [(equal? name1 'object) false]
    [else
     (type-case ClassT (find-classT name1 t-classes)
       [classT (name super-name fields methods)
               (is-subclass? super-name name2 t-classes)])]))

;; p4
(define (ancester name1 name2 t-classes)
  (cond
    [(equal? name1 'object) name1]
    [(equal? name1 name2) name1]
    [else
     (type-case ClassT (find-classT name1 t-classes)
       [classT (name super-name1 fields methods)
               (type-case ClassT (find-classT name2 t-classes)
                 [classT (name super-name2 fields methods)
                         (ancester super-name1 super-name2 t-classes)])])]))

;; p4
(define (level name t-classes level-num)
  (cond
    [(equal? name 'object) level-num]
    [else
     (type-case ClassT (find-classT name t-classes)
       [classT (name super-name fields methods)
               (level super-name t-classes (+ 1 level-num))])]))

;; p4
(define (ancester-n name t-classes level-num)
  (cond
    [(equal? level-num 0) name]
    [else
     (type-case ClassT (find-classT name t-classes)
       [classT (name super-name fields methods)
               (ancester-n super-name t-classes (- level-num 1))])]))

(define (is-subtype? t1 t2 t-classes)
  (type-case Type t1
    [objT (name1)
          (type-case Type t2 
            [objT (name2)
                  (is-subclass? name1 name2 t-classes)]
            [else false])]
    [nullT () true]
    [else (equal? t1 t2)]))

;; p4
(define (lca t1 t2 t-classes)
  (type-case Type t1
    [objT (name1)
          (type-case Type t2 
            [objT (name2)
                  (let ([level1 (level name1 t-classes 0)]
                        [level2 (level name2 t-classes 0)])
                    (cond
                      [(equal? level1 level2) (objT (ancester name1 name2 t-classes))]
                      [(> level1 level2)
                       (let ([delta (- level1 level2)])
                         (let ([name1-a (ancester-n name1 t-classes delta)])
                           (objT (ancester name1-a name2 t-classes))))]
                      [else
                       (let ([delta (- level2 level1)])
                         (let ([name2-a (ancester-n name2 t-classes delta)])
                           (objT (ancester name2-a name1 t-classes))))]))]
            [nullT () t1]
            [else (type-error t2 "object")])]
    [nullT () t2]
    [else (type-error t1 "number")]))

(module+ test
  (define a-t-class (classT 'a 'object empty empty))
  (define b-t-class (classT 'b 'a empty empty))

  (test (is-subclass? 'object 'object empty)
        true)
  (test (is-subclass? 'a 'b (list a-t-class b-t-class))
        false)
  (test (is-subclass? 'b 'a (list a-t-class b-t-class))
        true)
  (test (lca (nullT) (objT 'a) (list a-t-class))
        (objT 'a))
  (test (lca (objT 'a) (nullT) (list a-t-class))
        (objT 'a))
  (test (is-subtype? (numT) (nullT) empty)
        false)
  (test (is-subtype? (nullT) (objT 'object) empty)
        true)
  (test (is-subtype? (objT 'object) (nullT) empty)
        false)
  (test (is-subtype? (numT) (numT) empty)
        true)
  (test (is-subtype? (numT) (objT 'object) empty)
        false)
  (test (is-subtype? (objT 'object) (numT) empty)
        false)
  (test (is-subtype? (objT 'a) (objT 'b) (list a-t-class b-t-class))
        false)
  (test (is-subtype? (objT 'b) (objT 'a) (list a-t-class b-t-class))
        true))

;; ----------------------------------------

(define typecheck-expr : (ExprI (listof ClassT) (-> Type) (-> Type) -> Type)
  (lambda (expr t-classes arg-type this-type)
    (local [(define (recur expr)
              (typecheck-expr expr t-classes arg-type this-type))
            (define (typecheck-nums l r)
              (type-case Type (recur l)
                [numT ()
                      (type-case Type (recur r)
                        [numT () (numT)]
                        [else (type-error r "num")])]
                [else (type-error l "num")]))]
      (type-case ExprI expr
        [numI (n) (numT)]
        [plusI (l r) (typecheck-nums l r)]
        [multI (l r) (typecheck-nums l r)]
        [argI () (arg-type)]
        [thisI () (this-type)]
        [newI (class-name exprs)
              (local [(define arg-types (map recur exprs))
                      (define field-types
                        (get-all-field-types class-name t-classes))]
                (if (and (= (length arg-types) (length field-types))
                         (foldl (lambda (b r) (and r b))
                                true
                                (map2 (lambda (t1 t2) 
                                        (is-subtype? t1 t2 t-classes))
                                      arg-types
                                      field-types)))
                    (objT class-name)
                    (type-error expr "field type mismatch")))]
        [getI (obj-expr field-name)
              (type-case Type (recur obj-expr)
                [objT (class-name)
                      (local [(define t-class
                                (find-classT class-name t-classes))
                              (define field
                                (find-field-in-tree field-name
                                                    t-class
                                                    t-classes))]
                        (type-case FieldT field
                          [fieldT (name type) type]))]
                [else (type-error obj-expr "object")])]
        [sendI (obj-expr method-name arg-expr)
               (local [(define obj-type (recur obj-expr))
                       (define arg-type (recur arg-expr))]
                 (type-case Type obj-type
                   [objT (class-name)
                         (typecheck-send class-name method-name
                                         arg-expr arg-type
                                         t-classes)]
                   [else
                    (type-error obj-expr "object")]))]
        [superI (method-name arg-expr)
                (local [(define arg-type (recur arg-expr))
                        (define this-class
                          (find-classT (objT-class-name (this-type))
                                       t-classes))]
                  (typecheck-send (classT-super-name this-class)
                                  method-name
                                  arg-expr arg-type
                                  t-classes))]
        ;; p2
        [instanceofI (obj-expr class-name)
                     (type-case Type (recur obj-expr)
                       [objT (class-name)
                             (begin
                               (find-classT class-name t-classes)
                               (objT 'a))]
                       [else (type-error obj-expr "object")])]
        ;; p3
        [if0I (con thn els)
              (type-case Type (recur con)
                [numT ()
                      (let ([thn-t (recur thn)]
                            [els-t (recur els)])
                            (cond
                              [(is-subtype? thn-t els-t t-classes) els-t]
                              [(is-subtype? els-t thn-t t-classes) thn-t]
                              [else
                               (type-error thn "object")]))]
                [else (type-error con "number")])]

        ;; p4
        [if0gI (con thn els)
               (type-case Type (recur con)
                 [numT ()
                       (let ([thn-t (recur thn)]
                             [els-t (recur els)])
                         (cond
                           [(is-subtype? thn-t els-t t-classes) els-t]
                           [(is-subtype? els-t thn-t t-classes) thn-t]
                           [else
                            (lca thn-t els-t t-classes)]))]
                 [else (type-error con "number")])]
        ;; p5
        [castI (class1 obj)
              (type-case Type (recur obj)
                [objT (class2)
                      (if (or (is-subclass? class2 class1 t-classes)
                              (is-subclass? class1 class2 t-classes))
                          (objT class1)
                          (type-error obj "object"))]
                [nullT () (objT class1)]
                [numT ()
                      (type-error obj "object")])]

        ;; p7
        [nullI () (nullT)]))))

(define (typecheck-send [class-name : symbol]
                        [method-name : symbol]
                        [arg-expr : ExprI]
                        [arg-type : Type]
                        [t-classes : (listof ClassT)])
  (type-case MethodT (find-method-in-tree
                      method-name
                      (find-classT class-name t-classes)
                      t-classes)
    [methodT (name arg-type-m result-type body-expr)
             (if (is-subtype? arg-type arg-type-m t-classes)
                 result-type
                 (type-error arg-expr (to-string arg-type-m)))]))

(define (typecheck-method [method : MethodT]
                          [this-type : Type]
                          [t-classes : (listof ClassT)]) : ()
  (type-case MethodT method
    [methodT (name arg-type result-type body-expr)
             (if (is-subtype? (typecheck-expr body-expr t-classes
                                              (lambda () arg-type)
                                              (lambda () this-type))
                              result-type
                              t-classes)
                 (values)
                 (type-error body-expr (to-string result-type)))]))

(define (check-override [method : MethodT]
                        [this-class : ClassT]
                        [t-classes : (listof ClassT)])
  (local [(define super-name 
            (classT-super-name this-class))
          (define super-method
            (try
             ;; Look for method in superclass:
             (find-method-in-tree (methodT-name method)
                                  (find-classT super-name t-classes)
                                  t-classes)
             ;; no such method in superclass:
             (lambda () method)))]
    (if (and (equal? (methodT-arg-type method)
                     (methodT-arg-type super-method))
             (equal? (methodT-result-type method)
                     (methodT-result-type super-method)))
        (values)
        (error 'typecheck (string-append
                           "bad override of "
                           (to-string (methodT-name method)))))))

(define (typecheck-class [t-class : ClassT] [t-classes : (listof ClassT)])
  (type-case ClassT t-class
    [classT (name super-name fields methods)
            (map (lambda (m)
                   (begin
                     (typecheck-method m (objT name) t-classes)
                     (check-override m t-class t-classes)))
                 methods)]))

(define (typecheck [a : ExprI] [t-classes : (listof ClassT)]) : Type
  (begin
    (map (lambda (t-class)
           (typecheck-class t-class t-classes))
         t-classes)
    (typecheck-expr a t-classes
                    (lambda () (error 'typecheck "no type"))
                    (lambda () (error 'typecheck "no type")))))

;; ----------------------------------------

(module+ test
  (define posn-t-class
    (classT 'posn 'object
            (list (fieldT 'x (numT)) (fieldT 'y (numT)))
            (list (methodT 'mdist (numT) (numT) 
                           (plusI (getI (thisI) 'x) (getI (thisI) 'y)))
                  (methodT 'addDist (objT 'posn) (numT)
                           (plusI (sendI (thisI) 'mdist (numI 0))
                                  (sendI (argI) 'mdist (numI 0)))))))

  (define non-posn-t-class
    (classT 'non-posn 'object
            (list (fieldT 'none (numT)))
            (list)))

  (define posn3D-t-class 
    (classT 'posn3D 'posn
            (list (fieldT 'z (numT)))
            (list (methodT 'mdist (numT) (numT)
                           (plusI (getI (thisI) 'z) 
                                  (superI 'mdist (argI)))))))

  (define posn-time-t-class 
    (classT 'posn-time 'posn
            (list (fieldT 'time (numT)))
            (list (methodT 'when? (numT) (numT) (getI (thisI) 'time)))))

  (define posn-event-t-class 
    (classT 'posn-event 'posn-time
            (list (fieldT 'interval (numT)))
            (list)))

  (define square-t-class 
    (classT 'square 'object
            (list (fieldT 'topleft (objT 'posn)))
            (list)))
 
  (define (typecheck-posn a)
    (typecheck a
               (list posn-t-class non-posn-t-class posn3D-t-class posn-time-t-class posn-event-t-class square-t-class)))
  
  (define posn27 (newI 'posn (list (numI 2) (numI 7))))
  (define nonposn0 (newI 'non-posn (list (numI 0))))
  (define posn531 (newI 'posn3D (list (numI 5) (numI 3) (numI 1))))
  (define posn5312 (newI 'posn-time (list (numI 5) (numI 3) (numI 12))))
  (define posn53123 (newI 'posn-event (list (numI 5) (numI 3) (numI 12) (numI 3))))

  (test (typecheck-posn (sendI posn27 'mdist (numI 0)))
        (numT))
  (test (typecheck-posn (sendI posn531 'mdist (numI 0)))
        (numT))  
  (test (typecheck-posn (sendI posn531 'addDist posn27))
        (numT))  
  (test (typecheck-posn (sendI posn27 'addDist posn531))
        (numT))

  (test/exn (typecheck-posn (thisI))
             "no type")
  (test/exn (typecheck-posn (argI))
             "no type")
  
  ;; p2
  (test (typecheck-posn (instanceofI posn27 'posn))
        (objT 'a))
  (test/exn (typecheck-posn (instanceofI (numI 12) 'posn))
        "no type")

  ;; p3
  (test/exn (typecheck-posn (if0I posn27 posn27 posn27))
        "no type")
  (test (typecheck-posn (if0I (numI 0) posn27 posn531))
        (objT 'posn))
  (test (typecheck-posn (if0I (numI 0) posn531 posn27))
        (objT 'posn)) 
  (test/exn (typecheck-posn (if0I (numI 0) posn531 posn5312))
        "no type") 

  ;; p4
  (test/exn (typecheck-posn (if0gI posn27 posn27 posn27))
        "no type")
  (test (typecheck-posn (if0gI (numI 0) posn27 posn531))
        (objT 'posn))
  (test (typecheck-posn (if0gI (numI 0) posn531 posn27))
        (objT 'posn))
  (test (typecheck-posn (if0gI (numI 0) posn531 posn5312))
        (objT 'posn))
  (test (typecheck-posn (if0gI (numI 0) posn531 posn53123))
        (objT 'posn))
  (test (typecheck-posn (if0gI (numI 0) posn53123 posn531))
        (objT 'posn))
  (test (typecheck-posn (if0gI (numI 0) posn53123 nonposn0))
        (objT 'object))
  (test/exn (typecheck-posn (if0gI (numI 0) (numI 0) posn531))
        "no type")
  (test/exn (typecheck-posn (if0gI (numI 0) posn531 (numI 0)))
        "no type")
  (test (typecheck-posn (if0gI (numI 0) (numI 0) (numI 0)))
        (numT))

  ;; p5
  (test (typecheck-posn (castI 'posn posn27))
        (objT 'posn))
  (test (typecheck-posn (castI 'posn3D posn27))
        (objT 'posn3D))
  (test/exn (typecheck-posn (castI 'posn3D nonposn0))
        "no type")
  (test/exn (typecheck-posn (castI 'posn (numI 12)))
        "no type")

  (test (typecheck-posn (castI 'posn (nullI)))
        (objT 'posn))
  (test (typecheck-posn (sendI posn27 'addDist (nullI)))
        (numT))
  (test/exn (typecheck-posn (sendI (nullI) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (getI (nullI) 'x))
            "no type")
  
  (test (typecheck-posn (newI 'square (list (newI 'posn (list (numI 0) (numI 1))))))
        (objT 'square))
  (test (typecheck-posn (newI 'square (list (newI 'posn3D (list (numI 0) (numI 1) (numI 3))))))
        (objT 'square))
  
  (test (typecheck (multI (numI 1) (numI 2))
                   empty)
        (numT))

  (test/exn (typecheck-posn (sendI (numI 10) 'mdist (numI 0)))
            "no type")
  (test/exn (typecheck-posn (sendI posn27 'mdist posn27))
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'object empty))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (newI 'object empty) (numI 1))
                       empty)
            "no type")
  (test/exn (typecheck (plusI (numI 1) (newI 'object (list (numI 1))))
                       empty)
            "no type")
  (test/exn (typecheck (getI (numI 1) 'x)
                       empty)
            "no type")
  (test/exn (typecheck (numI 10)
                       (list posn-t-class 
                             (classT 'other 'posn
                                     (list)
                                     (list (methodT 'mdist 
                                                    (objT 'object) (numT)
                                                    (numI 10))))))
            "bad override")
  (test/exn (typecheck-method (methodT 'm (numT) (objT 'object) (numI 0)) (objT 'object) empty)
            "no type")
  (test/exn (typecheck (numI 0)
                       (list square-t-class
                             (classT 'cube 'square
                                     empty
                                     (list
                                      (methodT 'm (numT) (numT)
                                               ;; No such method in superclass:
                                               (superI 'm (numI 0)))))))
            "not found")
)

;; ----------------------------------------

(define strip-types : (ClassT -> ClassI)
  (lambda (t-class)
    (type-case ClassT t-class
      [classT (name super-name fields methods)
              (classI
               name 
               super-name
               (map fieldT-name fields)
               (map (lambda (m)
                      (type-case MethodT m
                        [methodT (name arg-type result-type body-expr)
                                 (methodI name body-expr)]))
                    methods))])))

(define interp-t : (ExprI (listof ClassT) -> Value)
  (lambda (a t-classes)
    (interp-i a
              (map strip-types t-classes))))

(module+ test
  (define (interp-t-posn a)
    (interp-t a
              (list posn-t-class posn3D-t-class)))
  
  (test (interp-t-posn (sendI posn27 'mdist (numI 0)))
        (numV 9))  
  (test (interp-t-posn (sendI posn531 'mdist (numI 0)))
        (numV 9))
  (test (interp-t-posn (sendI posn531 'addDist posn27))
        (numV 18))
  (test (interp-t-posn (sendI posn27 'addDist posn531))
        (numV 18)))
 