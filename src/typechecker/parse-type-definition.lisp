(in-package #:coalton-impl/typechecker)

;;;
;;; Parsing type defintions
;;;


(defstruct type-definition
  (name              (required 'name)              :type symbol                 :read-only t)
  (type              (required 'type)              :type ty                     :read-only t)
  (runtime-type      (required 'runtime-type)      :type t                      :read-only t)

  ;; See the fields with the same name on type-entry
  (explicit-repr     (required 'explicit-repr)     :type explicit-repr          :read-only t)
  (enum-repr         (required 'enum-repr)         :type boolean                :read-only t)
  (newtype           (required 'newtype)           :type boolean                :read-only t)

  (constructors      (required 'constructors)      :type constructor-entry-list :read-only t)
  (constructor-types (required 'constructor-types) :type scheme-list            :read-only t)

  (docstring         (required 'docstring)         :type (or null string)       :read-only t))

(defstruct partial-type-definition 
  "A type which is incomplete and still needs to be defined"
  (name         (required 'name)         :type list           :read-only t)
  (docstring    (required 'docstring)    :type (or null string) :read-only t)
  (constructors (required 'constructors) :type list             :read-only t))

(defstruct alias-definition
  "The result of parsing, but not type-checking, a DEFINE-ALIAS form"
  (alias     (required 'alias)     :type cons)
  (docstring (required 'docstring) :type (or null string))
  (aliased   (required 'aliased)   :type (or symbol cons)))

(define-list-of-type type-definition)
(define-list-of-type partial-type-definition)
(define-list-of-type alias-definition)

(defun definition-name (thing)
  (declare (type (or alias-definition partial-type-definition type-definition) thing)
           (values symbol))
  (typecase thing
    (alias-definition        (car (alias-definition-alias thing)))
    (partial-type-definition (car (partial-type-definition-name thing)))
    (type-definition         (type-definition-name thing))))

(defun parse-type-definition (partial-type self-type type-vars ksubs env)
  (declare (type partial-type-definition partial-type)
           (type ty self-type)
           (type list type-vars)
           (type ksubstitution-list ksubs)
           (type environment env)
           (values list list ksubstitution-list))

  (let* ((tyvar-names (cdr (partial-type-definition-name partial-type)))

         (unparsed-ctors (partial-type-definition-constructors partial-type))

         (local-type-vars
           (loop :for tyvar-name :in tyvar-names
                 :collect (list tyvar-name (make-variable (make-kvariable)))))

         (tyvars
           (append
            type-vars
            local-type-vars))

         (constructors
           (loop :for ctor :in unparsed-ctors
                 :for name := (first ctor)
                 :for fields := (rest ctor)
                 :collect (cons
                           name
                           (loop :for field :in fields
                                 :collect (multiple-value-bind (type new-ksubs)
                                              (parse-type-expr env field tyvars ksubs)
                                            (setf ksubs new-ksubs)
                                            (setf ksubs (kunify (kind-of type) kstar ksubs))
                                            type))))))

    ;; Unify the kind of the type with the kind:
    ;; kind(tvar1) -> kind(tvar2) ... -> *
    (setf ksubs (kunify
                 (kind-of self-type)
                 (make-kind-function*
                  (loop :for (name type) :in local-type-vars
                        :collect (kind-of type))
                  kstar)
                 ksubs))

    (values
     constructors
     local-type-vars
     ksubs)))

(defun parse-type-impls (partial-types env)
  "Parse the PARTIAL-TYPES in a single scc"
  (declare (type partial-type-definition-list partial-types)
           (type environment env))

  (let* ((type-names (mapcar #'partial-type-definition-name partial-types))

         (type-vars
           (loop :for type-name :in type-names
                 :collect (list type-name
                                (%make-tcon
                                 (%make-tycon
                                  :name type-name
                                  :kind (make-kvariable))))))

         (ksubs nil)

         (type-constructors
           (loop :for partial-type :in partial-types
                 :for self-type := (second (find (partial-type-definition-name partial-type) type-vars :key #'first))
                 :collect (multiple-value-bind (constructors local-tyvars new-ksubs)
                              (parse-type-definition partial-type self-type type-vars ksubs env)
                            (setf ksubs new-ksubs)
                            (cons constructors local-tyvars)))))

    (values
     (loop :for partial-type :in partial-types
           :for (name type) :in type-vars
           :for (ctors . local-tyvars) :in type-constructors

           :for type_ := (apply-ksubstitution ksubs type)
           :for ksubs_ := (kind-monomorphize-subs (kind-variables type_) ksubs)
           :for type__ := (apply-ksubstitution ksubs_ type)

           :for tyvar-types
             := (loop :for (name tyvar) :in local-tyvars
                      :collect (apply-ksubstitution ksubs_ tyvar))

           :for applied-type
             := (apply-type-argument-list
                 type__
                 tyvar-types)

           ;; Declare the current type in the env. This decleration is incomplete, and is discarded away after parsing
           :do (setf
                env
                (set-type
                 env
                 name 
                 (type-entry
                  :name name
                  :runtime-type name
                  :type type__
                  :explicit-repr nil
                  :enum-repr nil
                  :newtype nil
                  :docstring nil)))

           :collect (list
                     name
                     type__
                     (loop :for (ctor-name . args) :in ctors
                           :for arity := (length args)
                           :for classname := (alexandria:format-symbol
                                              (symbol-package name)
                                              "~A/~A" name ctor-name)
                           :for args_ := (apply-ksubstitution ksubs_ args)
                           :for type := (make-function-type* args_ applied-type)
                           :for scheme := (quantify-using-tvar-order (mapcar #'tvar-tyvar tyvar-types) (qualify nil type))

                           :for entry := (make-constructor-entry
                                          :name ctor-name
                                          :arity arity
                                          :constructs name
                                          :classname classname
                                          :compressed-repr nil)

                           :do (check-constructor name ctor-name env)

                           :do (setf env (set-constructor env ctor-name entry))

                           :collect (cons scheme entry))))
     env)))

(defun check-constructor (ty-name ctor-name env)
  "Verify that a given constructor isn't used by another type"
  (declare (type symbol ty-name)
           (type symbol ctor-name)
           (type environment env))
  
  (with-type-context ("define-type of ~S" ty-name)
   (let ((ctor-entry (lookup-constructor env ctor-name :no-error t)))
     (when (and ctor-entry (not (eq ty-name (constructor-entry-constructs ctor-entry))))
       (error 'duplicate-ctor
              :ctor-name ctor-name
              :ty-name (constructor-entry-constructs ctor-entry))))))

(defmacro assert-parsing (form assertion &body error-arguments)
  "If ASSERTION evaluates to NIL, call ERROR-PARSING as appropriate"
  `(unless ,assertion
     (error-parsing ,form ,@error-arguments)))


(defun parse-define-alias (form)
  (declare (type cons form)
           (values alias-definition symbol-list))
  "Parses a DEFINE-ALIAS form and returns a ALIAS-DEFINITION"
  (assert-parsing form (and (<= 3 (length form) 4)
                            (eq 'coalton:define-alias (first form)))
    "Malformed DEFINE-ALIAS")
  (let* ((alias          (alexandria:ensure-list (second form)))
         (docstring      (and (= (length form) 4) (third form)))
         (aliased        (if docstring (fourth form) (third form))))
    (assert-parsing alias     (non-keyword-symbol-p (first alias)) "Malformed alias name")
    (assert-parsing docstring (typep docstring '(or string null)) "Malformed docstring")
    (check-type-vars alias aliased)
    (values (make-alias-definition :alias alias :docstring docstring :aliased aliased)
            (collect-types aliased))))

(defun parse-define-type (form)
  (declare (type cons form)
           (values partial-type-definition symbol-list))
  "Parses a DEFINE-TYPE and returns a PARTIAL-TYPE-DEFINITION and a list of type names on which it depends"
  (assert-parsing form (and (<= 2 (length form))
                            (eq 'coalton:define-type (first form)))
    "Malformed DEFINE-TYPE")

  (let* ((type         (alexandria:ensure-list (second form)))
         (docstring    (and (stringp (third form)) (third form)))
         (constructors (if docstring (cdddr form)  (cddr form))))

    (with-parsing-context ("definition of type ~A" (first type))
      (assert-parsing type (non-keyword-symbol-p (first type)) "Malformed type name")
      (check-type-vars type constructors)

      (let ((dups (duplicates constructors :key #'car)))
        (unless (null dups)
          (error-parsing dups "Duplicate constructor~P" (length dups)))))

    (values
     (make-partial-type-definition
      :name type
      :constructors constructors :docstring docstring)
     (mapcan (alexandria:compose #'collect-types #'cdr) constructors))))

(defun parse-definition (form)
  (declare (type cons form)
           (values (or partial-type-definition alias-definition)))
  (case (first form)
    ((coalton:define-type)  (parse-define-type form))
    ((coalton:define-alias) (parse-define-alias form))
    (t                      (error-parsing form "Unknown definition operator"))))

(defun parse-type-definitions (forms repr-table env)
  "Parse the type defintion FORM in the ENVironment

Returns TYPE-DEFINITIONS"
  (declare (type list forms)
           (type environment env)
           (values type-definition-list))

  ;; Pull out and verify DEFINE-TYPE and type
  (let (defined-types type-dependencies)
    ;; defined-types is a list of type definition forms
    ;; type dependencies is an association list of type names to that type's dependencies names
    (dolist (form forms)
      (multiple-value-bind (type dependencies) (parse-definition form)
        (push type defined-types)
        (push (cons (definition-name type) dependencies) type-dependencies)))
                            
    (let* ((parsed-tcons
             (loop :for scc :in (reverse (tarjan-scc type-dependencies))
                   :for scc-types
                     := (mapcar (cut find <> type-definitions :key #'definition-name) scc)
                   :for aliases
                     := (remove-if-not #'alias-definition-p scc-types)
                   :for alias-dependencies
                     := (mapcar (lambda (name) (intersection (mapcar #'definition-name aliases)
                                                        (cdr (assoc (definition-name name) type-dependencies))))
                                aliases)
                   :do (dolist (alias-scc (tarjan-scc alias-dependencies))
                         (assert (< (length alias-scc) 2) ()
                                 "Cannot typecheck mutually recursive type aliases ~A" alias-scc)
                         (let ((alias (first alias-scc)))
                           (assert (null (find alias (cdr (assoc alias alias-dependencies)))) ()
                                   "Cannot typecheck recursive type alias ~A" alias)))
                   :append (multiple-value-bind (data new-env)
                               (parse-type-impls partial-types env)
                             (setf env new-env)
                             data))))

      (loop :for (tycon-name tcon ctor-data docstring) :in parsed-tcons
            :collect
            (with-parsing-context ("definition of type ~A" tycon-name)
              
              ;; Parse out the ctors
              (let* ((parsed-ctors (mapcar #'cdr ctor-data))

                     (ctor-types (mapcar #'car ctor-data))

                     ;; If every constructor entry has an arity of 0
                     ;; then this type can be compiled as an enum
                     (enum-type (every
                                 (lambda (ctor)
                                   (zerop (constructor-entry-arity ctor)))
                                 parsed-ctors))

                     ;; If there is a single constructor with a single
                     ;; field then this type can be compiled as a
                     ;; newtype
                     (newtype (and (= 1 (length parsed-ctors))
                                   (= 1 (constructor-entry-arity (first parsed-ctors)))))

                     (repr (car (gethash tycon-name repr-table)))
                     (repr-arg (cdr (gethash tycon-name repr-table))))
                (cond
                  ;; If the type is repr lisp then do *not* attempt to
                  ;; generate an optimized implementation
                  ((eql repr :lisp)
                   (make-type-definition
                    :name tycon-name
                    :type tcon
                    :runtime-type tycon-name
                    :explicit-repr :lisp
                    :enum-repr nil
                    :newtype nil
                    :constructors parsed-ctors
                    :constructor-types ctor-types
                    :docstring docstring))

                  ((eql repr :native)
                   (progn
                     (unless repr-arg
                       (error "Type ~A cannot have native repr of NIL" tycon-name)))
                   (make-type-definition
                    :name tycon-name
                    :type tcon
                    :runtime-type repr-arg
                    :explicit-repr (list repr repr-arg)
                    :enum-repr nil
                    :newtype nil
                    :constructors parsed-ctors
                    :constructor-types ctor-types
                    :docstring docstring))

                  ((or (and newtype (eql repr :transparent))
                       (and newtype (coalton-impl:coalton-release-p)))
                   (let (;; The runtime type of a newtype is the runtime type of it's only constructor's only argument
                         (runtime-type (function-type-from
                                        (qualified-ty-type
                                         (fresh-inst (first ctor-types))))))
                     (make-type-definition
                      :name tycon-name
                      :type tcon
                      :runtime-type runtime-type
                      :explicit-repr repr
                      :enum-repr nil
                      :newtype t
                      :constructors parsed-ctors
                      :constructor-types ctor-types
                      :docstring docstring)))

                  ((and (eql repr :transparent) (not newtype))
                   (error "Type ~A cannot be repr transparent. To be repr transparent a type must have a single constructor with a single field." tycon-name))

                  ((or (and enum-type (eql repr :enum))
                       (and enum-type (coalton-impl:coalton-release-p)))
                   (let ((parsed-ctors (mapcar #'rewrite-ctor parsed-ctors)))
                     (make-type-definition
                      :name tycon-name
                      :type tcon
                      :runtime-type `(member ,@(mapcar #'constructor-entry-compressed-repr parsed-ctors))
                      :explicit-repr repr
                      :enum-repr t
                      :newtype nil
                      :constructors parsed-ctors
                      :constructor-types ctor-types
                      :docstring docstring)))

                  ((and (eql repr :enum) (not enum-type))
                   (error "Type ~A cannot be repr enum. To be repr enum a type must only have constructors without fields." tycon-name))

                  (repr
                   (error "Type ~A supplied an unknown or incompatable repr ~A" tycon-name repr))

                  ((not repr)
                   (make-type-definition
                    :name tycon-name
                    :type tcon
                    :runtime-type tycon-name
                    :explicit-repr nil
                    :enum-repr nil
                    :newtype nil
                    :constructors parsed-ctors
                    :constructor-types ctor-types
                    :docstring docstring)))))))))

(defun rewrite-ctor (ctor)
  (declare (type constructor-entry ctor))
  (assert-parsing ctor (= 0 (constructor-entry-arity ctor)) "Malformed constructor")
  (make-constructor-entry
   :name (constructor-entry-name ctor)
   :arity (constructor-entry-arity ctor)
   :constructs (constructor-entry-constructs ctor)
   :classname (constructor-entry-classname ctor)
   :compressed-repr (constructor-entry-classname ctor)))

(defun quantify-using-tvar-order (tyvars type)
  (let* ((vars (remove-if
                (lambda (x) (not (find x (type-variables type) :test #'equalp)))
                tyvars))
         (kinds (mapcar #'kind-of vars))
         (subst (loop :for var :in vars
                      :for id :from 0
                      :collect (%make-substitution var (%make-tgen id)))))
    (%make-ty-scheme kinds (apply-substitution subst type))))

(defun tvar-count-to-kind (tvar-count)
  "Create a KIND from the number of type variables"
  (if (= 0 tvar-count)
      kStar
      (kFun kStar (tvar-count-to-kind (1- tvar-count)))))
