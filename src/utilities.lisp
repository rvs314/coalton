;;;; utilities.lisp

(in-package #:coalton-impl/util)

(defmacro debug-log (&rest vars)
  "Log names and values of VARS to standard output"
  `(format t
           ,(format nil "~{~A: ~~A~~%~}" vars)
           ,@vars))

(defmacro debug-tap (var)
  (let ((var-name (gensym)))
    `(let ((,var-name ,var))
       (format t ,(format nil "~A: ~~A~~%" var) ,var-name)
       ,var-name)))

(define-condition coalton-bug (error)
  ((reason :initarg :reason
           :reader coalton-bug-reason)
   (args :initarg :args
         :reader coalton-bug-args))
  (:report (lambda (c s)
             (format s "Internal coalton bug: ~?~%~%If you are seeing this, please file an issue on Github."
                     (coalton-bug-reason c)
                     (coalton-bug-args c)))))

(defun coalton-bug (reason &rest args)
  (error 'coalton-bug
         :reason reason
         :args args))

(defmacro unreachable ()
  "Assert that a branch of code cannot be evaluated in the course of normal execution."
  ;; Ideally, we would *catch* the code-deletion-note condition and signal a
  ;; warning if no such condition was seen (i.e., if SBCL didn't prove the
  ;; (UNREACHABLE) form to be prunable). As far as I can tell, though, that
  ;; requires wrapping the entire containing toplevel form in a HANDLER-BIND,
  ;; which cannot be done by the expansion of an inner macro form.
  '(locally
      #+sbcl (declare (sb-ext:muffle-conditions sb-ext:code-deletion-note))
      (coalton-bug "This error was expected to be unreachable in the Coalton source code.")))

(defun maphash-values-new (function table)
  "Map across the values of a hash-table. Returns a new hash-table with unchanged keys."
  (declare (type function function)
           (type hash-table table))
  (let ((new (make-hash-table)))
    (loop :for k :being :the :hash-keys :of table
          :for v :being :the :hash-values :of table
          :do (setf (gethash k new) (funcall function v)))
    new))

(defun find-symbol? (name package)
  (declare (type string name package)
           (values symbol-list))
  (unless (find-package package)
    (return-from find-symbol?))

  (list (alexandria:ensure-symbol name package)))

(defun required (name)
  "A function to call as a slot initializer when it's required."
  (declare (type symbol name))
  (coalton-bug "A slot ~S (of package ~S) is required but not supplied" name (symbol-package name)))

(defun sexp-fmt (stream object &optional colon-modifier at-modifier)
  "A formatter for qualified S-expressions. Use like

    (format t \"~/coalton-impl::sexp-fmt/\" '(:x y 5))

and it will print a flat S-expression with all symbols qualified."
  (declare (ignore colon-modifier at-modifier))
  (let ((*print-pretty* nil)
        (*package* (find-package "KEYWORD")))
    (prin1 object stream)))

(defmacro include-if (condition &body body)
  `(when ,condition
     (list ,@ (remove nil body))))

(defmacro define-symbol-property (property-accessor)
  "Define an accessor for a symbol property.

Implementation notes: These notes aren't relevant to users of this macro, but are Good To Know.

    * The symbol's property is stored as a part of the symbol's plist.

    * The plist key is just the name of the accessor.
    "
  (check-type property-accessor symbol)
  (let ((symbol (gensym "SYMBOL"))
        (new-value (gensym "NEW-VALUE")))
    `(progn
       (declaim (inline ,property-accessor (setf ,property-accessor)))
       (defun ,property-accessor (,symbol)
         (get ,symbol ',property-accessor))
       (defun (setf ,property-accessor) (,new-value ,symbol)
         (setf (get ,symbol ',property-accessor) ,new-value)))))

(defmacro define-list-of-type (type)
  "Given a symbol naming a type, defines a predicate 'TYPE-LIST-P', which is true IFF the given argument is a proper list where all elements are of TYPE, and a type 'TYPE-LIST', which is a type of all items which satisfy TYPE-LIST-P"
  (check-type type symbol)
  (let* ((type-list   (alexandria:format-symbol T "~A-LIST" type))
         (type-list-p (alexandria:format-symbol T "~A-LIST-P" type)))
    `(progn
       (defun ,type-list-p (item)
         ,(format nil "Returns T IFF ITEM is an proper list whose elements are all of type ~A" type)
         (and (alexandria:proper-list-p item)
              (every (lambda (x) (typep x ',type)) item)))
       (deftype ,type-list ()
         ,(format nil "The type of all proper lists where each element is of type ~A" type)
         '(satisfies ,type-list-p))
       #+(and sbcl coalton-release)
       (declaim
        (sb-ext:freeze-type ,type-list)))))

(define-list-of-type symbol)

(deftype literal-value ()
  "Allowed literal values as Lisp objects."
  '(or integer ratio single-float double-float string character))

#+(and sbcl coalton-release)
(declaim (sb-ext:freeze-type literal-value))

(defun duplicates (items &key (test #'eql) (key #'identity))
  "Returns all of the items in ITEMS for which their KEYS are duplicates according to TEST"
  (remove-if (lambda (item) (= 1 (count item items :test test :key key))) items :key key))


(defmacro cut (fun &rest args)
  "A shorthand form for creating curried procedures, from SRFI 26¹. The best way to see what is does is with examples:

- (cut cons (+ a 1) <>)   ⇔ (lambda (x2) (cons (+ a 1) x2))
- (cut list 1 <> 3 <> 5)  ⇔ (lambda (x2 x4) (list 1 x2 3 x4 5))
- (cut list)              ⇔ (lambda () (list))
- (cut list 1 <> 3 <...>) ⇔ (lambda (x2 &rest xs) (apply #'list 1 x2 3 xs))
- (cut list 1 <...> 2)    ⇔ (lambda (&rest xs) (apply #'list 1 (append xs (list 2))))

See 1: Scheme Request for Implementation (SRFI) 26 - Notation for Specializing Parameters without Currying by Sebastian Egner"
  (check-type fun symbol)
  (let* (lambda-list rest-arg lambda-body)
    (labels ((add-arg (arg)
               (case arg
                 ((<>)    (alexandria:with-gensyms (new-arg)
                            (push new-arg lambda-list)
                            (add-arg new-arg)))
                 ((<...>) (assert (not rest-arg)
                              () "Cannot compile a cut form with multiple <...> arguments")
                          (setf rest-arg (gensym))
                          (push '&rest lambda-list)
                          (push rest-arg lambda-list))
                 (T       (if rest-arg
                              (setf rest-arg `(append ,rest-arg (list ,arg)))
                              (push arg lambda-body))))))

      (mapc #'add-arg args)

      (list 'lambda (reverse lambda-list)
            (if rest-arg
                `(apply (function ,fun) ,@(reverse lambda-body) ,rest-arg)
                `(,fun ,@(reverse lambda-body)))))))

(define-symbol-macro <>    (error "The <> symbol is only valid directly below a CUT form "))
(define-symbol-macro <...> (error "The <...> symbol is only valid directly below a CUT form"))
