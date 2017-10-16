(declaim (optimize (speed 3)))

(defpackage :eval-nld
  (:use :cl)
  (:export :read-trees
	   :eval-nld))

(in-package :eval-nld)

;;; anaphoric macros
(defmacro aif (test then &optional else)
  `(let ((it ,test))
    (declare (ignorable it))
    (if it ,then ,else)))

(defmacro awhen (test &body body)
  `(aif ,test
    (progn ,@body)))

;;; list utils
(declaim (inline single?))
(defun single? (lst) (and (consp lst) (null (cdr lst))))

(declaim (inline get-alist))
(defun get-alist (key alist &key (test #'eql)) (cdr (assoc key alist :test test)))

;;; (multi)set utils
(declaim (inline make-set))
(defun make-set (&key (test 'eql))
  (make-hash-table :test test))

(declaim (inline set-test))
(defun set-test (set)
  (hash-table-test set))

(declaim (inline element?))
(defun element? (x set)
  (nth-value 1 (gethash x set)))

(declaim (inline elements))
(defun elements (set)
  (let ((elts nil))
    (maphash #'(lambda (key val) (declare (ignore val)) (push key elts))
             set)
    elts))

(declaim (inline multiplicity))
(defun multiplicity (x set)
  (car (gethash x set)))

(defun cardinality (set)
  (let ((c 0))
    (declare (integer c))
    (maphash #'(lambda (elt m) (declare (ignore elt)) (incf c (the fixnum (car m))))
             set)
    c))

(declaim (inline push-element!))
(defun push-element! (x set &key (count 1))
  (declare (fixnum count))
  (multiple-value-bind (m present?) (gethash x set)
    (if present?
        (incf (the fixnum (car m)) count)
        (setf (gethash x set) (list count))))
  set)

(defun list->set (lst &key (test 'eql))
  (let ((set (make-set :test test)))
    (dolist (x lst)
      (push-element! x set))
    set))

(defun set-intersection (set1 set2)
  (unless (eq (set-test set1) (set-test set2))
    (error "set-intersection"))

  (let ((new-set (make-set :test (set-test set1)))
        (elements nil))

    (dolist (x (elements set1))
      (when (element? x set2)
        (push x elements)))

    (dolist (x elements)
      (push-element! x new-set :count (min (the fixnum (multiplicity x set1))
                                           (the fixnum (multiplicity x set2)))))

    new-set))

;;; PTB utils
(declaim (inline make-char-buffer))
(defun make-char-buffer nil
  (make-array 0 :element-type 'character :adjustable t :fill-pointer 0))

(declaim (inline push-buffer))
(defun push-char-buffer (x buf)
  (vector-push-extend x buf))

(defun get-char-buffer (buf)
  (let ((str (make-array (length buf) :element-type 'character)))
    (dotimes (i (length buf))
      (setf (char str i) (char buf i)))
    (setf (fill-pointer buf) 0)
    str))

(defun parse-label (label)
  (let ((str (string label))
	(category nil)
	(functions nil)
	(id-index nil)
	(reference-index nil)
	(state :start)
	(buf (make-char-buffer)))

    (if (char= (char str 0) #\-)
	(return-from parse-label
	  (list (cons :category str))))

    (labels
	((extract-info nil
	   (case state
	     (:start
	      (setf category (get-char-buffer buf)))
	     (#\-
	      (let* ((token (get-char-buffer buf))
		     (object (read-from-string token)))
		(cond
		  ((numberp object)
		   (setf id-index object))
		  (t
		   (push token functions)))))
	     (#\=
	      (setf reference-index  (read-from-string (get-char-buffer buf)))))))

      (dotimes (i (length str))
	(cond
	  ((member (char str i) '(#\- #\=) :test #'char=)
	   (extract-info)
	   (setf state (char str i)))
	  (t
	   (push-char-buffer (char str i) buf))))

      (extract-info))

    (delete nil
	    (list (cons :category category)
		  (if functions (cons :functions (nreverse functions)))
		  (if id-index (cons :id-index id-index))
		  (if reference-index (cons :reference-index reference-index))))))

(declaim (inline whitespace?))
(defun whitespace? (x)
  (member x '(#\Linefeed #\Newline #\Page #\Return #\Space #\Tab) :test #'char=))

(defun skip-whitespace (stream)
  (loop
     :while (whitespace? (peek-char nil stream nil #\a))
     :do
     (read-char stream)))

(defun read-terminal (stream)
  (let ((buf (make-array 0 :element-type 'character :adjustable t :fill-pointer 0)))
    (loop
       :while (not (char= (peek-char t stream) #\) ))
       :do
       (if (char= (peek-char t stream) #\\)
	   (read-char stream)
	   (vector-push-extend (read-char stream) buf)))
    buf))

(defun read-label (stream)
  (let ((buf (make-array 0 :element-type 'character :adjustable t :fill-pointer 0)))
    (loop
       :while (not ((lambda (x) (or (whitespace? x) (char= x #\( ))) (peek-char nil stream)))
       :do
       (vector-push-extend (read-char stream) buf))
    buf))

(defun read-tree-aux (stream)

  (skip-whitespace stream)

  (if (char= (read-char stream) #\()

      (let ((root nil)
	    (subtrees nil))

	(skip-whitespace stream)

	(cond
	  ((char= (peek-char nil stream) #\()
	   (setf root "TOP"))
	  (t
	   (setf root (read-label stream))))

	(skip-whitespace stream)

	(cond
	  ((char= (peek-char t stream) #\()
	   (loop
	      :while (not (char= (peek-char t stream) #\)))
	      :do
	      (push (read-tree-aux stream) subtrees))
	   (setf subtrees (nreverse subtrees)))
	  (t
	   (setf subtrees (list (read-terminal stream)))))
	(skip-whitespace stream)
	(read-char stream)
	(cons (intern root *package*) subtrees))

      (error t "error in read-tree.")))

(defparameter +eos+ (gensym))

(defun read-tree (&optional (stream t) (eof-error-p t) eof-value)
  (skip-whitespace stream)
  (if (and (not eof-error-p)
	   (eq (peek-char nil stream nil +eos+) +eos+))
      (return-from read-tree eof-value)
      (read-tree-aux stream)))

(defmacro do-stream-tree ((x stream &optional result-form) &body body)
  (let ((gstrm (gensym)))
    `(let ((,gstrm ,stream))
      (do ((,x))
	  ((eq (setf ,x (read-tree ,gstrm nil +eos+)) +eos+) ,result-form)
	,@body))))

(defmacro do-file-tree ((x path &optional result-form) &body body)
  (let ((gstrm (gensym)))
    `(with-open-file (,gstrm ,path)
      (do-stream-tree (,x ,gstrm ,result-form) ,@body))))

(defun read-trees (file)
  (let ((trees nil))
    (do-file-tree (x file)
      (push x trees))
    (nreverse trees)))

(defun root-label (tree) (car tree))
(defun subtrees (tree) (cdr tree))
(defun preterminal? (tree) (atom (cadr tree)))

(defun terminal (tree)
  (if (preterminal? tree)
      (cadr tree)
      (error "~s is not preterminal tree." tree)))

(defmacro tree-ref (tree &rest indexes)
  (if (null indexes)
      tree
      `(tree-ref (nth ,(car indexes) (subtrees ,tree)) ,@(cdr indexes))))

(defun category (tree)
  (get-alist :category (parse-label (root-label tree))))

(defun index (tree)
  (get-alist :id-index (parse-label (root-label tree))))

;;; string position
(defstruct string-position
  start
  end)

(defun tree=>string-position (tree)
  (let ((table (make-hash-table :test 'eq)))
    (labels
	((traverse (tree start)
	   (declare (fixnum start))
	   (cond
	     ((preterminal? tree)
	      (cond
		((string= "-NONE-" (root-label tree))
		 (setf (gethash tree table)
		       (make-string-position :start start :end start))
		 start)
		(t
		 (setf (gethash tree table)
		       (make-string-position :start start :end (1+ start)))
		 (1+ start))))
	     (t
	      (let ((i start))
		(dolist (x (subtrees tree))
		  (setf i (traverse x i)))
		(setf (gethash tree table)
		      (make-string-position :start start :end i))
		i)))))
      (traverse tree 0)
      table)))

;;; empty element
(defun none? (tree)
  (equal (category tree) "-NONE-"))

(defun none-type (tree)
  (and (none? tree)
       (get-alist :category (parse-label (terminal tree)))))

(defun none-index (tree)
  (and (none? tree)
       (get-alist :id-index (parse-label (terminal tree)))))

;;; SBAR-S
(defun SBAR-S? (tree)
  (and (string= (category tree) "SBAR")
       (= (length (subtrees tree)) 2)
       (let ((1st (nth 0 (subtrees tree)))
	     (2nd (nth 1 (subtrees tree))))
	 (and (none? 1st)
	      (string= (none-type 1st) "0")
	      (empty-element? 2nd)
	      (string= (category 2nd) "S")
	      ))))

(defun empty-element? (tree &key SBAR-S)
  (or (and (not (preterminal? tree))
	   (single? (subtrees tree))
	   (none? (tree-ref tree 0)))

      (and SBAR-S
	   (SBAR-S? tree))

      (and (preterminal? tree)
	   (none? tree))))

(defun empty-element-type (tree)
  (or (and (not (preterminal? tree))
	   (single? (subtrees tree))
	   (none-type (tree-ref tree 0)))
      (and (preterminal? tree)
	   (none? tree)
	   (none-type tree))))

(defun empty-element-index (tree)
  (or (and (SBAR-S? tree)
	   (none-index (tree-ref tree 1 0)))
      (and (not (preterminal? tree))
	   (single? (subtrees tree))
	   (none-index (tree-ref tree 0)))))

(defun empty-elements (tree &key SBAR-S)
  (cond
    ((empty-element? tree :SBAR-S SBAR-S)
     (list tree))
    ((preterminal? tree)
     nil)
    (t
     (mapcan #'(lambda (x) (empty-elements x :SBAR-S SBAR-S))
	     (subtrees tree)))))

;;; co-indexed element
(defun index=>tree (tree)
  (let ((table (make-hash-table)))
    (labels
	((traverse (tree)
	   (cond
	     ((preterminal? tree)
	      nil)
	     (t
	      (awhen (index tree)
		(setf (gethash it table) tree))
	      (dolist (x (subtrees tree))
		(traverse x))))))
      (traverse tree)
      table)))

;;; constituent
(defstruct constituent
  category
  position)

;;; nonlocal dependency
(defstruct nonlocal-dependency
  empty-constituent
  co-indexed-constituent)

(defun extract-nonlocal-dependencies (tree &key SBAR-S)
  (let ((tree=>string-position (tree=>string-position tree))
	(index=>tree (index=>tree tree))
	(result nil))
    (labels
	((empty-element=>constituent (tree)
	   (cond
	     ((SBAR-S? tree)
	      (make-constituent :category (list "SBAR-S" (empty-element-type (tree-ref tree 1)))
				:position (gethash tree tree=>string-position)))
	     (t
	      (make-constituent :category (list (category tree) (empty-element-type tree))
				:position (gethash tree tree=>string-position)))))

	 (tree=>constituent (tree)
	   (cond
	     (tree
	      (make-constituent :category (category tree)
				:position (gethash tree tree=>string-position)))
	     (t
	      nil))))

      (dolist (x (empty-elements tree :SBAR-S SBAR-S))
	(push
	 (make-nonlocal-dependency :empty-constituent
				   (empty-element=>constituent x)
				   :co-indexed-constituent
				   (tree=>constituent (gethash (empty-element-index x) index=>tree)))
	 result)))
    result))

(defun f-value (p r)
  (cond
    ((and (zerop p) (zerop r))
     0.0)
    (t
     (/ (* 2.0 p r) (+ p r)))))

;;; evaluation
(defun nonlocal-dependency->empty-terminal (x)
  (make-nonlocal-dependency :empty-constituent
			    (make-constituent :category (list "" (nth 1 (constituent-category (nonlocal-dependency-empty-constituent x))))
					      :position (constituent-position (nonlocal-dependency-empty-constituent x)))))

(defun nonlocal-dependency->empty-element (x)
  (make-nonlocal-dependency :empty-constituent (nonlocal-dependency-empty-constituent x)))

(defun eval-nld (gold-trees test-trees &key (target :full) SBAR-S (output t))
  (let ((all-types (make-set :test 'equal))
	(gold-test-types (make-set :test 'equal))
	(gold-types (make-set :test 'equal))
	(test-types (make-set :test 'equal)))

    (loop
       :for gold-tree :in gold-trees
       :for test-tree :in test-trees
       :do
       (let ((gold-nonlocal-dependencies (extract-nonlocal-dependencies gold-tree :SBAR-S SBAR-S))
	     (test-nonlocal-dependencies (extract-nonlocal-dependencies test-tree :SBAR-S SBAR-S)))
	 (cond
	   ((eq target :empty-terminal)
	    (setf gold-nonlocal-dependencies
		  (mapcar #'nonlocal-dependency->empty-terminal gold-nonlocal-dependencies))
	    (setf test-nonlocal-dependencies
		  (mapcar #'nonlocal-dependency->empty-terminal test-nonlocal-dependencies)))

	   ((eq target :empty-element)
	    (setf gold-nonlocal-dependencies
		  (mapcar #'nonlocal-dependency->empty-element gold-nonlocal-dependencies))
	    (setf test-nonlocal-dependencies
		  (mapcar #'nonlocal-dependency->empty-element test-nonlocal-dependencies))))

	 (labels
	     ((type (x)
		(cons (aif (nonlocal-dependency-co-indexed-constituent x) (constituent-category it))
		      (constituent-category (nonlocal-dependency-empty-constituent x))))

	      (target? (x)
		(cond
		  ((eq target :dependency)
		   (nonlocal-dependency-co-indexed-constituent x))
		  (t
		   t))))

	   (dolist (x gold-nonlocal-dependencies)
	     (when (target? x)
	       (push-element! (type x) gold-types)
	       (push-element! (type x) all-types)))

	   (dolist (x test-nonlocal-dependencies)
	     (when (target? x)
	       (push-element! (type x) test-types)
	       (push-element! (type x) all-types)))

	   (let ((intersection (set-intersection (list->set gold-nonlocal-dependencies :test 'equalp)
						 (list->set test-nonlocal-dependencies :test 'equalp))))
	     (dolist (x (elements intersection))
	       (when (target? x)
		 (push-element! (type x) gold-test-types :count (multiplicity x intersection))))))))

    ;; Result
    (labels
	((arrange-string (x n)
	   (concatenate 'string x (make-string (- n (length x)) :initial-element #\ ))))

      (format output "~%~%")
      (format output "filler ee cat type                      prec.   rec. f-val.~%")
      (format output "-----------------------------------------------------------~%")
      (dolist (x (sort (elements all-types) #'> :key #'(lambda (x) (or (multiplicity x gold-types) 0))))
	(let ((precision 0.0)
	      (recall 0.0))
	  (when (multiplicity x test-types)
	    (setf precision
		  (/ (float (or (multiplicity x gold-test-types) 0))
		     (multiplicity x test-types))))

	  (when (multiplicity x gold-types)
	    (setf recall
		  (/ (float (or (multiplicity x gold-test-types) 0))
		     (multiplicity x gold-types))))

	  (format output "~a ~a ~a: ~5d ~5d ~5d ~6,4f ~6,4f ~6,4f~%"
		  (arrange-string (nth 0 x) 6)
		  (arrange-string (nth 1 x) 6)
		  (arrange-string (nth 2 x) 5)
		  (or (multiplicity x gold-types) 0)
		  (or (multiplicity x test-types) 0)
		  (or (multiplicity x gold-test-types) 0)
		  precision
		  recall
		  (f-value precision recall)))))

    (let ((precision 0.0)
	  (recall 0.0)
	  (f 0.0))
      (setf precision
	    (/ (float (cardinality gold-test-types))
	       (cardinality test-types)))
      (setf recall
	    (/ (float (cardinality gold-test-types))
	       (cardinality gold-types)))
      (setf f (f-value precision recall))
      (format output "precision = ~f~%" precision)
      (format output "recall = ~f~%" recall)
      (format output "f-value = ~f~%" f)
      f)))
