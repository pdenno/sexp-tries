
(ns trie-logic.core
  "Essential parts of trie-db"
  (:use clojure.pprint)
  (:require [pod-utils.core :as pod]) ; POD probably don't want to do this
  (:require [ctries.clj :as ct]))

;(use 'clojure-inspector) ; inspect, inspect-tree, inspect-table
;(use 'clojure.pprint); 

(def ^:dynamic *zippy* nil) ; for diagnostics

;;; ==== Management of Databases =====
(def ^{:dynamic true :private true :doc "A map of DBs"} *the-databases*  (ct/concurrent-map))

(defn- new-db 
  "Add a database named NAME. If one exists, "
  []
  {:roots (ct/concurrent-map)
   :indecies (ct/concurrent-map)})

(defn- find-db 
  "Lookup a database by name, which can be any map index value."
  [db-name]
  (get *the-databases* db-name))

;;; ==== Single 'Object' =====
;; As of Clojure 1.3, vars need to be explicitly marked as ^:dynamic in order for
;; them to be dynamically rebindable. (That is, in order for binding to be used.)
(def ^:dynamic *trie-db* nil)

(defn- get-roots [db]
  (:roots db))

(defn- add-root! [db key val]
  (assoc! (get db :roots) key val))

(defn- clear-tries 
  "Remove all the tries for all the predicates."
  []
  (cl-format *out* "Clearing trie DB!")
  (assoc! *trie-db* :roots (ct/concurrent-map)))

(def ^{:dynamic true, :doc "Used to hold position in search in case continuing"}
  *last-trie* nil)

(defmacro with-trie-db 
  "Macro to bind use the argument trie database, DB"
  [[db-name] & body]
  (let [db (gensym "db")] 
    `(let [~db (get *the-databases* ~db-name)]
       (when-not ~db (pod/error "No such trie db: %s" ~db-name))
       (binding [*trie-db* ~db]
         ~@body))))

(defn ensure-trie-db 
  "Make a trie database, or if one already exists by this DB-NAME, clear it."
  [db-name]
  (assoc! *the-databases* db-name (new-db))
  (get *the-databases* db-name))

;;;================= Trie ========================
(defn- new-trie [] (ct/concurrent-map :value nil :arcs (ct/concurrent-map) :clauses [])) ; pod outer c-m not necessary if set value

;;; POD clj equivalent of inline? 
(defn- arc-key [arc] (first arc))
(defn- arc-trie [arc] (rest arc))
(defn- trie-arcs [tr] (get tr :arcs))
(defn- trie-value [tr] (get tr :value))
(defn- trie-set-value  [tr val] (assoc! tr :value val))
(defn- trie-add-arc [tr key val] (assoc! (get tr :arcs) key val))
(defn- trie-rem-arc  [tr key] (dissoc! (get tr :arvs) key))
(defn- trie-clauses [tr] (get tr :clauses))
(defn- trie-add-clause [tr val] (assoc! tr :clauses (conj (get tr :clauses) val)))

(defn describe-trie [tr]
  (cl-format *out* "~A: value: ~A arcs: ~A" tr (trie-value tr) (trie-arcs tr)))

;;; POD there is probably something like this in clojure already...
(defn- subst
  "Replace OLD with NEW in the sequence TREE."
  [new old tree]
  (cond (= tree old) new
	(not (seq? tree)) tree
	:else (map #(subst new old %) tree)))

;;; POD clj macrolet? POD Had to pass in tb. Otherwise was confused on namespace!!!
(defmacro var-conj [tb x] `(var-set ~tb (conj (var-get ~tb) ~x)))

(defn- serialize
  "Flatten out a list replacing open and close parentheses with symbols openp and closep.
   Returns a vector. "
  [input]
  (letfn [(s-internal [input]
            (if (seq? input) 
              `(openp ~@(map s-internal input) closep) ; POD backquote looks for interned symbol, OK?
              input))]
    ; POD Yeah, the butlast but no rest is a quirk...
    (butlast (flatten (s-internal input)))))

(defn- 
  trie-arcs-lookup 
  "Find the trie at key in the argument trie. Trie arcs might be an alist or ht.
   Key can be a object or list of objects with balanced :o and :c."
  [key trie]
  (let [arcs (when trie (trie-arcs trie))]
    (cond (nil? trie) nil
          (nil? key) trie
          (not (coll? key)) (get arcs key)
          :else (trie-arcs-lookup (rest key)
                                  (trie-arcs-lookup (first key) trie)))))
(defn- trie-arcs-push 
   "Add a new trie at KEY."
   [child-trie key parent-trie]
   (trie-add-arc parent-trie key child-trie))

(defn- trie-arcs-pop 
  "Remove the arc at KEY."
  [key trie]
  (trie-rem-arc trie key))

#_(defn- qvar-versions 
  "Exported function to return N qvar symbols named ?PREFIX, (defaults to 'X') 
   interned in PACKAGE (defaults to *package*)."
  [n &key (prefix "?X") (package *package*)]
  (loop for i from 1 to n
	for var = (intern (cl-format nil "~A~A" prefix i) (find-package package))
	do (setf (get var 'qvar) t)
	collect var))
  
#_(defn- db-predicates 
  "Exported function returning the predicates hash table or a list of predicates
   and their arity (of course, arity isn't fixed, but often constant)."
  [&key symbol.arity]
  (unless symbol.arity (return-from db-predicates (get-roots *trie-db*)))
  (loop for pred being the hash-key of (get-roots *trie-db*)
	collect (cons pred
		      (loop for i from 1 to 6
			    when (trie-query `(~pred ~@(qvar-versions i :package (find-package :trie))))
			    return i))))

#_(defn- show-db 
  "Write content to STREAM."
  [&key pred (stream *out*) (pre-write "--- ") (post-write "")]
  (let [query-vars (map #((qvar-versions % :package (find-package :trie))) '(0 1 2 3 4 5 6))]
    (if pred
	(loop for qvars in query-vars
	      for query = `(~pred ~@qvars) do
	      (loop for term in (trie-query-all query) 
		    do (cl-format stream "~%~A~S~A" pre-write term post-write)))
	(let ((preds (sort (loop for key being the hash-key of (get-roots *trie-db*) collect key) #'string<)))
	  (loop for pred in preds do
		(loop for qvars in query-vars
		      for query = `(~pred ~@qvars) do
		      (loop for term in (trie-query-all query) 
			    do (cl-format stream "~%~A~S~A" pre-write term post-write))))))))

#_(defn write-db 
  "Write a trie-db to STREAM, suitable for re-reading."
  [&key (stream *out*)]
  (cl-format stream ";;; Output of trie-db content generated ~A" (now))
  (cl-format stream "~2%(ensure-trie-db ~S)"  (name *trie-db*))
  (cl-format stream "~%(with-trie-db (~S)" (name *trie-db*))
  (show-db :stream stream :pre-write "  (trie-add '" :post-write ")")
  (cl-format stream ")"))

(defn- ensure-trie 
  "Get or make a trie for this predicate (the symbol at the car of the list)."
  [predicate]
  (pod/VARS *trie-db* predicate)
  (or (get (get-roots *trie-db*) predicate)
      (let [tr (new-trie)]
        (add-root! *trie-db* predicate tr)
        tr)))

;;; POD clj inline?
(defn- predsym [relation] (first relation))

(defn- follow-arc-adding 
  "Find the trie node for this component of the key. Make a new node if needed."
  [component tr]
  ;(declare #|(type trie tr) (type (or symbol string number k:skolem-fn) component)|#)
  (or
    (trie-arcs-lookup component tr)
    (let [child-trie (new-trie)]
      (trie-arcs-push child-trie component tr)
      child-trie)))

(defn- find-trie-adding 
  "Find the trie node for this key. Make a new node if needed."
  [tbuf root]
  (with-local-vars [trie (follow-arc-adding (first tbuf) root)]
    (doseq [elem (rest tbuf)]
      (var-set trie (follow-arc-adding elem (var-get trie))))
    (var-get trie)))

;;; ----------   Adding ---------------------------
(defn- trie-add 
  "Toplevel function: Set the value of the key in trie."
  [key & [clause-ix]]
  (when (not (symbol? (first key))) 
    (pod/error "Malformed predicate: %s" key))
  (let [root (ensure-trie (predsym key))
        key (subst 'special-value-nil nil key)
        tbuf (serialize key)
        trie (find-trie-adding tbuf root)]
    (pod/VARS key tbuf trie)
    (reset! *zippy* trie)
    (if trie 
	(do (trie-set-value trie key)
            (trie-add-clause trie clause-ix))
	(pod/error "trie-add failed on key=%s, clause-ix=%s" key clause-ix))
    trie))

#_(def *trie-trace* nil "collects path of tries for delete processing") ; POD NYI

;;; ----------   Removing ---------------------------
;(defn- trie-remove 
;  "Toplevel function to delete a term." 
;  [key] ; something more will be necessary for removing clause index ? see trie-delete below
;  (when-let [root (gethash (predsym key) (:roots *trie-db*))]
;    (setf *trie-trace* nil)
;    (let [key (subst 'special-value-nil nil key)
;	  tbuf (serialize key)
;	  array (termbuf-arr tbuf)]
;      ;(declare (type termbuf tbuf))
;      (when-let [trie (find-trie-tracing tbuf root)] ; else no such thing stored.
;	(unless (equal key (trie-value trie)) (pod/error "tries inconsistent.")) ; pod useless test?
;	(pop *trie-trace*) ; last one is trie with value = key. 
;	(loop for i from (1- (termbuf-fill-pointer tbuf)) downto 0
;	      for val = (aref array i) 
;	      for trie in *trie-trace* do 
;	      (trie-arcs-pop val trie)
;	      when (trie-arcs trie) return nil))))) ; trie-arcs non-nil means other uses.


#_(defn- follow-arc-tracing 
  "Find the trie node for this component of the key. Make a new node if needed."
  [component tr]
  (let ((tr (trie-arcs-lookup component tr)))
    ;(push tr *trie-trace*) ;POD NYI
    tr))

#_(defn- find-trie-tracing 
  "Find the trie node for this key. Make a new node if needed."
  [tbuf root]
  (let [arr (termbuf-arr tbuf)]
    (loop for i from 1 to (foo1- (termbuf-fill-pointer tbuf)) 
          for tr = (follow-arc-tracing (aref arr 1) root) then 
                   (follow-arc-tracing (aref arr i) tr)
          finally (return tr))))

;;; ----------   Query ---------------------------
#_(defvar +trie-bindings+ nil "An assoc list of a variable and a bind-rec. 
                             Represents the binding of that variable.")

#_(defstruct bind-rec
  (path nil)       ;; a list of indecies (fixnum or arcs-position) that navigate from the root to the binding value.
  (tbuf-ix nil)    ;; the index in the key where this navigation starts
  (root nil))      ;; the trie where navigation starts.

#_(defstruct arcs-position
  "A structure that represents a value in the list of positions of a 
   bind-rec-path slot. It is used for this value only in cases 
   where the trie's arcs stores a hash table."
  (arr nil)  ;; array of keys from trie-arcs
  (ptr 0))   ;; a position in the arr array, selecting a key.

#_(defn- new-arcs-position 
  [arcs]
  (make-arcs-position 
   :arr (make-array (hash-table-count arcs)
                    :initial-contents
                    (loop for k being the hash-key of arcs collect k))))

;;; NOTE: This is not thread-safe. The arcs-position thing assumes the arcs 
;;; have not been update during its existence.
#_(defn- nth-arc 
  "Return the 'nth arc' (that is (key . trie)) from the assoc list or hashtable arcs.
   If arcs is a hash-table n will be a arcs-position, and return
   ((arcs-position-ptr n) . (gethash (arcs-position-ptr n))) where the car of that cons 
   is a key and the cdr is a trie -- just like lisp nth on trie-arcs."
  [n arcs]
  (declare (type (or fixnum arcs-position) n) (type (or list hash-table) arcs))
  (if (hash-table-p arcs)
    (when (< (arcs-position-ptr n) (array-total-size (arcs-position-arr n)))
      (let ((key (aref (arcs-position-arr n) (arcs-position-ptr n))))
        (cons key (gethash key arcs))))
    (nth n arcs)))

;(defn- path-incf 
;  "Increment the argument, which is a position in a trie navigation."
;  [n]
;  (cond (numberp n) (1+ n)
;        :else (incf (arcs-position-ptr n)) n))

#_(defn- path-n+1-p 
  "Return true if the path is not exhausted at position n."
  [n arcs]
  (declare (type (or fixnum arcs-position) n))
  (if (hash-table-p arcs) ; don't really care
    (> (array-total-size (arcs-position-arr n)) (foo1+ (arcs-position-ptr n)))
    (nth (foo1+ n) arcs)))

(defn- qvar? [x] (re-find #"^\?.*" (str x)))

#_(defn- trie-clear-history 
  []
  (setf +trie-bindings+ nil))

#_(defn- find-trie 
  "Find the trie node for this key."
  [tbuf iptr trie]
  (when (not trie) (throw 'query-done nil))
  (loop 
     (let ((key (aref (termbuf-arr tbuf) iptr)))
       (cond (= iptr (termbuf-fill-pointer tbuf)) ; reached end of terms and key.
             (if (trie-value trie) ; since this is nil unless fully closed, good test.
               (throw 'query-done trie)
               (let [[niptr ntrie]] (trie-pop-state nil) ; backtrack (variable arity?)
                                        ;(break "backtracking") (cl-format t "~% backtracking") 
                    (setf iptr niptr trie ntrie)))
             (not (qvar? key))
             (if-let  [answer (trie-arcs-lookup key trie)]
                      (setf trie answer iptr (inc iptr))
                      (let [[niptr ntrie]] (trie-pop-state nil) ; Backtrack to new value for last key.
                           (setf iptr niptr trie ntrie)))
             (not (trie-var-bound-p key))
             (cond (trie-push-state key iptr trie) 
                   true ; clj
                   :else
                   (let [niptr ntrie] (trie-pop-state key) ; ...backtrack to new value of that key.
                        ;;(cl-format t "~%backtracking iptr = ~A" iptr) (break "backtracking") 
                        (setf iptr niptr trie ntrie)))
             (when-let [found (trie-arcs-lookup (bind-val key) trie)] ;It is a var key. Check one val.
               (incf iptr) (setf trie found))
             nil ;clj
             :else
             (let [niptr ntrie] (trie-pop-state key) ; ...backtrack to new value of that key.
                  ;;(cl-format t "~%backtracking iptr = ~A" iptr) (break "backtracking") 
                  (setf iptr niptr trie ntrie))))))

(defn trie-query 
  "Toplevel function: If the key identifies a trie, return it."
  [key]
  (let [pred (predsym key)
        tr (get (get-roots *trie-db*) pred)
        tbuf (serialize (subst 'special-value-nil nil key))] ; 15 removed trie-query-pre here
    (find-trie tbuf 1 tr)
    (when tr
      (when-let [found (find-trie tbuf 1 tr)]
        (set! *last-trie* found)
        (subst nil 'special-value-nil (trie-value found))))))

;;; POD Messy. Use of +termbuf+
#_(defn trie-query-next 
  "Get the next trie. Use it after calling trie-query or itself."
  []
  (when-let [found (catch 'query-done (find-trie +termbuf+ 1 *last-trie*))]
             (setf *last-trie* found)
             (subst nil 'special-value-nil (trie-value found))))

#_(defn- trie-query-all 
  "Toplevel function: return a list of all values found."
  [key]
  (declare (type list key))
  (let* ((pred (predsym key))
         (root (gethash pred (:roots @*trie-db*)))
         (tbuf (trie-query-pre key)))
    ;; By starting at iptr = 1 you skip the outer :o (outer :c was not added)
    ;; so a termbuf-arr for (a ?x) looks like #(:o a ?x t t t ...)
    (loop for tr = (catch 'query-done (find-trie tbuf 1 root))
              then (catch 'query-done 
                     (mvb (iptr trie) (trie-pop-state (caar +trie-bindings+))
                       (find-trie tbuf iptr trie)))
              while tr collect (subst nil 'special-value-nil (trie-value tr)))))

#_(defn- trie-var-bound-p (key)
  "Return true if the variable is bound."
  (assoc key +trie-bindings+))

#_(defn- balance-parens 
  "The argument trie opened count parentheses at index ix. Navigate chosing
   the first arc of every node until parentheses are balanced."
  [root path]
  (letfn [(ix-first-arc [tr]
           (if (listp (trie-arcs tr)) 0 (new-arcs-position (trie-arcs tr))))]
    (mvb (followed-to count) (follow-path root path)
      (let [path-adds
            (loop until (zerop count)
                  for ix = (ix-first-arc followed-to) then (ix-first-arc tr)
                  for (val . tr) = (nth-arc ix (trie-arcs followed-to)) then (nth-arc ix (trie-arcs tr))
                  if (eql val 'trie-core/openp) do (incf count)
                  else if (eql val 'trie-core/closep) do (decf count)
                  collect ix into result
                  finally (return result))]
        (append path path-adds)))))

#_(defn- trie-push-state (var iptr root)
  "Save the state consisting of a variable (pointed at by tbuf-ix), the trie
   where the program is about to choose to bind the variable, and a path from
   that point that balances the parentheses."
  (declare (type symbol var) (type trie root))
  (declare (values))
  (when-let [arcs (trie-arcs root)] ; otherwise this root is terminal, will have to backtrack.
    (let ((first-step (if (hash-table-p arcs) (new-arcs-position arcs) 0)))
      (push (cons var (make-bind-rec  
                       :path (balance-parens root (list first-step))
                       :tbuf-ix iptr
                       :root root))
            +trie-bindings+))))

#_(defn- follow-path (root path)
  "Return (values <destination trie> <open paren count>) that is 
   the result of following the path."
  (if (null path) 
    (values root 0)
    (let ((open-count 0))
      (loop for step in path
         for (val . tr) = (nth-arc step (trie-arcs root)) 
         then (nth-arc step (trie-arcs tr))
         if (eql val 'trie-core/openp) do (incf open-count)
         else if (eql val 'trie-core/closep) do (decf open-count)
         finally (return (values tr open-count))))))

#_(defn- navigate-next (root path)
  "Return the index (list of positions) to the next value in the arcs of the argument trie, or nil."
  (when-let [newpath
              (loop for short-path on path by #'butlast ; progressively shorten path
                 for old-last = (last short-path)
                 for path-end = (follow-path root (butlast short-path))
                 when (path-n+1-p old-last (trie-arcs path-end))
                 return (append (butlast short-path) (list (path-incf old-last))))]
    (balance-parens root newpath)))
            
;;; The current binding for the variable failed. (current = top of stack)
;;; If there are more values to try for variable, pop the failed one off b-rec-vals and continue,
;;; otherwise, pop the whole variable and continue.    inline new 2005-03-12
#_(defn- trie-pop-state 
  [var]
  (let (nav)
    (cond (null +trie-bindings+) (throw 'query-done nil) ; failure (the only exit in code)
          (and (null var)
               (when-let [br (cdar +trie-bindings+)]
                          (setf nav (navigate-next (bind-rec-root br) (bind-rec-path br))))) ; values remain
          (when-let [br (cdar +trie-bindings+)] ; 2013-02-04 was a let -- actual problem is probably concurrency!
                     (setf (bind-rec-path br) nav)
                     (values (bind-rec-tbuf-ix br) 
                             (bind-rec-root br)))
          var ; pop all the way back to argument variable
          (do (loop for binding-rest on +trie-bindings+
                    when (eql var (car binding-rest))
                    return (setf +trie-bindings+ binding-rest))
              (trie-pop-state nil))
          :else ; All bindings of top variable failed...
          (do (pop +trie-bindings+) 
              (trie-pop-state nil)))))

;;; POD This could probably be cleaned up to use follow path
#_(defn- bind-val 
  "Return the value currently bound to the argument variable.
   If the variable is bound to a list, (indicated by the first value being :o, return the 
   whole :o blah blah :c thing."
  [var]
  (when-let [br (cdr (assoc var +trie-bindings+))] ; 2013-02-04 was part of let*
    (let* ((root (bind-rec-root br))
	   (path  (bind-rec-path br))
	   (result
	    (loop with count = 0
	       for ix in path
	       for (key . tr) = (nth-arc ix (trie-arcs root)) then (nth-arc ix (trie-arcs tr))
	       collect key
	       if (eql key 'trie-core/openp) do (incf count)
	       else if (eql key 'trie-core/closep) do (decf count)
	       until (zerop count))))
          (if (eql (first result) 'trie-core/openp)
            result ; it is bound to a list
            (last result))))) ; it is bound to a non-collection.

#_(defn- diag-current-bindings ()
  (loop for bind in +trie-bindings+ do
        (cl-format *out* "~%Bound ~S to ~S"
                (first bind) (bind-val (first bind)))))


;;;=======================================
(defn tryme []
  (ensure-trie-db :foo)
  (with-trie-db (:foo)
    (trie-add '(hello world))
    (cl-format *out* "~%(trie-query '(hello world)) = %s" (trie-query '(hello world)))
    (cl-format *out* "~%(trie-query '(hello ?what)) = %s" (trie-query '(hello ?what)))))
	  
