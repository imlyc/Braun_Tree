;;braun tree
;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

(defthm not-consp-is-endp
  (implies (listp l)
           (implies (not (consp l))
                    (equal l nil)))
  :rule-classes (:built-in-clause))#|ACL2s-ToDo-Line|#


(defthm cdr-is-list
  (implies (and (listp l) (consp l))
           (listp (cdr l)))
  :hints (("Goal''"
           :use not-consp-is-endp)))

(defthm streep-lemma
  (IMPLIES (AND (LISTP TR)
                (CONSP TR)
                (NOT (CONSP (CDR TR))))
           (NOT (CDR TR)))
  :hints (("Goal"
           :use not-consp-is-endp)))

(defun streep (tr)
  (declare (xargs :guard t))
  (if (listp tr)
    (if (endp tr)
      t
      (if (not (endp (rest tr)))
        (if (not (endp (rest (rest tr))))
          (if (not (endp (rest (rest (rest tr)))))
            (if (endp (rest (rest (rest (rest tr)))))
              (and (natp (first tr))
                   (streep (second tr))
                   (streep (third tr)))
              nil)
            nil)
          nil)
        nil))
    nil))

(defun stree-size (tr)
  (declare (xargs :guard (streep tr)))
  (if (endp tr)
    0
    (first tr)))

(defun streec-leaf () nil)

(defun streec (data lc rc)