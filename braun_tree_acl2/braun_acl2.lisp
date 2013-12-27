;;arithmetic
(include-book "arithmetic-5/top" :dir :system)
;;disable guard verifcation
;;(set-guard-checking :none)
;;braun tree
;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

;;define tree with size, size tree
(defun streep (tr)
  (declare (xargs :guard t))
  (if (true-listp tr)
    (if (endp tr)
      t
      (if (equal (len tr) 4)
        (let ((sz (first tr))
              (lc (second tr))
              (rc (third tr)))
          (if (and (natp sz)
                   (streep lc)
                   (streep rc))
            (let ((lcsz (if (endp lc) 0 (first lc)))
                  (rcsz (if (endp rc) 0 (first rc))))
              (equal sz (+ 1 lcsz rcsz)))
            nil))
        nil))
    nil))

;;selector
;; size
(defun stree-size (tr)
  (declare (xargs :guard (streep tr)))
  (if (endp tr)
    0
    (first tr)))
;; left
(defun stree-left (tr)
  (declare (xargs
            :guard (and (streep tr)
                        (consp tr))))
  (second tr))
;; right
(defun stree-right (tr)
  (declare (xargs
            :guard (and (streep tr)
                        (consp tr))))
  (third tr))

;;tree size, iteration
(defun stree-size-it (tr)
  (declare (xargs :guard (streep tr)))
  (if (endp tr)
    0
    (+ 1  (stree-size-it (stree-left tr))
            (stree-size-it (stree-right tr)))))

;;tree size equivalence
(defthm stree-size-it=stree-size
  (implies (streep tr)
           (equal (stree-size-it tr) (stree-size tr)))
  :rule-classes nil)

;;stree constructor
(defun streec-leaf (data)
  (list 1 nil nil data))

(defun streec (data lc rc)
  (declare (xargs :guard (and (streep lc) (streep rc))))
  (list (+ 1 (stree-size lc) (stree-size rc)) lc rc data))

(defun streep-null (tr)
  (declare (xargs :guard (streep tr)))
  (endp tr))

(defun streep-leaf (tr)
  (declare (xargs :guard (streep tr)))
  (if (endp tr)
    nil
    (and (equal (stree-left tr) nil)
         (equal (stree-right tr) nil))))




;;(in-theory (disable streep streep-leaf streep-null 
  ;;                  stree-left stree-right stree-size))



;;braun tree
(defun brtreep (brtr)
  (declare (xargs :guard t))
  (if (streep brtr)
    (if (streep-null brtr)
      t
      (let ((lc (stree-left brtr))
            (rc (stree-right brtr)))
        (let ((lcsz (stree-size lc))
              (rcsz (stree-size rc)))
          (if (or (equal lcsz rcsz)
                  (equal lcsz (+ rcsz 1)))
            (and (brtreep lc) (brtreep rc))
            nil))))
    nil))

;;in brtree-diff, num must satisfy the condition
;; that size = num or size = num + 1

(defun stree-size-nump (brtr num)
  (declare (xargs :guard (and (streep brtr)
                              (natp num))))
  (let ((sz (stree-size brtr)))
    (or (equal sz num)
        (equal sz (+ num 1)))))

;;braun tree diff
(defun brtree-diff (brtr num)
  (declare (xargs :guard (and (natp num) (brtreep brtr) 
                              (stree-size-nump brtr num))))
  (cond
   ((zp num)
    (if (streep-leaf brtr)
      1
      0))
   ((oddp num)
    (brtree-diff (stree-left brtr) (/ (- num 1) 2)))
   ((evenp num)
    (brtree-diff (stree-right brtr) (/ (- num 2) 2)))))

;;braun size
#|
     (IMPLIES (AND (BRTREEP BRTR) (NOT (ENDP BRTR)))
              (LET ((M (BRTREE-SIZE (STREE-RIGHT BRTR)))
                    (S (STREE-LEFT BRTR)))
                   (AND (ACL2-NUMBERP M)
                        (NATP M)
                        (STREE-SIZE-NUMP S M)
                        (BRTREEP S)
                        (ACL2-NUMBERP (* 2 M))
                        (ACL2-NUMBERP (BRTREE-DIFF S M))
                        (ACL2-NUMBERP (+ (* 2 M) (BRTREE-DIFF S M))))))
|#
;;(in-theory (disable streep));; stree-left stree-right));; stree-size))


(defun brtree-size (brtr)
;;  (declare (xargs :guard (brtreep brtr)))
  (if (endp brtr)
    0
    (let ((m (brtree-size (stree-right brtr)))
         (s (stree-left brtr)))
          (+ 1 (* 2 m) (brtree-diff s m)))))
(in-theory (disable streep stree-left stree-right stree-size))#|ACL2s-ToDo-Line|#

(defthm brtee-size-correct
  (implies (brtreep brtr)
           (equal (brtree-size brtr) (stree-size-it brtr)))
  :rule-classes nil)