;;braun tree, size

;;arithmetic
(include-book "arithmetic-5/top" :dir :system)

;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

;;define tree with size, size tree
(defun streep-null (tr)
;;  (declare (xargs :guard (streep tr)))
  (endp tr))

;;selector
;; size
(defun stree-size (tr)
;;  (declare (xargs :guard (streep tr)))
  (if (streep-null tr)
    0
    (first tr)))

;; left
(defun stree-left (tr)
;;  (declare (xargs
;;            :guard (and (streep tr)
;;                        (not (streep-null tr)))))
  (second tr))

;; right
(defun stree-right (tr)
;;  (declare (xargs
;;            :guard (and (streep tr)
;;                        (not (streep-null tr)))))
  (third tr))

(defun streep (tr)
;;  (declare (xargs :guard t))
  (if (true-listp tr)
    (if (streep-null tr)
      t
      (if (equal (len tr) 4)
        (let ((sz (stree-size tr))
              (lc (stree-left tr))
              (rc (stree-right tr)))
          (if (and (natp sz)
                   (streep lc)
                   (streep rc))
            (let ((lcsz (stree-size lc))
                  (rcsz (stree-size rc)))
              (equal sz (+ 1 lcsz rcsz)))
            nil))
        nil))
    nil))

(defun streep-leaf (tr)
;;  (declare (xargs :guard (streep tr)))
  (if (streep-null tr)
    nil
    (and (equal (stree-left tr) nil)
         (equal (stree-right tr) nil))))

;;tree size, iteration
(defun stree-size-it (tr)
;;  (declare (xargs :guard (streep tr)))
  (if (streep-null tr)
    0
    (+ 1  (stree-size-it (stree-left tr))
            (stree-size-it (stree-right tr)))))

;;tree size equivalence
(defthm stree-size-it=stree-size
  (implies (streep tr)
           (equal (stree-size-it tr) (stree-size tr)))
  :rule-classes nil)

;;braun tree
(defun brtreep (brtr)
;;  (declare (xargs :guard t))
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
;; this function maybe not used
(defun stree-size-nump (brtr num)
;;  (declare (xargs :guard (and (streep brtr)
;;                              (natp num))))
  (let ((sz (stree-size brtr)))
    (or (equal sz num)
        (equal sz (+ num 1)))))

;;braun tree diff
(defun brtree-diff (brtr num)
;;  (declare (xargs :guard (and (natp num) (brtreep brtr) 
;;                              (stree-size-nump brtr num))))
  (cond
   ((zp num)
    (if (streep-leaf brtr)
      1
      0))
   ((oddp num)
    (brtree-diff (stree-left brtr) (/ (- num 1) 2)))
   ((evenp num)
    (brtree-diff (stree-right brtr) (/ (- num 2) 2)))))

;;braun tree size
;; the guard here cannot be verified
(defun brtree-size (brtr)
;;  (declare (xargs :guard (brtreep brtr)))
  (if (streep-null brtr)
    0
    (let ((m (brtree-size (stree-right brtr)))
         (s (stree-left brtr)))
          (+ 1 (* 2 m) (brtree-diff s m)))))

;;disable stree* function
;; these functions needn't be rewritten
(in-theory (disable streep streep-leaf streep-null 
                   stree-left stree-right stree-size))

;;our final target
;; 1. Try to prove it on paper
;; 2. Try to prove it via ACL2
(defthm brtee-size-correct
  (implies (brtreep brtr)
           (equal (brtree-size brtr) (stree-size-it brtr)))
  :rule-classes nil)