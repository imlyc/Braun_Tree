;;braun tree, size

;;arithmetic
(include-book "arithmetic-5/top" :dir :system)

;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

;;define tree with size, size tree
(defun streep-null (tr)
  (endp tr))

;;selector
;; size
(defun stree-size (tr)
  (if (streep-null tr)
    0
    (first tr)))

;; left
(defun stree-left (tr)
  (second tr))

;; right
(defun stree-right (tr)
  (third tr))

;;tree with size as a field
(defun streep (tr)
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

;;leaf node
(defun streep-leaf (tr)
  (if (streep-null tr)
    nil
    (and (equal (stree-left tr) nil)
         (equal (stree-right tr) nil))))

;;tree size, iteration
(defun stree-size-it (tr)
  (if (streep-null tr)
    0
    (+ 1  (stree-size-it (stree-left tr))
            (stree-size-it (stree-right tr)))))

;;tree size equivalence
(defthm stree-size-it=stree-size
  (implies (streep tr)
           (equal (stree-size tr) (stree-size-it tr))))
(in-theory (disable stree-size-it=stree-size))
;;  :rule-classes nil)

;;braun tree
(defun brtreep (brtr)
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
  (let ((sz (stree-size brtr)))
    (or (equal sz num)
        (equal sz (+ num 1)))))

;;braun tree diff
(defun brtree-diff (brtr num)
  (if (stree-size-nump brtr num)
    (cond
     ((and (streep-null brtr) (zp num))
      0)
     ((and (streep-leaf brtr) (zp num))
      1)
     (t
      (if (oddp num)
        (brtree-diff (stree-left brtr) (/ (- num 1) 2))
        (brtree-diff (stree-right brtr) (/ (- num 2) 2)))))
    'error))

;; define diff by definition, instead of calculation
(defthm brtree-diff-minus
  (implies (and (brtreep tr) (natp num) (stree-size-nump tr num)) 
           (equal (brtree-diff tr num)
                  (- (stree-size tr) num)))
  :hints (("Goal" :in-theory (disable stree-size)))
  :rule-classes (:definition))
(in-theory (disable brtree-diff))

;;braun tree size
(defun brtree-size (brtr)
  (if (streep-null brtr)
    0
    (let ((m (brtree-size (stree-right brtr)))
         (s (stree-left brtr)))
          (+ 1 (* m 2) (brtree-diff s m)))))

;;our final target
(defthm brtee-size-correct
  (implies (brtreep brtr)
           (equal (brtree-size brtr) (stree-size brtr)))
  :rule-classes nil)