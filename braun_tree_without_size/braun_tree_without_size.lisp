;;braun tree, size

;;arithmetic
(include-book "arithmetic-5/top" :dir :system)

;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

;;define tree with size, size tree
(defun treep-null (tr)
  (endp tr))

;;selector
;; left
(defun tree-left (tr)
  (first tr))

;; right
(defun tree-right (tr)
  (second tr))

;;tree with size as a field
(defun treep (tr)
  (if (true-listp tr)
    (if (treep-null tr)
      t
      (if (equal (len tr) 3)
        (and (treep (tree-left tr))
             (treep (tree-right tr)))
        nil))
    nil))

;;leaf node
(defun treep-leaf (tr)
  (if (treep-null tr)
    nil
    (and (equal (tree-left tr) nil)
         (equal (tree-right tr) nil))))

;;tree size, iteration
(defun tree-size (tr)
  (if (treep-null tr)
    0
    (+ 1  (tree-size (tree-left tr))
            (tree-size (tree-right tr)))))

;;braun tree
(defun brtreep (brtr)
  (if (treep brtr)
    (if (treep-null brtr)
      t
      (let ((lc (tree-left brtr))
            (rc (tree-right brtr)))
        (let ((lcsz (tree-size lc))
              (rcsz (tree-size rc)))
          (if (or (equal lcsz rcsz)
                  (equal lcsz (+ rcsz 1)))
            (and (brtreep lc) (brtreep rc))
            nil))))
    nil))

;;in brtree-diff, num must satisfy the condition
;; that size = num or size = num + 1
;; this function maybe not used
(defun tree-size-nump (brtr num)
  (let ((sz (tree-size brtr)))
    (or (equal sz num)
        (equal sz (+ num 1)))))

;;braun tree diff
(defun brtree-diff (brtr num)
  (if (tree-size-nump brtr num)
    (cond
     ((and (treep-null brtr) (zp num))
      0)
     ((and (treep-leaf brtr) (zp num))
      1)
     (t
      (if (oddp num)
        (brtree-diff (tree-left brtr) (/ (- num 1) 2))
        (brtree-diff (tree-right brtr) (/ (- num 2) 2)))))
    'error))
;; define diff by definition, instead of calculation
(defthm lemma
  (IMPLIES (AND (BRTREEP TR) (<= 0 (TREE-SIZE TR)))
           (EQUAL (BRTREE-DIFF TR (TREE-SIZE TR))
                  0)))

(defthm lemma2
  (IMPLIES (AND (BRTREEP TR)
                (INTEGERP NUM)
                (<= 0 NUM)
                (EQUAL (TREE-SIZE TR) (+ 1 NUM)))
           (EQUAL (BRTREE-DIFF TR NUM)
                  (+ (- NUM) (TREE-SIZE TR)))))

(defthm brtree-diff-minus
  (implies (and (brtreep tr) (natp num) (tree-size-nump tr num)) 
           (equal (brtree-diff tr num)
                  (- (tree-size tr) num)))
  :rule-classes :definition)
(in-theory (disable brtree-diff))

;;braun tree size
(defun brtree-size (brtr)
  (if (treep-null brtr)
    0
    (let ((m (brtree-size (tree-right brtr)))
         (s (tree-left brtr)))
          (+ 1 (* m 2) (brtree-diff s m)))))
(in-theory (disable tree-left tree-right treep-null treep-leaf))
;;our final target
(defthm brtee-size-correct
  (implies (brtreep brtr)
           (equal (brtree-size brtr) (tree-size brtr)))
  :rule-classes nil)#|ACL2s-ToDo-Line|#
