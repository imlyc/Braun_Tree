;;braun tree
;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

;;define tree with size, size tree
(defun streep (tr)
  (declare (xargs :guard t))
  (if (listp tr)
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
              (equal sz (+ 1 (+ lcsz rcsz))))
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
    (+ 1 (+ (stree-size-it (stree-left tr))
            (stree-size-it (stree-right tr))))))

;;tree size equivalence
(defthm stree-size-it=stree-size
  (implies (streep tr)
           (equal (stree-size-it tr) (stree-size tr))))

;;stree constructor
(defun streec-leaf (data)
  (list 1 nil nil data))

(defun streec (data lc rc)
  (declare (xargs :guard (and (streep lc) (streep rc))))
  (list (+ 1 (+ (stree-size lc) (stree-size rc))) lc rc data))

(defun streep-leaf (tr)
  (declare (xargs :guard (streep tr)))
  (if (endp tr)
    nil
    (and (equal (stree-left tr) nil)
         (equal (stree-right tr) nil))))

;;braun tree
(defun brtreep (brtr)
  (declare (xargs :guard (streep brtr)))
  (if (endp brtr)
    t
    (let ((lc (stree-left brtr))
          (rc (stree-right brtr)))
      (let ((lcsz (stree-size lc))
            (rcsz (stree-size rc)))
        (if (or (equal lcsz rcsz)
                (equal lcsz (+ rcsz 1)))
          (and (brtreep lc) (brtreep rc))
          nil)))))#|ACL2s-ToDo-Line|#



;; stuck here !!!
;;braun tree diff
(defun brtree-diff (brtr num)
  (declare (xargs :guard (and (brtreep brtr) 
                              (natp num))))
  (cond
   ((zp num)
    (if (streep-leaf brtr)
      1
      0))
   ((oddp num)
    (brtree-diff (stree-left brtr) (/ (- num 1) 2)))
   ((evenp num)
    (brtree-diff (stree-right brtr) (/ (- num 2) 2)))
   (t 7)))

;;braun size
(defun brtree-size (brtr)
  (declare (xargs :guard (brtreep brtr)))
  (if (endp brtr)
    0
    (let ((m (brtree-size (stree-right brtr))))
      (+ (+ 1 (* m 2))
         (brtree-diff (stree-left brtr) m)))))
  