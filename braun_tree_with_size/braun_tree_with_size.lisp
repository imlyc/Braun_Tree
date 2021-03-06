; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the TRACE* book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (assign evalable-printing-abstractions nil)

;arithmetic book
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading arithmetic-5/top book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "arithmetic-5/top" :dir :system)

;basic thms/lemmas about lists
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading coi/lists book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "coi/lists/basic" :dir :system)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2's lexicographic-ordering-without-arithmetic book.~%This indicates that either your ACL2 installation is missing the standard books are they are not properly certified.") (value :invisible))
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :load-compiled-file :comp :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)

; Non-events:
(set-guard-checking :none)


; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(acl2::include-book "arithmetic-5/top" :dir :system)

;;braun tree
;;stree is a list, either a nil list or a list with four elements
;;nil | size left right data

;;define tree with size, size tree
(defunc streep (tr)
  :input-contract t
  :output-contract (booleanp (streep tr))
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
(defunc stree-size (tr)
  :input-contract (streep tr)
  :output-contract (natp (stree-size tr))
  (if (endp tr)
    0
    (first tr)))
;; left
(defunc stree-left (tr)
  :input-contract (and (streep tr)
                        (consp tr))
  :output-contract (streep (stree-left tr))
  (second tr))
;; right
(defunc stree-right (tr)
  :input-contract (and (streep tr)
                        (consp tr))
  :output-contract (streep (stree-right tr))
  (third tr))

;;tree size, iteration
(defunc stree-size-it (tr)
  :input-contract (streep tr)
  :output-contract (natp (stree-size-it tr))
  (if (endp tr)
    0
    (+ 1 (stree-size-it (stree-left tr))
       (stree-size-it (stree-right tr)))))

;;tree size equivalence
(defthm stree-size-it=stree-size
  (implies (streep tr)
           (equal (stree-size-it tr) (stree-size tr))))

(defunc streep-null (tr)
  :input-contract (streep tr)
  :output-contract (booleanp (streep-null tr))
  (endp tr))

(defunc streep-leaf (tr)
  :input-contract (streep tr)
  :output-contract (booleanp (streep-leaf tr))
  (if (endp tr)
    nil
    (and (equal (stree-left tr) nil)
         (equal (stree-right tr) nil))))

;;braun tree
(defunc brtreep (brtr)
  :input-contract t
  :output-contract (booleanp (brtreep brtr))
  (if (streep brtr)
    (if (endp brtr)
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

(defunc stree-size-nump (brtr num)
  :input-contract (and (streep brtr)
                              (natp num))
  :output-contract (booleanp (stree-size-nump brtr num))
  (let ((sz (stree-size brtr)))
    (or (equal sz num)
        (equal sz (+ num 1)))))

(defthm brtree-left-is-brtree
  (implies (and (brtreep brtr) (not (endp brtr)))
           (brtreep (stree-left brtr))))
(defthm brtree-right-is-brtree
  (implies (and (brtreep brtr) (not (endp brtr)))
           (brtreep (stree-right brtr))))

(defthm stree-size-nump-0
  (implies (and (brtreep brtr)
                (not (streep-leaf brtr))
                (stree-size-nump brtr 0))
           (endp brtr))
  :rule-classes :forward-chaining)

(defthm stree-property
  (implies (and (streep tr) (not (endp tr)))
           (and (consp (cdr tr))
                (true-listp (cddr tr))
                (equal (len (cddr tr)) 2)))
  :rule-classes (:forward-chaining
                 :type-prescription))

(in-theory (disable stree-left stree-right stree-size streep))#|ACL2s-ToDo-Line|#


;;braun tree diff
(defunc brtree-diff (brtr num)
  :input-contract (and (natp num) (brtreep brtr) 
                              (stree-size-nump brtr num))
  :output-contract (natp (brtree-diff brtr num))
  (cond
   ((and (endp brtr) (zp num))
    0)
   ((and (streep-leaf brtr) (zp num))
    1)
   (t
    (if (oddp num)
      (brtree-diff (stree-left brtr) (/ (- num 1) 2))
      (brtree-diff (stree-right brtr) (/ (- num 2) 2))))))
  
#|
(IMPLIES (AND (CONSP (CDR BRTR)) ;;rest tr is consp
              (TRUE-LISTP (CDDR BRTR)) ;;(rt data) is true-list
              (STREEP (CADDR BRTR)) ;; rt is stree
              (CONSP (CADDR BRTR)) ;; rt is consp
              (EQUAL 1 (CAR BRTR)) ;; tr size 1
              (EQUAL 0 (CAADDR BRTR)) ;; rt size is 0
              (NOT (CADR BRTR)) ;; lt is nil
              (BRTREEP (CADDR BRTR)) ;;rt is brtree
              (CONSP BRTR) ;;tr is consp
              (EQUAL (LEN (CDDR BRTR)) 2)) ;;
         (INTEGERP (ACL2S-UNDEFINED 'BRTREE-DIFF
                                    (CONS (CADDR BRTR) '(-1)))))
|#

;;braun size
(defun brtree-size (brtr)
  (declare (xargs :guard (brtreep brtr)))
  (if (endp brtr)
    0
    (let ((m (brtree-size (stree-right brtr)))
         (s (stree-left brtr)))
          (+ 1 (* 2 m) (brtree-diff s m)))))
  