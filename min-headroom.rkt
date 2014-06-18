#lang racket

(require "forward-analysis.rkt"
         ;; TODO this should be a built-in module
         "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  stack-ensure-hdrm
                  pda-term-insn
                  push?
                  pop-assign?
                  stack-ensure?))

(provide min-headroom-analysis
         min-headroom-bounded-lattice
         min-headroom-flow-function
         min-headroom-pop-flow-function)

;; LV = [U 'infinity Natural]

;; lattice-add1 : LV -> LV
;;
;; If we have infinite headroom, we can always add more and still have infinite
;; headroom.
(define (lattice-add1 flow-value)
  (if (inf? flow-value)
      flow-value
      (add1 flow-value)))

;; lattice-sub1 : LV -> LV
;;
;; If we have infinite headroom, we can always use some and still have infinite
;; headroom.
;;
;; However, we cannot have less than zero headroom.
(define (lattice-sub1 flow-value)
  (if (inf? flow-value)
      flow-value
      (meet (sub1 flow-value) 0)))

(define (min-headroom-flow-function _1 _2 _3
                                    term _4 flow-value)
  (define insn (pda-term-insn term))
  (cond [(push? insn) (lattice-sub1 flow-value)]
        [(pop-assign? insn) (lattice-add1 flow-value)]
        [(stack-ensure? insn)
         (meet flow-value (stack-ensure-hdrm insn))]
        [else flow-value]))

(define (min-headroom-pop-flow-function _1 _2 _3
                                        push-term push-astate push-fv
                                        pop-term pop-astate pop-fv)
  (meet push-fv
        (min-headroom-flow-function push-term push-astate push-fv
                                    pop-term pop-astate pop-fv)))

(define (inf? x)
  (eq? x 'infinity))

(define (join x y)
  (cond [(inf? x) y]
        [(inf? y) x]
        [else (min x y)]))

(define (gte? x y)
  (or (inf? y)
      (and (not (inf? x))
           (<= x y))))

(define (meet x y)
  (if (or (inf? x) (inf? y))
      'infinity
      (max x y)))

(define (lte? x y)
  (or (inf? x)
      (and (not (inf? y))
           (>= x y))))

(define min-headroom-bounded-lattice
  (bounded-lattice join
                   gte?
                   meet
                   lte?
                   (lambda (x y)
                     (or (inf? x) (inf? y)
                         (and (number? x) (number? y))))
                   (lambda (x _) 0)
                   0
                   'infinity))

(define (min-headroom-analysis pda-risc)
  (forward-analysis min-headroom-bounded-lattice
                    'infinity ;; 0
                    min-headroom-flow-function
                    min-headroom-pop-flow-function
                    pda-risc))
