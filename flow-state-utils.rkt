#lang racket

(require "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/flow.rkt")

(provide (all-defined-out))

;; same-sub-lattice? : FlowState FlowState -> Boolean
(define (flow-state-same-sub-lattice? fs1 fs2 [recur equal?])
  (astate-same-sub-lattice? (flow-state-astate fs1)
                      (flow-state-astate fs2)
                      recur))

;; sub-lattice-hash-code : FlowState -> Number
(define (flow-state-sub-lattice-hash-code fs [recur equal-hash-code])
  (astate-sub-lattice-hash-code (flow-state-astate fs) recur))

;; flow-state-lattice : [Semi-Lattice FlowState]
(define (flow-state-lattice bounded-lattice)
  (pointwise-bounded-lattice flow-state
    [flow-state-astate astate-bounded-lattice]
    [flow-state-flow-value bounded-lattice]))
