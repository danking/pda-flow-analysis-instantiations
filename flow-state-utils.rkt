#lang racket

(require "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/flow.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-term->uid))

(provide (all-defined-out))

;; same-sub-lattice? : FlowState FlowState -> Boolean
(define (flow-state-same-sub-lattice? fs1 fs2 [recur equal?])
  (= (pda-term->uid (flow-state-node fs1))
     (pda-term->uid (flow-state-node fs2))))

;; sub-lattice-hash-code : FlowState -> Number
(define (flow-state-sub-lattice-hash-code fs [recur equal-hash-code])
  (recur (pda-term->uid (flow-state-node fs))))

;; flow-state-lattice : [Semi-Lattice FlowState]
(define (flow-state-lattice bounded-lattice)
  (pointwise-lattice flow-state
    [flow-state-node bounded-flat-equal?-lattice]
    [flow-state-astate astate-lattice]
    [flow-state-flow-value bounded-lattice]))
