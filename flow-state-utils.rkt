#lang racket

(require "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/flow.rkt")

(provide (all-defined-out))

;; same-chain? : FlowState FlowState -> Boolean
(define (flow-state-same-chain? fs1 fs2 [recur equal?])
  (astate-same-chain? (flow-state-astate fs1)
                      (flow-state-astate fs2)
                      recur))

;; chain-hash-code : FlowState -> Number
(define (flow-state-chain-hash-code fs [recur equal-hash-code])
  (astate-chain-hash-code (flow-state-astate fs) recur))

;; flow-state-lattice : [Semi-Lattice FlowState]
(define (flow-state-lattice bounded-lattice)
  (pointwise-bounded-lattice flow-state
    [flow-state-astate astate-bounded-lattice]
    [flow-state-flow-value bounded-lattice]))
