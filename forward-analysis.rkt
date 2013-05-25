#lang racket

(require "../cfa2/cfa2.rkt"
         ;; TODO this should be a built-in module
         "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/flow.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-risc-enh-initial-term
                  pop-assign?
                  push?))

(provide forward-analysis)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Forward Analysis

;; forward-analysis : [Bounded-Lattice FlowValue]
;;                    [AbstractState FlowValue -> FlowValue]
;;                    [AbstractState FlowValue AbstractState FlowValue
;;                       -> FlowValue]
;;                    PDA-RISC-ENH
;;                    ->
;;                    [FlowAnalysis FlowState
;;                                  [Lattice FlowState]]
;;
(define (forward-analysis flow-value-bounded-lattice
                          fv-next
                          pop-fv-next
                          pda-risc-enh)
  ;; push-fstate? : FlowState -> Boolean
  (define push-fstate? (lift-insn/flow push?))

  ;; pop-fstate? : FlowState -> Boolean
  (define pop-fstate? (lift-insn/flow pop-assign?))

  ;; pop-succ-states : AState AState -> [SetOf AState]
  (define (pop-succ-states push pop)
    (abstract-step/new-stack pop (abstract-state-st push)))

  (define (flow-state-same-chain? fs1 fs2 [recur equal?])
    (astate-same-chain? (flow-state-astate fs1)
                        (flow-state-astate fs2)
                        recur))
  (define (flow-state-chain-hash-code fs [recur equal-hash-code])
    (astate-chain-hash-code (flow-state-astate fs) recur))

  (define flow-state-lattice
    (pointwise-bounded-lattice flow-state
      [flow-state-astate astate-bounded-lattice]
      [flow-state-flow-value flow-value-bounded-lattice]))

  ;; succ-states/flow : FlowState -> [SetOf FlowState]
  (define (succ-states/flow fstate)
    (match-define (flow-state astate fv) fstate)

    (for/seteq ([astate~ (in-set (abstract-step astate))])
      (flow-state astate~ (fv-next astate fv))))

  ;; pop-succ-states/flow : FlowState FlowState -> [SetOf FlowState]
  (define (pop-succ-states/flow push-fstate pop-fstate)
    (match-define (flow-state push-astate push-fv) push-fstate)
    (match-define (flow-state pop-astate pop-fv) pop-fstate)

    (for/seteq ([astate~ (in-set (pop-succ-states push-astate pop-astate))])
      (flow-state astate~ (pop-fv-next push-astate push-fv pop-astate pop-fv))))

  (FlowAnalysis (initial-flow-state
                 (pda-risc-enh-initial-term pda-risc-enh)
                 (bounded-lattice-bottom flow-value-bounded-lattice))
                push-fstate? pop-fstate?
                (get-join-semi-lattice-from-lattice flow-state-lattice)
                flow-state-same-chain?
                flow-state-chain-hash-code
                succ-states/flow pop-succ-states/flow))
