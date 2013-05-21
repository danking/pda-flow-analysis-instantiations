#lang racket

(require "../cfa2/cfa2.rkt"
         "../cfa2/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/abstract-utilities.rkt"
         "../semantics/flow.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-risc-enh-initial-term
                  pop-assign?
                  push?))

(provide forward-analysis)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Forward Analysis

;; forward-analysis : [Lattice FlowValue]
;;                    [AbstractState FlowValue -> FlowValue]
;;                    [AbstractState FlowValue AbstractState FlowValue
;;                       -> FlowValue]
;;                    PDA-RISC-ENH
;;                    ->
;;                    [FlowAnalysis FlowState
;;                                  [Lattice FlowState]]
;;
(define (forward-analysis flow-value-lattice
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

  ;; flow-state-join : FlowState FlowState -> FlowState
  (define flow-state-join
    (maplift-astate*fv/flow astate-join
                            (lattice-join flow-value-lattice)))

  ;; flow-state-gte : FlowState FlowState -> Boolean
  (define flow-state-gte
    (foldlift-astate*fv/flow astate-gte
                             (lattice-gte flow-value-lattice)
                             (lambda (x y)
                               (and x y))))

  (define flow-state-lattice
    (lattice flow-state-join
             flow-state-gte
             (lattice-bottom flow-value-lattice)
             (lattice-top flow-value-lattice)))

  ;; flow-state-similar? : FlowState FlowState -> Boolean
  (define flow-state-similar?
    (match-lambda* [(list (flow-state s1 _)
                          (flow-state s2 _))
                    (astate-similar? s1 s2)]))
  ;; flow-state-hash-code : FlowState -> Number
  (define flow-state-hash-code
    (match-lambda [(flow-state as _) (astate-hash-code as)]))

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

  (FlowAnalysis (initial-flow-state (pda-risc-enh-initial-term pda-risc-enh)
                                    (lattice-bottom flow-value-lattice))
                push-fstate? pop-fstate? flow-state-equal?
                flow-state-lattice
                flow-state-similar? flow-state-hash-code
                succ-states/flow pop-succ-states/flow))
