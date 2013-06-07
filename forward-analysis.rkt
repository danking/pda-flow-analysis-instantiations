#lang racket

(require "flow-state-utils.rkt"
         "../cfa2/cfa2.rkt"
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

  (define (flow-state-same-sub-lattice? fs1 fs2 [recur equal?])
    (astate-same-sub-lattice? (flow-state-astate fs1)
                              (flow-state-astate fs2)
                              recur))
  (define (flow-state-sub-lattice-hash-code fs [recur equal-hash-code])
    (astate-sub-lattice-hash-code (flow-state-astate fs) recur))

  (define flow-state-lattice
    (pointwise-lattice flow-state
      [flow-state-astate astate-lattice]
      [flow-state-flow-value flow-value-bounded-lattice]))

  ;; succ-states/flow : FlowState FlowState
  ;;                    ->
  ;;                    [Values [SetOf FlowState] Configuration]
  (define/match (succ-states/flow push-fstate node-fstate config)
    [((flow-state push-astate push-fv) (flow-state node-astate node-fv) _)
     (let-values (((succ-astates config)
                   (successor-states push-astate node-astate config)))
      (values (for/seteq ([astate~ (in-set succ-astates)])
                (flow-state astate~ (fv-next push-astate push-fv
                                             node-astate node-fv)))
              config))])

  ;; pop-succ-states/flow : FlowState FlowState FlowState Configuration
  ;;                        ->
  ;;                        [Values [SetOf FlowState] Configuration]
  (define/match (pop-succ-states/flow gp-fstate push-fstate pop-fstate config)
    [((flow-state gp-astate gp-fv)
      (flow-state push-astate push-fv)
      (flow-state pop-astate pop-fv)
      _)
     (let-values (((succ-astates config)
                   (successor-states/new-stack gp-astate
                                               push-astate
                                               pop-astate
                                               config)))
       (values (for/seteq ([astate~ (in-set succ-astates)])
                 (flow-state astate~ (pop-fv-next gp-astate
                                                  gp-fv
                                                  push-astate
                                                  push-fv
                                                  pop-astate
                                                  pop-fv)))
               config))])

  (FlowAnalysis (set
                 (initial-flow-state
                  (pda-risc-enh-initial-term pda-risc-enh)
                  (bounded-lattice-bottom flow-value-bounded-lattice)))
                init-configuration
                push-fstate? pop-fstate?
                (get-join-semi-lattice-from-lattice
                  (flow-state-lattice flow-value-bounded-lattice))
                flow-state-same-sub-lattice?
                flow-state-sub-lattice-hash-code
                succ-states/flow pop-succ-states/flow))
