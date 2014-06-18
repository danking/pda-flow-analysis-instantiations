#lang racket

(require "flow-state-utils.rkt"
         "../cfa2/cfa2.rkt"
         ;; TODO this should be a built-in module
         "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/flow.rkt"
         "../pda-to-pda-risc/risc-enhanced/fold-enhanced.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-risc-enh-initial-term
                  pda-term-succs
                  pop-assign?
                  push?
                  ;; for task-debug-info
                  pda-term->uid))

(provide forward-analysis)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Forward Analysis

;; forward-analysis : [Bounded-Lattice FlowValue]
;;                    FlowValue
;;                    [Term AbstractState FlowValue
;;                     Term AbstractState FlowValue
;;                     ->
;;                     FlowValue]
;;                    [Term AbstractState FlowValue
;;                     Term AbstractState FlowValue
;;                     Term AbstractState FlowValue
;;                       -> FlowValue]
;;                    PDA-RISC-ENH
;;                    ->
;;                    [FlowAnalysis FlowState
;;                                  [Lattice FlowState]]
;;
(define (forward-analysis flow-value-bounded-lattice
                          initial-flow-value
                          fv-next
                          pop-fv-next
                          pda-risc-enh)
  (define flow-function-map (make-hash))
  (define (compute-and-set-ff! t)
    (define ff (compute-flow-function t))
    (hash-set! flow-function-map t ff))

  (let loop
      ([W (seteq (pda-risc-enh-initial-term pda-risc-enh))]
       [Seen (seteq)])
    (cond [(set-empty? W)]
          [else (compute-and-set-ff! (set-first W))
                (define-values (new-W new-Seen)
                  (for/fold
                      ([W (set-rest W)]
                       [Seen Seen])
                      ([new (pda-term-succs (set-first W))])
                    (if (set-member? Seen new)
                        (values W Seen)
                        (values (set-add W new) (set-add Seen new)))))
                (loop new-W new-Seen)]))

  ;; push-fstate? : FlowState -> Boolean
  (define push-fstate? (lift-insn/flow push?))

  ;; pop-fstate? : FlowState -> Boolean
  (define (pop-fstate? fs)
    ((lift-insn/flow pop-assign?) fs))

  ;; succ-states/flow : FlowState FlowState
  ;;                    ->
  ;;                    [Values [SetOf FlowState] Configuration]
  (define/match (succ-states/flow push-fstate node-fstate config)
    [((flow-state push-term push-astate push-fv)
      (flow-state node-term node-astate node-fv)
      _)
     (define new-fv (fv-next push-term push-astate push-fv
                             node-term node-astate node-fv))
     (define succ-terms+astates
       ((hash-ref flow-function-map node-term) node-astate))
     (values (for/set ([term+astate succ-terms+astates])
               (flow-state (first term+astate)
                           (second term+astate)
                           new-fv))
             config)])

  ;; pop-succ-states/flow : FlowState FlowState FlowState Configuration
  ;;                        ->
  ;;                        [Values [SetOf FlowState] Configuration]
  (define/match (pop-succ-states/flow gp-fstate push-fstate pop-fstate config)
    [((flow-state gp-term gp-astate gp-fv)
      (flow-state push-term push-astate push-fv)
      (flow-state pop-term pop-astate pop-fv)
      _)
     (define new-fv (pop-fv-next gp-term gp-astate gp-fv
                                 push-term push-astate push-fv
                                 pop-term pop-astate pop-fv))
     (define succ-terms+astates
       ((hash-ref flow-function-map pop-term)
        (abstract-state-st push-astate) pop-astate))
     (values (for/set ([term+astate succ-terms+astates])
               (flow-state (first term+astate)
                           (second term+astate)
                           new-fv))
             config)])

  (define initial-term (pda-risc-enh-initial-term pda-risc-enh))

  (define/match (flowstate-debug-string flowstate)
    [((flow-state term (abstract-state: in st tr re) fv))
     (format "Task: (uid in st re tr fv) = (~a ~a ~a ~a ~a ~a)"
             (pda-term->uid term) in st re tr fv)])

  (FlowAnalysis (set (initial-flow-state initial-term initial-flow-value))
                #f
                push-fstate? pop-fstate?
                (get-join-semi-lattice-from-lattice
                  (flow-state-lattice flow-value-bounded-lattice))
                flow-state-same-sub-lattice?
                flow-state-sub-lattice-hash-code
                succ-states/flow pop-succ-states/flow
                flowstate-debug-string))
