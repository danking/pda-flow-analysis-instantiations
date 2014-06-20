#lang racket

(require "flow-state-utils.rkt"
         "../cfa2/cfa2.rkt"
         ;; TODO this should be a built-in module
         "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/flow.rkt"
         "../semantics/monadic-configuration.rkt"
         (prefix-in monad: "../semantics/monads.rkt")
         "../pda-to-pda-risc/risc-enhanced/fold-enhanced.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-risc-enh-initial-term
                  pdarisc-reg-uid
                  pda-term-succs
                  pop-assign?
                  push?
                  ;; for task-debug-info
                  pda-term->uid))

(monad:instantiate-monad-ops
 ConfigMonad-bind ConfigMonad-return ConfigMonad-creator ConfigMonad-accessor
 (~>~ monad:~>~)
 (~> monad:~>)
 (for/set~>~ monad:for/set~>~)
 (for/list~>~ monad:for/list~>~)
 (mapM monad:mapM))

(define-syntax-rule (return x ...) (ConfigMonad-return x ...))
(define-syntax-rule (bind x ...) (ConfigMonad-bind x ...))

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
  (define register-count (pdarisc-reg-uid pda-risc-enh))
  ;; flow-function-map : [Map Term [FlowFunction Term AStack AState]]
  (define flow-function-map (make-hash))

  ;; compute-and-set-ff! : Term -> [ConfigMonad Void]
  (define (compute-and-set-ff! t)
    (~> ((ff (compute-flow-function t)))
      (hash-set! flow-function-map t ff)))

  ;; build-flow-function-map : [SetEqOf Term]
  ;;                           [SetEqOf Term]
  ;;                           ->
  ;;                           [ConfigMonad Void]
  (define (build-flow-function-map W Seen)
    (cond [(set-empty? W) (return (void))]
          [else (~> ((_ (compute-and-set-ff! (set-first W)))
                     (result (let-values (((new-W new-Seen)
                                           (for/fold
                                               ([W2 (set-rest W)]
                                                [Seen Seen])
                                               ([new (pda-term-succs (set-first W))])
                                             (if (set-member? Seen new)
                                                 (values W2 Seen)
                                                 (values (set-add W2 new)
                                                         (set-add Seen new))))))
                               (build-flow-function-map new-W new-Seen))))
                  result)]))

  (define-values (_ configuration)
    (run-config-monad*
     (init-configuration register-count)
     (build-flow-function-map (seteq (pda-risc-enh-initial-term pda-risc-enh))
                              (seteq (pda-risc-enh-initial-term
                                      pda-risc-enh)))))

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
     (run-config-monad*
      config
      (~> ((succ-terms+astates ((hash-ref flow-function-map node-term)
                                node-astate)))
        (for/set ([term+astate succ-terms+astates])
          (flow-state (first term+astate)
                      (second term+astate)
                      new-fv))))])

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
     (run-config-monad*
      config
      (~> ((succ-terms+astates ((hash-ref flow-function-map pop-term)
                                (abstract-state-st push-astate) pop-astate)))
        (for/set ([term+astate succ-terms+astates])
          (flow-state (first term+astate)
                      (second term+astate)
                      new-fv))))])

  (define initial-term (pda-risc-enh-initial-term pda-risc-enh))

  (define/match (flowstate-debug-string flowstate)
    [((flow-state term (abstract-state: in st tr re) fv))
     (format "Task: (uid in st re tr fv) = (~a ~a ~a ~a ~a ~a)"
             (pda-term->uid term) in st re tr fv)])

  (FlowAnalysis (set (initial-flow-state initial-term
                                         initial-flow-value
                                         register-count))
                configuration
                push-fstate? pop-fstate?
                (get-join-semi-lattice-from-lattice
                 (flow-state-lattice flow-value-bounded-lattice))
                flow-state-same-sub-lattice?
                flow-state-sub-lattice-hash-code
                succ-states/flow pop-succ-states/flow
                flowstate-debug-string))
