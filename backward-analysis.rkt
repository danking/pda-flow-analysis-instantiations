#lang racket

(require "flow-state-utils.rkt"
         (only-in "../cfa2/cfa2.rkt"
                  FlowAnalysis)
         "../lattice/lattice.rkt"
         "../semantics/back-abstract.rkt"
         "../semantics/abstract-data.rkt"
         "../semantics/flow.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "../pda-to-pda-risc/risc-enhanced/fold-enhanced.rkt")

(provide backward-analysis)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Backward Analysis

;; backward-analysis : [Bounded-Lattice FlowValue]
;;                     [AbstractState FlowValue -> FlowValue]
;;                     PDA-RISC-ENH
;;                     ->
;;                     [FlowAnalysis FlowState
;;                                   [Lattice FlowState]]
;;
(define (backward-analysis flow-value-bounded-lattice
                           flow
                           pda-risc-enh)

  ;; open? : FlowState -> Boolean
  (define open? (lift-insn/flow pop-assign?))

  ;; close? : FlowState -> Boolean
  (define close? (lift-insn/flow push?))

  ;; prev-states/flow : FlowState -> [SetOf FlowState]
  ;; Applies this backward analysis's flow function to the edges entering the
  ;; given flow state from its predecessors. The value attached to the flow
  ;; state is the flow value from _before_ entry into that state.
  (define (prev-states/flow fstate)
    (match-let ([(flow-state astate fvalue) fstate])
      (for/seteq ([pred-astate (abstract-backstep astate)])
        (flow-state pred-astate (flow pred-astate fvalue)))))

  ;; prev-states-across/flow : FlowState FlowState -> [SetOf FlowState]
  ;; abstract-backstep ignores most components of the abstract state, so the
  ;; additional information contained within the given open (pop) state is not
  ;; actionable, and ignored.
  (define (prev-states-across/flow open close) (prev-states/flow close))

  ;; join-accept-nodes : PDA-RISC-ENH -> Term
  ;; Returns a new pda risc enhanced term, with its accepts merged into a
  ;; single node.
  (define (join-accept-nodes pre [acc (list (seteq) (seteq) (seteq) '())])
    (pda-term (seteq) (seteq) (seteq) (seteq) (accept -1 '()))
#;
    (match-let
     ([(list preds avail-regs live-regs rets)

       ;; TODO: stick this match into fold-enhanced
       (match term
         [(pda-term preds _ avail-regs live-regs (accept _ rets))
          (match-let ([(list preds^ ars^ lrs^ rets^) acc])
                     (list (set-union preds preds^)
                           (set-intersect avail-regs ars^)
                           (set-intersect live-regs lrs^)
                           (append rets rets^)))]
         [_ acc])])
     ;; /TODO

     (pda-term preds (seteq) avail-regs live-regs (accept -1 rets))))

  ;; initial-state : PDA-RISC-ENH -> FlowState
  (define (initial-state pre)
    (flow-state (abstract-state (join-accept-nodes pre) #f #f #f #f #f)
                (bounded-lattice-bottom flow-value-bounded-lattice)))

  (FlowAnalysis (initial-state pda-risc-enh)
                open?
                close?
                (get-join-semi-lattice-from-lattice
                  (flow-state-lattice flow-value-bounded-lattice))
                flow-state-same-chain?
                flow-state-chain-hash-code
                prev-states/flow prev-states-across/flow))
