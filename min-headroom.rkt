#lang racket

(require "forward-analysis.rkt"
         "../cfa2/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/abstract-utilities.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  stack-ensure-hdrm
                  pda-term-insn))

(provide min-headroom-analysis
         min-headroom-lattice
         min-headroom-flow-function
         min-headroom-pop-flow-function)

(define (min-headroom-flow-function astate flow-value)
  (cond [(push-astate? astate) (max (sub1 flow-value) 0)]
        [(pop-astate? astate) (add1 flow-value)]
        [(stack-ensure-astate? astate)
         (+ flow-value
            (stack-ensure-hdrm
             (pda-term-insn
              (abstract-state-node astate))))]
        [else flow-value]))

(define (min-headroom-pop-flow-function push-astate push-fv pop-astate pop-fv)
  (max push-fv (min-headroom-flow-function pop-astate pop-fv)))

(define min-headroom-lattice
  (lattice min <= 0 +inf.0))

(define (min-headroom-analysis pda-risc)
  (forward-analysis min-headroom-lattice
                    min-headroom-flow-function
                    min-headroom-pop-flow-function
                    pda-risc))
