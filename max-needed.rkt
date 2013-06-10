#lang racket

(require "backward-analysis.rkt"
         "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/back-abstract.rkt"
         "../semantics/abstract-utilities.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  stack-ensure-hdrm
                  pda-term-insn))

(provide max-needed-analysis
         max-needed-lattice
         max-needed-flow-function)

;; any reason not to use +inf.0?
(define ⊤ +inf.0)
(define ⊥ 0)

(define (bump lim n)
  (if (>= n lim) ⊤ n))

(define ((⊑ lim) x y)
  (<= (bump lim x) (bump lim y)))

(define ((⊒ lim) x y)
  (>= (bump lim x) (bump lim y)))

(define ((∨ lim) x y)
  (bump lim (max x y)))

(define ((∧ lim) x y)
  (bump lim (min x y)))

(define (inc lim n)
  (bump lim (add1 n)))

(define (dec n)
  (cond [(<= n ⊥) ⊥]
        [else (sub1 n)]))

(define ((max-needed-flow-function lim) astate flow-value)
  (displayln flow-value)
  (cond [(push-astate? astate) (inc lim flow-value)]
        [(pop-astate? astate) (dec flow-value)]
        [(stack-ensure-astate? astate)
         ((∨ lim) flow-value
            (stack-ensure-hdrm
             (pda-term-insn
              (abstract-state-node astate))))]
        [else flow-value]))

(define (max-needed-lattice lim)
  (bounded-lattice (∨ lim) (⊒ lim) (∧ lim) (⊑ lim)
                   (max-needed-flow-function lim)
                   (max-needed-flow-function lim)
                   ⊤ ⊥))

(define ((max-needed-analysis lim) pda-risc)
  (backward-analysis (max-needed-lattice lim)
                     ⊥
                     (max-needed-flow-function lim)
                     pda-risc))
