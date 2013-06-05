#lang racket

(require "forward-analysis.rkt"
         "../lattice/lattice.rkt"
         "../semantics/abstract.rkt"
         "../semantics/abstract-utilities.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  stack-ensure-hdrm
                  pda-term-insn))

(provide max-headroom-analysis
         max-headroom-lattice
         max-headroom-flow-function)

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

(define ((max-headroom-flow-function lim) astate flow-value)
  (displayln flow-value)
  (cond [(push-astate? astate) (dec flow-value)]
        [(pop-astate? astate) (inc lim flow-value)]
        [(stack-ensure-astate? astate)
         ((∨ lim) flow-value
            (stack-ensure-hdrm
             (pda-term-insn
              (abstract-state-node astate))))]
        [else flow-value]))

(define ((max-headroom-pop-flow-function lim)
         push-astate push-fv pop-astate pop-fv)
  ((max-headroom-flow-function lim) pop-astate pop-fv))

(define (max-headroom-lattice lim)
  (bounded-lattice (∨ lim) (⊒ lim) (∧ lim) (⊑ lim)
                   (max-headroom-flow-function lim)
                   (max-headroom-pop-flow-function lim)
                   ⊤ ⊥))

(define ((max-headroom-analysis lim) pda-risc)
  (forward-analysis (max-headroom-lattice lim)
                    (max-headroom-flow-function lim)
                    (max-headroom-pop-flow-function lim)
                    pda-risc))
