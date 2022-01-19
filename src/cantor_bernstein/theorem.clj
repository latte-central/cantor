(ns cantor-bernstein.theorem
  "A proof of the Cantor-Bernstein(-Schroeder) theorem
  in LaTTe"

  (:refer-clojure :exclude [and or not set])
  
  (:require
   ;; for notebook presentation
   [nextjournal.clerk :as clerk]
   [nextjournal.clerk.viewer :as v]

   ;; latte dependencies
   [latte.core :as latte
    :refer [definition defthm defaxiom defnotation
            forall lambda defimplicit deflemma qed
            assume have pose proof try-proof lambda forall]]

   ;; propositional logic
   [latte-prelude.prop :as p :refer [and and* or not]]

   ;; basic sets
   [latte-sets.set :as s :refer [set]]

   ;; basic relations
   [latte-sets.rel :as rel :refer [rel]]
   
   ;; relations as partial functions
   [latte-sets.pfun :as pfun :refer [functional serial injective]]
   
   ;; quantifying relations
   [latte-sets.powerrel :as prel :refer [powerrel rel-ex]]

   ))

;; # The Cantor-Bernstein theorem

;; In this (Clojure) program *slash* document we formalize a proof of the infamous
;; [Cantor-Bernstein](https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem)
;; theorem, which is an important result of (infinite) set theory.
;;
;;
;; ## Comparing sets
;;
;; The starting question is: how do you compare the sizes of sets?
;; For finite sets, this sounds like a straightforward question:
;; simply compare their number of elements. Since these are finite
;; quantities - namely *cardinalities* - it is a "simple" matter
;; of comparing numbers.
;; For infinite sets, there are simply no numbers to compare.
;; The breakthrough idea, unanimously attributed to Georg Cantor,
;; relies on the notion of an **injective function**.
;;
;; Here is the definition proposed by the [[latte-prelude]]:
;;

(comment
  (definition injective
    "An injective function."
    [[?T ?U :type], f (==> T U)]
    (forall [x y T]
      (==> (equal (f x) (f y))
           (equal x y))))
  )

;; Using a more classical notation, we say that a function $f$ is injective
;; *iff*: $$∀x,y ∈ T,~f(x) = f(y) \implies x = y$$
;;
;; The problem with the above `definition` is that it is
;; *type-theoretic*, i.e. the $T$ and $U$ in the definition above are
;; types and not sets. One important difference is that type "membership"
;; (called *inhabitation*) is decidable (at least in LaTTe) whereas
;; it is not in the theory of sets.


;; ## A relational detour

;; Thankfully, it is possible to formalize sets in type theory,
;; in various ways. LaTTe uses the so-called *predicative* approach,
;; which considers sets as predicates: the set of elements satisfiying
;; some predicate $P$ is the predicate $P$ itself.
;; A set of element of type `T` uses the type `(set T)` as a shortcut to `(==> T :type)`
;; which is the type of predicates over `T`.
;; Moreover, instead of considering relations as sets of pairs, which
;; is possible, LaTTe favors the privileded type-theoretic approach
;; of considering the type `(rel T U)` of relation $T\times U$ as a shortcut
;; to `(==> T U =type)` i.e. binary predicates over `T` and `U`.

;; This leads to the following relational interpretation of injectivity: 

(comment
(definition injective
  [[?T ?U :type] [f (rel T U)] [from (set T)] [to (set U)]]
  (forall-in [x1 from]
    (forall-in [x2 from]
      (forall-in [y1 to]
        (forall-in [y2 to]
          (==> (f x1 y1)
               (f x2 y2)
               (equal y1 y2)
               (equal x1 x2)))))))
)

;; One important difference with the relational approach is that
;; we need to write `(f x y)` as a replacement for the
;; classical mathematic notation $y=f(x)$
;; I a more traditional proof of the theorem, one would use
;; the set-theoretic interpretation of functions, i.e. something
;; like $(x,y) \in f$ rather than a relational notation.

;; Hence, the former definition explains what it is for a *relation* to be
;; injective, or rather to possess the property of injectivity.
;; To be *injective* (or an *injection*) we must also  ensure that
;; $f$ is *also* a function, hence we need also the following:

(comment
  (definition functional
    [[?T ?U :type], f (rel T U), from (set T), to (set U)]
    (forall-in [x from]
      (forall-in [y1 to]
        (forall-in [y2 to]
          (==> (f x y1)
               (f x y2)
               (equal y1 y2))))))
  )

;; This says that the relation we call `f` is, indeed, a *function*
;; in the sense that it is deterministic: if $f(x)=y1$ and $f(y)=y2$
;; then $y1=y_2$.

;; We also need the relation/function to be *serial* (or *total*), i.e. that
;; it is defined on its while domain, which is the set calle `from`.

(comment
  (definition serial
    "The relation `f` covers all of (is total wrt.) the provided `from` domain set."
    [[?T ?U :type], f (rel T U), from (set T), to (set U)]
    (forall-in [x from]
       (exists-in [y to]
         (f x y)))
    )
  )

;; In a more classical notation, we would write:
;; $$\forall x \in from,~\exists y \in to,~y=f(x)$$

;; ## Comparing sets (take 2)

;; We have now everything we need to give a formal definition
;; for a set to be *smaller* than another set, which is valid
;; even in the infinite case.

;; First, we formalize the set of (relational) functions
;; that are injective from domain $e_1$ and range $e_2$.

(definition ≲-prop
  [[?T ?U :type], e1 (set T), e2 (set U)]
  (lambda [f (rel T U)]
    (and* (functional f e1 e2)
          (serial f e1 e2)
          (injective f e1 e2))))

;; In the traditional notation we would write this set as:
;; $$\{f \in e_1 \rightarrow e_2  \mid ∀x ∈ e_1, \forall y ∈ e_2,~f(x) = f(y) \implies x = y \}$$
;; (keeping implicit the details of what makes $f$ a total function)

;; This gives our definition of the *smaller-than* comparator for sets
;; as follows:

(definition ≲
  "Set `e1` is *smaller* than set `e2`
(according to Cantor)."
  [[?T ?U :type], e1 (set T), e2 (set U)]
  (rel-ex (≲-prop e1 e2)))

;; The informal meaning is that $e_1$ is *smaller than* $e_2$,
;; which is denoted by $e_1 ≲ e_2$  (or `(≲ e1 e2)` in the Clojure notation)
;; iff there exists a relation $f$ in the set defined by `≲-prop`, i.e.
;; iff there exist an injection $f$ between $e_1$ and $e_2$.

