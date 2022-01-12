(ns cantor-bernstein.theorem
  "A proof of the Cantor-Bernstein(-Schroeder) theorem
  in LaTTe"
  (:require
   ;; for notebook presentation
   [nextjournal.clerk :as clerk]
   [nextjournal.clerk.viewer :as v]

   ;; latte dependencies
   [latte.core :as latte
    :refer [definition defthm defaxiom defnotation
            forall lambda defimplicit deflemma qed
            assume have pose proof try-proof lambda forall]]))

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
;; Here is the definition proposed by the [[latte-predlude]]:
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
;; *type-theoretic*. Since we are interested by comparing
;; sets, we need a light more complex but more adequate
;; definition:

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

;; This defines what it is for a *relation* to be injective.
;; To ensure that it is *also* a function, we need also the following:

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

;; We also need the relation/function to be *serial*, i.e. that
;; it is defined on its while domain `from`.

(comment
    "The relation `f` covers all of (is total wrt.) the provided `from` domain set."
    [[?T ?U :type], f (rel T U), from (set T), to (set U)]
    (forall-in [x from]
       (exists-in [y to]
         (f x y)))
    )

