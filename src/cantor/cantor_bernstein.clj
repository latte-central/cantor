(ns cantor.cantor-bernstein
  "A proof of the Cantor-Bernstein(-Schroeder) theorem
  in LaTTe"

  (:refer-clojure :exclude [and or not set])
  
  (:require
   ;; for notebook presentation
   ;;[nextjournal.clerk :as clerk]
   ;;[nextjournal.clerk.viewer :as v]

   ;; latte dependencies
   [latte.core :as latte
    :refer [definition defthm defaxiom defnotation
            forall lambda defimplicit deflemma qed
            assume have pose proof try-proof lambda forall]]

   ;; propositional logic
   [latte-prelude.prop :as p :refer [and and* or not]]

   ;; equality
   [latte-prelude.equal :as eq :refer [equal]]

   ;; basic sets
   [latte-sets.set :as s :refer [set elem subset seteq]]
   [latte-sets.quant :as sq :refer [forall-in exists-in]]

   ;; boolean algebra for sets
   [latte-sets.algebra :as alg :refer [inter diff disjoint]]

   ;; basic relations
   [latte-sets.rel :as rel :refer [rel]]
   [latte-sets.ralgebra :as ralg :refer [rinverse]]

   
   ;; relations as partial functions
   [latte-sets.pfun :as pfun :refer [functional serial injective surjective bijective injection bijection
                                     image]]
   
   ;; quantifying sets
   [latte-sets.powerset :as pset :refer [powerset set-ex]]

   ;; quanoutifying relations
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

;; This allows us to define what is an **injection** in the
;; realm of sets and partial functions.

(comment
  (definition injection
    [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
    (and* (functional f s1 s2)
          (serial f s1 s2)
          (injective f s1 s2)))
  )

;; ## Comparing sets (take 2)

;; We have now everything we need to give a formal definition
;; for a set to be *smaller* than another set, which is valid
;; even in the infinite case.

;; First, we formalize the set of (relational) functions
;; that are injective from domain $e_1$ and range $e_2$.

(definition ≲-prop
  [[?T ?U :type], s1 (set T), s2 (set U)]
  (lambda [f (rel T U)] (injection f s1 s2)))


;; In the traditional notation we would write this set as:
;; $$\{f \in e_1 \rightarrow e_2  \mid ∀x ∈ e_1, \forall y ∈ e_2,~f(x) = f(y) \implies x = y \}$$
;; (keeping implicit the details of what makes $f$ a total function)

;; This gives our definition of the *smaller-than* comparator for sets
;; as follows:

(definition ≲
  "Set `s1` is *smaller* than set `s2`
(according to Cantor)."
  [[?T ?U :type], s1 (set T), s2 (set U)]
  (rel-ex (≲-prop s1 s2)))

;; The informal meaning is that $e_1$ is *smaller than* $e_2$,
;; which is denoted by $e_1 ≲ e_2$  (or `(≲ s1 s2)` in the Clojure notation)
;; iff there exists a relation $f$ in the set defined by `≲-prop`, i.e.
;; iff there exist an injection $f$ between $e_1$ and $e_2$.

;; ## To be : The Same

;; The next question is: what is it to be *the same* for sets ?
;; For this we need a few more definitions.
;; First, we define what is it for a function to be surjective :

(comment
  (definition surjective
    [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
    (forall-in [y s2]
       (exists-in [x s1]
          (f x y)))) 
)

;; For each image $y$ of $f$ in $s_2$, there si an element $x$ of the domain
;; $s_1$ (i.e. an antecedent) such that $f(x)=y$. Put in other terms,
;; the whole set $s_2$ is "covered" by the function $f$.

;; From this, we obtain a notion of a surjection for partial functions:

(comment
  (definition surjection
    [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
    (and* (functional f s1 s2)
          (serial f s1 s2)
          (surjective f s1 s2)))
)

;; Now, to be the same is to be *at the same time* an injection and
;; a surjection, in which case we say that it is a **bijection**
;; So a bijective function is both injective and surjective.

(comment
  (definition bijective
    [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
    (and (injective f s1 s2)
         (surjective f s1 s2)))
  )

;; Which leads to the following definition for a bijection :

(comment
  (definition bijection
    [[?T ?U :type] [f (rel T U)] [s1 (set T)] [s2 (set U)]]
    (and* (functional f s1 s2)
          (serial f s1 s2)
          (bijective f s1 s2)))
)

;; We will denote by $s_1 \approx s_2$ the fact that the sets $s_1$ and $s_2$
;; are "the same" and thus that there exists a bijection between them.

(definition ≈-prop
  [[?T ?U :type], s1 (set T), s2 (set U)]
  (lambda [f (rel T U)] (bijection f s1 s2)))

(definition ≈
  "Set `s1` is *the same* as set `s2` (according to Cantor)."
  [[?T ?U :type], s1 (set T), s2 (set U)]
  (rel-ex (≈-prop s1 s2)))

;; ## Statement of the Theorem

;; We have now everything we need to establish the main theorem statement

(defthm cantor-bernstein
  "The Cantor-Bernstein(-Schroeder) theorem"
  [[?T ?U :type], s1 (set T), s2 (set U)]
  (==> (≲ s1 s2) (≲ s2 s1)
       (≈ s1 s2)))

;; This seems very intuitive : if $s_1$ is "smaller" than $s_2$
;; and $s_2$ is "smaller" than $s_1$, then they should be "the same".

;; For finite sets, this is indeed quite intuitive. Since $s_1$ has
;; less elements than $s_2$  (in the worst case, the same number) and
;; $s_2$ has also less elements than $s_1$, then it seems obvious
;; that they have exactly the same number of elements, i.e. the same
;; *cardinality*, and thus they indeed are "the same".
;; What is missing in the reasoning is a proper definition of what
;; it is to be a finite set. Also, we would need to relate the number
;; of elements to the notions of injectivity and surjectivity.
;; At least this gives a strong argument for the truthiness of the
;; theorem.

;; In the case of infinite sets, it is much more difficult to call for 
;; intuition (except *after* we demonstrated the theorem).
;; And in fact, we will see that the proof is not trivial (not difficult 
;; either, for set theorists)

;; ## Proof from The Book

;; There are in fact several proofs of Cantor-Bernstein theorem. I have chosen a proof scheme
;; that is not *too* cumbersome to formalize. Is it mostly based on the proof
;; presented in D.W. Cunningham book
;; cf. https://www.cambridge.org/fr/academic/subjects/mathematics/logic-categories-and-sets/set-theory-first-course

;; A crucial, and quite technical, lemma for the proof is the following one.

(definition round-trip-prop
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (and (subset X s1)
       (seteq (image g (diff s2 (image f X s2)) s1)
              (diff s1 X))))

(deflemma round-trip
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (set-ex (lambda [X (set T)] (round-trip-prop f g s1 s2 X))))

;; This is quite a mouthfull! This relies on several definitions we have
;; not yet presented.

;; The definition is parameterized by two partial functions:
;;
;;   - a function $f : s_1 \rightarrow s_2$
;;   - a function $g : s_2 \rightarrow s_1$, i.e. the other way around
;;
;; The main statement is that there exists a subset $X$ of $s_1$ such
;; that the following two sets are equal:
;;
;;   - the first set is the image through $g$ of the set $s_2 \setminus f[X]$
;; with $f[X]$ the image of set $X$ through $f$. So we take $s_2$ and we remove
;; all its elements $y$ such that $f(x)=y$ with $x \in X$. We then keep $g(y)$ which
;; is an element of $s_1$.
;;   - the second set is simply $s_1 \setminus X$.
;;
;; So, intuitively, what this lemma says is that the elements of the set $X$ that we are looking for
;; may be removed from $s_1$ in two distinct ways: (1) removing them indirectly in the range $s_2$
;; and then going back in the domain using $g$, or (2) directly removing them in the domain $s_1$.
;; And these two ways are deemed identical.

;; To prove this lemma, we use the following definition :

(definition rt-fun
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (lambda [C (set T)]
    (diff s1 (image g (diff s2 (image f C s2)) s1))))

;; This function enjoys a few properties. The first one is as follows :

(deflemma rt-fun-prop1
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (forall [C (set T)]
    (==> (subset C s1)
         (subset ((rt-fun f g s1 s2) C) s1))))

(proof 'rt-fun-prop1-lemma
  (assume [C _
           HC _]
    (assume [x T
             Hx (elem x ((rt-fun f g s1 s2) C))]

      "We have now to prove `(elem x s1)`"

      "Let's first restate the hypothesis `Hx`:"
      (have Hx' (elem x (diff s1 (image g (diff s2 (image f C s2)) s1)))
            :by Hx)

      "This is trivial since `s1` minus something is a subst of `s1`"
      (have <a> (elem x s1) :by ((alg/diff-subset s1 (image g (diff s2 (image f C s2)) s1))
                                 x Hx'))))
  (qed <a>))

;; Moreover, we have the following property:

(deflemma rt-fun-prop2
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (forall [C (set T)]
    (seteq (diff s1 ((rt-fun f g s1 s2) C))
           (image g (diff s2 (image f C s2)) s1))))

(proof 'rt-fun-prop2-lemma
  (assume [C (set T)]
    "Subset case"
    (assume [x T
             Hx (elem x (diff s1 ((rt-fun f g s1 s2) C)))]
      "We use the fact that `X / X / Y` is the same set as `X ∩ Y`"
      (have <a1> (elem x (inter s1 (image g (diff s2 (image f C s2)) s1)))
            :by ((p/and-elim-left (alg/diff-diff s1 (image g (diff s2 (image f C s2)) s1)))
                 x Hx))
      (have <a> (elem x (image g (diff s2 (image f C s2)) s1))
            :by (p/and-elim-right <a1>)))

    "Superset case"
    (assume [x T
             Hx (elem x (image g (diff s2 (image f C s2)) s1))]
      (have <b> (elem x s1) :by (p/and-elim-left Hx))
      "By contradiction"
      (assume [Hcontra (elem x ((rt-fun f g s1 s2) C))]
        (have <c> p/absurd :by ((p/and-elim-right Hcontra) Hx)))
      
      (have <d> (elem x (diff s1 ((rt-fun f g s1 s2) C)))
            :by (p/and-intro <b> <c>)))

    (have <e> _ :by (p/and-intro <a> <d>)))
  (qed <e>))

(deflemma round-trip-cond
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (forall  [X (set T)]
    (==> (subset X s1)
         (seteq ((rt-fun f g s1 s2) X) X)
         (round-trip-prop f g s1 s2 X))))

(proof 'round-trip-cond-lemma
  (assume [X _
           HX1 _
           HX2 _]
    (pose P := (lambda [Z (set T)]
                 (seteq (diff s1 Z)
                        (image g (diff s2 (image f X s2)) s1))))
    (have <a1> (P ((rt-fun f g s1 s2) X))
          :by ((rt-fun-prop2 f g s1 s2) X))
    (have <a2> (P X) :by ((s/seteq-subst-prop P ((rt-fun f g s1 s2) X) X)
                         HX2 <a1>))
    (have <a> _ :by ((s/seteq-sym (diff s1 X) (image g (diff s2 (image f X s2)) s1))
                     <a2>))

    (have <b> (round-trip-prop f g s1 s2 X)
          :by (p/and-intro HX1 <a>)))

  (qed <b>))

(deflemma rt-claim1
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (forall [C D (set T)]
    (==> (subset C D)
         (subset ((rt-fun f g s1 s2) C) ((rt-fun f g s1 s2) D)))))

(proof 'rt-claim1-lemma
  (assume [C _ D _ Hsub _]

    (have <a> (subset (image f C s2)
                      (image f D s2))
          :by ((pfun/image-subset-monotonous f C D s2) Hsub))

    (have <b> (subset (diff s2 (image f D s2))
                      (diff s2 (image f C s2)))
          :by ((alg/diff-subset-antimonotonous s2 
                                               (image f C s2) 
                                               (image f D s2)) 
               <a>))

    (have <c> (subset (image g (diff s2 (image f D s2)) s1)
                      (image g (diff s2 (image f C s2)) s1))
          :by ((pfun/image-subset-monotonous g 
                                             (diff s2 (image f D s2)) 
                                             (diff s2 (image f C s2)) s1)
               <b>))

    (have <d> (subset ((rt-fun f g s1 s2) C) ((rt-fun f g s1 s2) D))
          :by ((alg/diff-subset-antimonotonous s1 
                                               (image g (diff s2 (image f D s2)) s1)
                                               (image g (diff s2 (image f C s2)) s1))
               <c>)))

  (qed <d>))

(definition rt-set
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (lambda [s (set T)]
    (and (subset s s1) (subset ((rt-fun f g s1 s2) s) s))))

(definition rt-inter
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (pset/intersections (rt-set f g s1 s2)))

(deflemma rt-inter-prop1
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (subset (rt-inter f g s1 s2) s1))

(proof 'rt-inter-prop1-lemma
  (have <a> (subset s1 s1) :by (s/subset-refl s1))
  (have <b> (subset ((rt-fun f g s1 s2) s1) s1)
        :by ((rt-fun-prop1 f g s1 s2) s1 <a>))
  (have <c> (pset/set-elem s1 (rt-set f g s1 s2))
        :by (p/and-intro <a> <b>))
  (have <d> (subset (rt-inter f g s1 s2) s1)
        :by ((pset/intersections-lower-bound (rt-set f g s1 s2))
             s1 <c>))
  (qed <d>))

(deflemma rt-inter-prop2
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (subset ((rt-fun f g s1 s2) (rt-inter f g s1 s2)) s1))

(proof 'rt-inter-prop2-lemma
  (qed ((rt-fun-prop1 f g s1 s2)
        (rt-inter f g s1 s2)
        (rt-inter-prop1 f g s1 s2))))

(deflemma rt-fun-inter-fixpoint
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (seteq ((rt-fun f g s1 s2) (rt-inter f g s1 s2))
         (rt-inter f g s1 s2)))

(deflemma rt-fun-inter-fix-sub
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (subset ((rt-fun f g s1 s2) (rt-inter f g s1 s2))
          (rt-inter f g s1 s2)))

(proof 'rt-fun-inter-fix-sub-lemma
  (assume [y T
           Hy (elem y ((rt-fun f g s1 s2) (rt-inter f g s1 s2)))]
    (assume [s (set T)
             Hs (pset/set-elem s (rt-set f g s1 s2))]
      "We need to show that y∈s"
      (have <a> (subset (rt-inter f g s1 s2) s)
            :by ((pset/intersections-lower-bound (rt-set f g s1 s2)) s Hs))
      (have <b> (subset ((rt-fun f g s1 s2) (rt-inter f g s1 s2))
                        ((rt-fun f g s1 s2) s))
            :by ((rt-claim1 f g s1 s2) (rt-inter f g s1 s2) s <a>))
      (have <c> (subset ((rt-fun f g s1 s2) s) s)
            :by (p/and-elim-right Hs))
      (have <d> (subset ((rt-fun f g s1 s2) (rt-inter f g s1 s2)) s)
            :by ((s/subset-trans ((rt-fun f g s1 s2) (rt-inter f g s1 s2))
                                 ((rt-fun f g s1 s2) s)
                                 s) <b> <c>))
      (have <e> (elem y s) :by (<d> y Hy))))
  (qed <e>))

(deflemma rt-fun-inter-fix-super
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (subset (rt-inter f g s1 s2)
          ((rt-fun f g s1 s2) (rt-inter f g s1 s2))))

(proof 'rt-fun-inter-fix-super-lemma
  (have <a> (subset ((rt-fun f g s1 s2) (rt-inter f g s1 s2))
                    (rt-inter f g s1 s2))
        :by (rt-fun-inter-fix-sub f g s1 s2))
  (have <b> (subset ((rt-fun f g s1 s2) ((rt-fun f g s1 s2) (rt-inter f g s1 s2)))
                    ((rt-fun f g s1 s2) (rt-inter f g s1 s2)))
        :by ((rt-claim1 f g s1 s2) 
             ((rt-fun f g s1 s2) (rt-inter f g s1 s2))
             (rt-inter f g s1 s2)
             <a>))
  (have <c> (pset/set-elem ((rt-fun f g s1 s2) (rt-inter f g s1 s2)) (rt-set f g s1 s2))
        :by (p/and-intro (rt-inter-prop2 f g s1 s2) <b>))
  (qed ((pset/intersections-lower-bound (rt-set f g s1 s2))
        ((rt-fun f g s1 s2) (rt-inter f g s1 s2)) <c>)))

(proof 'rt-fun-inter-fixpoint-lemma
  (qed (p/and-intro (rt-fun-inter-fix-sub f g s1 s2)
                    (rt-fun-inter-fix-super f g s1 s2))))


(deflemma round-trip-inter
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)]]
  (round-trip-prop f g s1 s2 (rt-inter f g s1 s2)))

(proof 'round-trip-inter-lemma
  (qed ((round-trip-cond f g s1 s2)
        (rt-inter f g s1 s2)
        (rt-inter-prop1 f g s1 s2)
        (rt-fun-inter-fixpoint f g s1 s2))))

(proof 'round-trip-lemma
  (qed ((pset/set-ex-intro (lambda [X (set T)] (round-trip-prop f g s1 s2 X))
                           (rt-inter f g s1 s2))
        (round-trip-inter f g s1 s2))))


(deflemma ct-claim1
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (==> (injective g s2 s1)
       ;; right part of round-trip-prop
       (seteq (image g (diff s2 (image f X s2)) s1)
              (diff s1 X))
       (subset (image g (image f X s2) s1) X)))

(proof 'ct-claim1-lemma
  (assume [Hginj _
           Hrt _]
    (have <a> (disjoint (image f X s2) 
                        (diff s2 (image f X s2)))
          :by (alg/disjoint-diff (image f X s2) s2))

    (have <b2> (subset (image f X s2) s2) :by (pfun/image-subset f X s2))
    (have <b3> (subset (diff s2 (image f X s2)) s2) :by (alg/diff-subset s2 (image f X s2)))

    "g[f[X]] ∩ g[s2 - f[X]] = ∅"
    (have <b> (disjoint (image g (image f X s2) s1)
                        (image g (diff s2 (image f X s2)) s1))
          :by ((pfun/injection-img-inter g (image f X s2) (diff s2 (image f X s2)) s2 s1)
               Hginj <b2> <b3> <a>))

    "and since g[s2 - f[X]] = s1 - X   (from round-trip-prop)"
    "then g[f[X]] ∩ (s1 - X) = ∅"
    (have <d> (disjoint (image g (image f X s2) s1) (diff s1 X)) 
          :by ((s/seteq-subst-prop (lambda [$ (set T)]
                                     (disjoint (image g (image f X s2) s1) $))
                                   (image g (diff s2 (image f X s2)) s1)
                                   (diff s1 X))
                     Hrt <b>))
    "Also g[f[X]] ⊆ s1"
    (have <e> (subset (image g (image f X s2) s1) s1)
          :by (pfun/image-subset g (image f X s2) s1))

    "Then we can conclude g[f[X]] ⊆ X"
    (have <g> (subset (image g (image f X s2) s1) X)
          :by ((alg/disjoint-diff-subset (image g (image f X s2) s1) X s1)
               <d> 
               <e>)))
  (qed <g>))


(definition ct-rel
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (lambda [x T]
    (lambda [y U]
      (and (==> (elem x X) (f x y))
           (==> (elem x (diff s1 X)) ((rinverse g) x y))))))

(deflemma ct-rel-left
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (forall [x T]
    (forall [y U]
      (==> (elem x X)
           (f x y)
           ((ct-rel f g s1 s2 X) x y)))))

(proof 'ct-rel-left-lemma
  (assume [x T
           y U
           H1 (elem x X)
           H2 (f x y)]
    "left part - trivial "
    (assume [Hleft (elem x X)]
      (have <a> (f x y) :by H2))

    "right part - by contradiction"
    (assume [Hright (elem x (diff s1 X))]
      (have <b1> p/absurd :by ((p/and-elim-right Hright) H1))
      (have <b> _ :by (<b1> ((rinverse g) x y))))

    (have <c> ((ct-rel f g s1 s2 X) x y)
          :by (p/and-intro <a> <b>)))
  (qed <c>))

(deflemma ct-rel-right
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (forall [x T]
    (forall [y U]
      (==> (elem x (diff s1 X))
           ((rinverse g) x y)
           ((ct-rel f g s1 s2 X) x y)))))

(proof 'ct-rel-right-lemma
  (assume [x T
           y U
           Hx (elem x (diff s1 X))
           Hg ((rinverse g) x y)]

    "left part - contradiction"
    (assume [Hleft (elem x X)]
      (have <a1> p/absurd :by ((p/and-elim-right Hx) Hleft))
      (have <a> _ :by (<a1> (f x y))))
    
    "right part - trivial"
    (assume [Hright (elem x (diff s1 X))]
      (have <b> _ :by Hg))

    (have <c> ((ct-rel f g s1 s2 X) x y)
          :by (p/and-intro <a> <b>)))

  (qed <c>))

(deflemma ct-rel-functional
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (==> (functional f s1 s2)
       (injective g s2 s1)
       (functional (ct-rel f g s1 s2 X) s1 s2)))

(proof 'ct-rel-functional-lemma
  (assume [Hffun _
           Hginj _]
    (pose h := (ct-rel f g s1 s2 X))
    (assume [x T Hx (elem x s1)]
      (assume [y1 U Hy1 (elem y1 s2)
               y2 U Hy2 (elem y2 s2)
               Hh1 (h x y1)
               Hh2 (h x y2)]
        "We have to show: y1=y2"

        "We proceed by case analysis"
        (have <xsplit> (or (elem x X)
                           (elem x (diff s1 X)))
            :by ((alg/diff-split s1 X) x Hx))

        (assume [Hleft (elem x X)]
          (have <a> (f x y1) :by ((p/and-elim-left Hh1) Hleft))
          (have <b> (f x y2) :by ((p/and-elim-left Hh2) Hleft))

          (have <c> (equal y1 y2)
                :by ((sq/single-in-elim (Hffun x Hx) y1 y2)
                     Hy1 Hy2 <a> <b>)) )

        (assume [Hright (elem x (diff s1 X))]
          (have <d> (g y1 x) :by ((p/and-elim-right Hh1) Hright))
          (have <e> (g y2 x) :by ((p/and-elim-right Hh2) Hright))
          (have <f> (equal y1 y2)
                :by (Hginj y1 Hy1 y2 Hy2 x Hx x Hx <d> <e> (eq/eq-refl x))))

        (have <g> (equal y1 y2) :by (p/or-elim <xsplit> <c> <f>)))

      (have <h> _ :by ((sq/single-in-intro s2 (lambda [$ U] (h x $))) <g>)))

    (have <i> (functional (ct-rel f g s1 s2 X) s1 s2)
          :by <h>))

  (qed <i>))

(deflemma ct-rel-serial
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (==> (serial f s1 s2)
       ;; right part of round-trip lemma
       (seteq (image g (diff s2 (image f X s2)) s1)  ;; this replaces surjectivity for g
              (diff s1 X))
       (serial (ct-rel f g s1 s2 X) s1 s2)))

(proof 'ct-rel-serial-lemma
  (assume [Hfser _
           Hrt _]
    (pose h := (ct-rel f g s1 s2 X))

    (assume [x T Hx (elem x s1)]

      "We have to show:  ∃y∈s2, (h x y)"

      "We proceed by case analysis"
      (have <xsplit> (or (elem x X)
                         (elem x (diff s1 X)))
            :by ((alg/diff-split s1 X) x Hx))
      
      (assume [Hleft (elem x X)]
        (have <a> (sq/exists-in [y s2] (f x y))
              :by (Hfser x Hx))
        
        (assume [y U Hy (elem y s2)
                 Hf (f x y)]
          (have <b1> (h x y) :by ((ct-rel-left f g s1 s2 X) x y Hleft Hf))
          (have <b> (exists-in [y s2] (h x y))
                :by ((sq/ex-in-intro s2 (lambda [$ U] (h x $)) y) Hy <b1>)))

        (have <c> (exists-in [y s2] (h x y)) :by (sq/ex-in-elim <a> <b>)))

      (assume [Hright (elem x (diff s1 X))]
        (have <d> (elem x (image g (diff s2 (image f X s2)) s1))
              :by ((p/and-elim-right Hrt) x Hright))

        (have <e> (exists-in [y (diff s2 (image f X s2))] (g y x))
              :by (p/and-elim-right <d>))

        (assume [y U Hy (elem y (diff s2 (image f X s2)))
                 Hg (g y x)]
          (have <f1> (elem y s2) :by (p/and-elim-left Hy))
          (have <f2> (h x y) :by ((ct-rel-right f g s1 s2 X) x y Hright Hg))
          (have <f> (exists-in [y s2] (h x y))
                :by ((sq/ex-in-intro s2 (lambda [$ U] (h x $)) y) <f1> <f2>)))

        (have <g> (exists-in [y s2] (h x y)) :by (sq/ex-in-elim <e> <f>)))
        
      (have <h> _ :by (p/or-elim <xsplit> <c> <g>)))

    (have <i> (serial (ct-rel f g s1 s2 X) s1 s2) :by <h>))
 
  (qed <i>))

(deflemma ct-claim2
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (==> (injective f s1 s2)
       (functional g s2 s1)
       (injective g s2 s1)
       ;; right part of round-trip-prop
       (seteq (image g (diff s2 (image f X s2)) s1)
              (diff s1 X))
       (injective (ct-rel f g s1 s2 X) s1 s2)))

(proof 'ct-claim2-lemma
  (assume [Hfinj _
           Hgfun _
           Hginj _
           Hrt _]
    (pose h := (ct-rel f g s1 s2 X))
    (assume [x1 T Hx1 (elem x1 s1)
             x2 T Hx2 (elem x2 s1)
             y1 U Hy1 (elem y1 s2)
             y2 U Hy2 (elem y2 s2)
             Hh1 (h x1 y1)
             Hh2 (h x2 y2)
             Heq (equal y1 y2)]

      (have <claim> (subset (image g (image f X s2) s1) X)
            :by ((ct-claim1 f g s1 s2 X)
                 Hginj Hrt))


      "We have to show that x1=x2"
      "We proceed by case analysis"

      (have <x1split> (or (elem x1 X)
                           (elem x1 (diff s1 X)))
            :by ((alg/diff-split s1 X) x1 Hx1))

      
      (assume [Hx1left (elem x1 X)]
      
        (have <a> (f x1 y1) :by ((p/and-elim-left Hh1) Hx1left))

        (have <x2split> (or (elem x2 X)
                            (elem x2 (diff s1 X)))
              :by ((alg/diff-split s1 X) x2 Hx2))

        
        (assume [Hx2left (elem x2 X)]

          (have <b1> (f x2 y2) :by ((p/and-elim-left Hh2) Hx2left))

          "Since f is injective we're done"
          (have <b> (equal x1 x2) :by (Hfinj x1 Hx1 x2 Hx2 y1 Hy1 y2 Hy2 <a> <b1> Heq)))

        (assume [Hx2right (elem x2 (diff s1 X))]
          
          (have <c1> (g y2 x2) :by ((p/and-elim-right Hh2) Hx2right))
          
          (have <c2> (f x1 y2) :by (eq/eq-subst (lambda [$ U] (f x1 $)) Heq <a>))

          (have <c3> (elem y2 (image f X s2)) 
                :by (p/and-intro Hy2 
                                 ((sq/ex-in-intro X (lambda [$ T] (f $ y2)) x1)
                                  Hx1left <c2>)))

          (have <c4> (elem x2 (image g (image f X s2) s1))
                :by (p/and-intro Hx2 
                                 ((sq/ex-in-intro (image f X s2) (lambda [$ U] (g $ x2)) y2)
                                  <c3> <c1>)))


          (have <c5> (elem x2 X) :by (<claim> x2 <c4>))

          "We reached a contradiction"
          (have <c6> p/absurd :by ((p/and-elim-right Hx2right) <c5>))
          
          (have <c> (equal x1 x2) :by (<c6> (equal x1 x2))))

        "We synthetize the two rught subcases"
        (have <d> (equal x1 x2) :by (p/or-elim <x2split> <b> <c>)))

      (assume [Hx1right (elem x1 (diff s1 X))]
        
        (have <e> (g y1 x1) :by ((p/and-elim-right Hh1) Hx1right))

        (have <x2split'> (or (elem x2 X)
                            (elem x2 (diff s1 X)))
              :by ((alg/diff-split s1 X) x2 Hx2))
      
        (assume [Hx2left (elem x2 X)]
          
          (have <f> (f x2 y1) :by (eq/eq-subst (lambda [$ U] (f x2 $)) (eq/eq-sym Heq) ((p/and-elim-left Hh2) Hx2left)))

           (have <g1> (elem y1 (image f X s2)) 
                 :by (p/and-intro Hy1 
                                  ((sq/ex-in-intro X (lambda [$ T] (f $ y1)) x2)
                                   Hx2left <f>)))


           (have <g2> (elem x1 (image g (image f X s2) s1))
                 :by (p/and-intro Hx1 
                                  ((sq/ex-in-intro (image f X s2) (lambda [$ U] (g $ x1)) y1)
                                   <g1> <e>)))

           (have <g3> (elem x1 X) :by (<claim> x1 <g2>))

           (have <g4> p/absurd :by ((p/and-elim-right Hx1right) <g3>))

           (have <g> (equal x1 x2) :by (<g4> (equal x1 x2))))

        (assume [Hx2right (elem x2 (diff s1 X))]
          
          (have <h1> ((rinverse g) x1 y1) :by <e>)
          (have <h2> ((rinverse g) x2 y2) :by ((p/and-elim-right Hh2) Hx2right))
          (have <h3> (injective (rinverse g) s1 s2)
                :by ((pfun/function-rinverse-injective g s2 s1) Hgfun))

          "Since h is injective"
          (have <h> (equal x1 x2) :by (<h3> x1 Hx1 x2 Hx2 y1 Hy1 y2 Hy2 <h1> <h2> Heq)))

        "We synthetize the two right subcases"
        (have <i> (equal x1 x2) :by (p/or-elim <x2split'> <g> <h>)))
      
      "We synthetize the two left subcases"
      (have <j> (equal x1 x2) :by (p/or-elim <x1split> <d> <i>)))

    (have <k> (injective (ct-rel f g s1 s2 X) s1 s2) :by <j>))

  (qed <k>))

(deflemma ct-claim3
  [[?T ?U :type] [f (rel T U)] [g (rel U T)] [s1 (set T)] [s2 (set U)] [X (set T)]]
  (==> (injective f s1 s2)
       (functional g s2 s1)
       (serial g s2 s1)
       (injective g s2 s1)
       (round-trip-prop f g s1 s2 X)
       (surjective (ct-rel f g s1 s2 X) s1 s2)))

(proof 'ct-claim3-lemma
  (assume [Hfinj _
           Hgfun _
           Hgser _
           Hginj _
           Hrt _]
    (pose h := (ct-rel f g s1 s2 X))
    (assume [y U Hy (elem y s2)]

      "We have to find some x∈s1 such that (h x y)"

      "We proceed by case analysis on y"
      (have <ysplit> (or (elem y (image f X s2))
                         (elem y (diff s2 (image f X s2))))
            :by ((alg/diff-split s2 (image f X s2)) y Hy))

      (assume [Hyleft (elem y (image f X s2))]

        (have <a> (exists-in [x X] (f x y)) 
              :by (p/and-elim-right Hyleft)) 
        
        (assume [x T Hx (elem x X)
                 Hf (f x y)]
          
          (have <b1> (elem x s1) :by ((p/and-elim-left Hrt) x Hx))

          (have <b2> (h x y) 
                :by ((ct-rel-left f g s1 s2 X) x y Hx Hf))

          (have <b> (exists-in [x s1] (h x y))
                :by ((sq/ex-in-intro s1 (lambda [$ T] (h $ y)) x)
                     <b1> <b2>)))

        (have <c> _ :by (sq/ex-in-elim <a> <b>)))

      (assume [Hyright (elem y (diff s2 (image f X s2)))]
      
        (have <d1> (elem y s2) :by (p/and-elim-left Hyright)) 
    
        (have <d> (exists-in [x s1] (g y x)) :by (Hgser y <d1>))
      
        (assume [x T Hx (elem x s1)
                 Hg (g y x)]

          (have <e1> (elem x (image g (diff s2 (image f X s2)) s1))
                
                :by (p/and-intro 
                     Hx
                     ((sq/ex-in-intro (diff s2 (image f X s2))
                                      (lambda [$ U] (g $ x))
                                      y)
                      Hyright Hg)))
          
          (have <e2> (subset (image g (diff s2 (image f X s2)) s1) (diff s1 X))
                :by (p/and-elim-left (p/and-elim-right Hrt)))

          (have <e3> (elem x (diff s1 X))
                :by (<e2> x <e1>))

          (have <e4> (h x y) :by ((ct-rel-right f g s1 s2 X)
                                  x y <e3> Hg))

          (have <e> (exists-in [x s1] (h x y))
                :by ((sq/ex-in-intro s1 (lambda [$ T] (h $ y)) x)
                     Hx <e4>)))

        (have <f> _ :by (sq/ex-in-elim <d> <e>)))

      (have <g> (exists-in [x s1] ((ct-rel f g s1 s2 X) x y)) 
            :by (p/or-elim <ysplit> <c> <f>)))

    (have <h> (surjective (ct-rel f g s1 s2 X) s1 s2) :by <g>))

  (qed <h>))


;; And now the proof of the main theorem

(proof 'cantor-bernstein-thm
  (assume [H1 (≲ s1 s2) 
           H2 (≲ s2 s1)]
    
    "We have to prove (≈ s1 s2)"

    "Leveraging H1"
    (assume [f (rel T U)
             Hf (injection f s1 s2)]

      "Leveraging H2"
      (assume [g (rel U T)
               Hg (injection g s2 s1)]

        "Leveraging the round-trip lemma"
        (assume [X (set T) 
                 Hrt (round-trip-prop f g s1 s2 X)]

          "Our candidate bijection"
          (pose h := (ct-rel f g s1 s2 X))

          "First, we prove that it is indeed bijective"
          (have <a1> (injective f s1 s2)
                :by (p/and-elim* 3 Hf))
          (have <a2> (functional g s2 s1)
                :by (p/and-elim* 1 Hg))
          (have <a3> (injective g s2 s1)
                :by (p/and-elim* 3 Hg))

          (have <a> (injective h s1 s2)
                :by ((ct-claim2 f g s1 s2 X)
                     <a1> <a2> <a3> (p/and-elim-right Hrt)))

          (have <b1> (serial g s2 s1)
                :by (p/and-elim* 2 Hg))

          (have <b> (surjective h s1 s2)
                :by ((ct-claim3 f g s1 s2 X)
                     <a1> <a2> <b1> <a3> Hrt))

          (have <c> (bijective h s1 s2)
                :by (p/and-intro <a> <b>))

          "Now let's prove that it is functional (i.e. single-valued)"
          
          (have <d1> (functional f s1 s2) :by (p/and-elim* 1 Hf))

          (have <d> (functional h s1 s2)
                :by ((ct-rel-functional f g s1 s2 X)
                     <d1> <a3>))


          "And finally let's prove it is serial (i.e. total on s1)"

          (have <e1> (serial f s1 s2) :by (p/and-elim* 2 Hf))

          (have <e> (serial h s1 s2)
                :by ((ct-rel-serial f g s1 s2 X)
                     <e1> (p/and-elim-right Hrt)))

          (have <f> (bijection h s1 s2)
                :by (p/and-intro* <d> <e> <c>))

          (have <g> (rel-ex (≈-prop s1 s2)) :by ((prel/rel-ex-intro (≈-prop s1 s2) h) <f>)))

        "Apply the round-trip lemma"
        (have <h> (≈ s1 s2) :by ((pset/set-ex-elim (lambda [$ (set T)]
                                                     (round-trip-prop f g s1 s2 $)) 
                                                   (≈ s1 s2))
                                 (round-trip f g s1 s2) <g>)))

      (have <i> (≈ s1 s2) :by ((prel/rel-ex-elim (≲-prop s2 s1) (≈ s1 s2)) H2 <h>)))

    (have <j> (≈ s1 s2) :by ((prel/rel-ex-elim (≲-prop s1 s2) (≈ s1 s2)) H1 <i>)))

  (qed <j>))
