{-# OPTIONS --safe #-}
module MagicIsCommutative where

{-
Instructions:
For any binary operator ∙ with (x∙y)∙y=x and y∙(y∙x)=x, we havex∙y=y∙x.

Try to prove this!

(This interesting little proposition comes as an exercise in Introduction to Algebra by Aleksei Ivanovich Kostrikin)
-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; cong ; trans ; sym; refl)

import Relation.Binary.EqReasoning as EqR

record IsMagical {A : Set} (_∙_ : A → A → A) : Set where
  field
    left         : ∀ x y → (x ∙ y) ∙ y  ≡  x
    right        : ∀ x y → y ∙ (y ∙ x)  ≡  x

record IsCommuntative {A : Set} (_∙_ : A → A → A) : Set where
  field
    comm         : ∀ x y → x ∙ y  ≡ y ∙ x

open IsMagical
open IsCommuntative

{-
Paper:
 We know that: Left ∀ x y, y ∙ (y ∙ x) = x.
 So in particular for a given x and y, it holds that:
   Left x (y ∙ x) ≡ (y ∙ x) ∙ ((y ∙ x) ∙ x) = x.
 But now we can use right here^^^^^^^^^^^^^^
 and we get Lemma1 : ∀ x y, (y ∙ x) ∙ y = x

 So,
   x ∙ y
 = < Lemma 1, (y ∙ x) ∙ y = x >
   ((y ∙ x) ∙ y) ∙ y
 = < Right >
     y ∙ x
-}

lemma1 : {A : Set} ( _∙_ : A -> A -> A ) -> IsMagical (_∙_) -> (x y : A) -> ( y ∙ x) ∙ y ≡ x
lemma1 (_∙_) isM x y = sym (trans (sym (right isM x ((y ∙ x)))) (cong (λ e → (y ∙ x) ∙ e) (left isM y x)))

magic-is-commutative : {A : Set} (_∙_ : A → A → A) → IsMagical _∙_ → IsCommuntative _∙_
magic-is-commutative (_∙_)
  magic
  = record { comm = λ x y →
    trans (cong (_∙ y) (sym (lemma1 _∙_ magic x y)))
    (left magic (y ∙ x) y)
    }
