{-# OPTIONS --safe #-}
module ConcatInjective where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Properties
-- you can import other functions from the stdlib here

++-injectiveʳ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ b ≡ a ++ c → b ≡ c
++-injectiveʳ [] b c eq = eq
++-injectiveʳ (x ∷ a) b c eq = ++-injectiveʳ a b c (∷-injectiveʳ eq)

-- pretty hard
-- try to use cong to convert to an eazier problem
++-injectiveˡ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ c ≡ b ++ c → a ≡ b
++-injectiveˡ a b c eq = trans (sym (reverse-involutive a))
                        (sym (trans (sym (reverse-involutive b))
                        (cong reverse (++-injectiveʳ ( reverse c) (reverse b) (reverse a)
                        (trans (sym (reverse-++-commute b c))
                        (sym (trans (sym (reverse-++-commute a c))
                        (cong reverse eq))))))))
