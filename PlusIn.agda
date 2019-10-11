{-# OPTIONS --safe #-}
module PlusIn where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

inSucc : (a b : ℕ) -> suc a ≡ suc b -> a ≡ b
inSucc zero zero t = refl
inSucc (suc a) (suc .a) refl = cong suc refl

inPlusSucc : (a b : ℕ) -> a + suc a ≡ b + suc b -> a + a ≡ b + b
inPlusSucc a b t = inSucc (a + a) (b + b) (trans (trans (sym (+-suc a a)) t) (+-suc b b))

invert : (a b : ℕ) → a + a ≡ b + b → a ≡ b
invert zero zero t = refl
invert (suc a) (suc b) t =
       cong suc
         (invert a b (inPlusSucc a b (inSucc (a + suc a) (b + suc b) t)))
