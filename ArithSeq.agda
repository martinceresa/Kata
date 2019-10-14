{-# OPTIONS --safe #-}
module ArithSeq where

open import Data.Nat
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.EqReasoning
----------------------------------------
-- open import Preloaded
-- module Preloaded where
-- open import Data.Nat

arith-sum : ℕ → ℕ
arith-sum zero = zero
arith-sum (suc n) = suc n + arith-sum n

arith-formula : ℕ → ℕ
arith-formula n = ⌊ n * (n + 1) /2⌋
----------------------------------------

{-
Url: https://www.codewars.com/kata/program-verification-number-1-the-sum-of-an-arithmetic-progression/train/agda
Description:
The goal of this kata is to prove that two functions which compute the sum 0 + 1 + 2 + ... + n are equivalent.

Your task is to implement the following function:

arith-eq : (n : ℕ) -> arith-formula n ≡ arith-sum n
arith-eq n = ?

-}

{-
*-distribˡ-+ ≡ ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
*-distribʳ-+ ≡ ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
-}
rewriteLemma : (n : ℕ) -> suc (n + 1 + n * suc (n + 1)) ≡ (2 + (n * 2)) + n * (n + 1)
rewriteLemma n =  begin-equality
               suc (n + 1 + n * suc (n + 1)) ≡⟨ refl ⟩
               1 + n + 1 + n * suc (n + 1) ≡⟨ cong (1 + n + 1 +_) (*-distribˡ-+ n 1 (n + 1)) ⟩
               1 + n + 1 + (n * 1 + n * (n + 1)) ≡⟨ cong (1 + n + 1 +_) (cong (λ x → x + n * (n + 1)) (*-identityʳ n)) ⟩
               1 + n + 1 + (n + n * (n + 1)) ≡⟨ sym (+-assoc (1 + n + 1) n (n * (n + 1))) ⟩
               1 + n + 1 + n + n * (n + 1) ≡⟨ cong (λ x → suc x + n + n * (n + 1)) (trans (+-suc n 0) (cong suc (+-identityʳ n))) ⟩
               2 + n + n + n * (n + 1)  ≡⟨ cong (λ x → 2 + x + n * (n + 1)) (sym (trans (*-comm n 2) (cong (n +_) (+-comm n (0 * n))))) ⟩
               2 + n * 2 + n * (n + 1) ∎

dupFloor : (n m : ℕ) -> ⌊ (n * 2) + m /2⌋ ≡ n + ⌊ m /2⌋
dupFloor zero m = refl
dupFloor (suc n) m = cong suc (dupFloor n m)

lemmaArithForm : (n : ℕ) -> arith-formula (suc n) ≡ suc (n + arith-formula n)
lemmaArithForm n = trans (cong (λ x → ⌊ x /2⌋) (rewriteLemma n))
                   (cong suc (trans (dupFloor n (n * (n + 1))) (cong (n +_) refl)))

arith-eq : (n : ℕ) -> arith-formula n ≡ arith-sum n
arith-eq zero = refl
arith-eq (suc n) = trans (lemmaArithForm n) (cong suc (cong (n +_) (arith-eq n)))
