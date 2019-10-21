{-# OPTIONS --safe #-}
module ++-Identity where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.HeterogeneousEquality
open import Data.Vec

{-
Url: https://www.codewars.com/kata/heterogeneous-equality-on-sized-vectors
Description:
Agda's default equality type is defined in Agda.Builtin.Equality:

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
instance refl : x ≡ x
As you can see in the above definition, the two args taken by the equality type are of the same type A. In other words, it's homogeneous.

Most of the time, homogeneous equality works fine, but if we want to prove equality of objects with different type, the compiler would throw an error "type mismatch".

So we have heterogeneous equality defined in Relation.Binary.HeterogeneousEquality:

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
refl : x ≅ x
Try to prove xs ++ [] ≅ xs with heterogeneous equality.

Hint: read the module Relation.Binary.HeterogeneousEquality before proving the theorem.
-}

consComm : ∀ {n} {A : Set} (x : A) (xs : Vec A n) -> x ∷  xs ++ [] ≅ x ∷ (xs ++ [])
consComm x [] = refl
consComm x (x₁ ∷ xs) = cong (x ∷_) (consComm x₁ xs)


++-identityʳ : ∀ {n} {A : Set} (xs : Vec A n) → xs ++ [] ≅ xs
++-identityʳ {.0} {A} [] = refl
++-identityʳ {.(suc _)} {A} (x ∷ xs) = icong (Vec A) (+-identityʳ _) (\w -> x ∷ w) (++-identityʳ xs)
