{-# OPTIONS --safe #-}
module FlipTreeSym where

open import Relation.Binary.PropositionalEquality
-- open import Preloaded
 
{-
Preloaded:
-}

-- module Preloaded where

data Tree (A : Set) : Set where
  leaf : A → Tree A
  branch : A → Tree A → Tree A → Tree A

flipTree : {A : Set} → Tree A → Tree A
flipTree (leaf x) = leaf x
flipTree (branch x l r) = branch x (flipTree r) (flipTree l)

symflipTreeSym : {A : Set} → (t : Tree A) → flipTree (flipTree t) ≡ t
symflipTreeSym (leaf x) = refl
symflipTreeSym (branch x t t₁) = cong₂ (branch x) (symflipTreeSym t) (symflipTreeSym t₁)

flipTreeSym : {A : Set} → (t : Tree A) → t ≡ flipTree (flipTree t)
flipTreeSym t = sym (symflipTreeSym t)
