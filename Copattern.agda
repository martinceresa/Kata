{-# OPTIONS --copattern --safe --no-sized-types --guardedness #-}
module Copattern where

-- open import StreamDef
open import Data.Nat
open import Relation.Binary.PropositionalEquality

{-
Url: https://www.codewars.com/kata/pattern-in-the-mirror-and-bisimulation-for-real/
Description:
In this Kata you'll learn copattern and guarded recursion, and how much I like
Coinduction. What you're going to do is essentially the same in this one but
using a different language feature, and I'll show you what you can do more with
this machanism.

We have a coinductive stream:
(Preloaded Code)
I didn't choose Codata.Stream because that's based on sized types.

Comments will help you, don't be afraid.
-}

{- Preloaded: -}
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

-- | Bisimulation as equality
record _==_ {A : Set} (x : Stream A) (y : Stream A) : Set where
  coinductive
  field
    refl-head : head x ≡ head y
    refl-tail : tail x == tail y
open _==_ public

-- Getting started:
module Introduction where

  -- Infinite sequence of `ones`.
  ones : Stream ℕ
  head ones = suc zero
  tail ones = ones

  -- Infinite sequence of give number
  repeat : {A : Set} -> A -> Stream A
  head (repeat a) = a -- your turn
  tail (repeat a) = repeat a

  -- Odd and Even, as you've implemented in:
  -- https://www.codewars.com/kata/tear-me-apart-and-merge-the-pieces-together
  even : ∀ {A} -> Stream A -> Stream A
  head (even a) = head a -- your turn
  tail (even a) = even (tail (tail a)) -- your turn

  odd : ∀ {A} -> Stream A -> Stream A
  odd a = even (tail a)

module Bisimulation where
  open Introduction

  -- Refl for bisimulation
  refl′ : ∀ {A} -> (a : Stream A) -> a == a
  refl-head (refl′ a) = refl -- your turn
  refl-tail (refl′ a) = refl′ (tail a)

  oddEven : ∀ {A} -> (a : Stream A) -> odd a == even (tail a)
  refl-head (oddEven a) = refl -- your turn
  refl-tail (oddEven a) = oddEven (tail (tail a))

module Merge where
  open Bisimulation
  open Introduction

  merge : ∀ {A} -> Stream A -> Stream A -> Stream A
  head (merge a _) = head a -- your turn
  tail (merge a b) = merge b (tail a) -- your turn

  -- Merge! Even! Odd!
  moe : ∀ {A} -> (a : Stream A) -> (merge (even a) (odd a) == a)
  refl-head (moe a) = refl -- your turn
  refl-tail (moe a) = moe (tail a)

