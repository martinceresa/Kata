{-# OPTIONS --cubical --safe #-}
module SymInt where

open import Cubical.Core.Everything
open import Cubical.Data.Nat renaming ( _+_ to _:+:_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.PathSplitEquiv
open import Cubical.HITs.Ints.QuoInt renaming (_+ℤ_ to _+_; ℤ to Z)

{-
Tutorial
Chapter one
Definition of Int:

data ℤ : Set where
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ
  posneg : pos 0 ≡ neg 0
So we can construct Ints:
-}
two : Z
two = pos 2
negTwo : Z
negTwo = neg 2
{- But how does the constructor posneg work?

Let's start from the ≡ definition. It's no longer a datatype, but a lambda. It's
a lambda takes a parameter representing a point on a segment, returns the value
on the point. Each a ≡ b (imagine a b : A) is a segment, where the two endpoints
are a and b respectively.

The instances of a ≡ b are such segments, i0 is the left endpoint while i1 is
the right one.

While a segment has infinite number of points, you can't pattern match it. This
means you cannot simply construct things like

bla : 1 ≡ 2
bla i = if i == i0 then 1 else 2
but we can easily do trivial proofs

-}
-- constant segment 1
sample : 1 ≡ 1
sample i = 1
{-so we have refl:

refl : x ≡ x
refl i = x
there's an unary operator on interval: find the point of symmetry. So we can
flip a path by:

sym : a ≡ b -> b ≡ a
sym inputPath intervalParamOfTheReturnedPath
  = inputPath (~ intervalParamOfTheReturnedPath)

+ As far as I understan things here, (~) = λ i . i1 - i

congruence is function composition:

cong : (F : A -> B) -> {x y : A} -> x ≡ y -> F x ≡ F y
cong f g a = f (g a)

-- cong f inputPath intervalParamOfTheReturnedPath =
--   f (inputPath intervalParamOfTheReturnedPath)
back to our Int, we can prove a lot of interesting things:

0=0 : neg 0 ≡ pos 0
0=0 i = posneg (~ i)

Chapter two
You should understand how does the interval construtor in HITs work. Read this CS StackExchange question.

Chapter three
Read the definitions in Cubical.HITs.HitInt, like this:

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ (pos (suc n)) = sucℤ   (m +ℤ pos n)
m +ℤ (neg (suc n)) = predℤ  (m +ℤ neg n)
m +ℤ _             = m
Now you can do the Kata.
-}

plus0Comm : ∀ a -> pos 0 + a ≡ a
plus0Comm (pos zero) = refl
plus0Comm (pos (suc n)) = cong sucℤ (plus0Comm (pos n))
plus0Comm (neg zero) = posneg
plus0Comm (neg (suc n)) = cong predℤ (plus0Comm (neg n))
plus0Comm (posneg i) = λ i₁ → posneg (i ∧ i₁)

posNegZero : ∀ i -> pos 0 ≡ posneg i
posNegZero i = λ i₁ → posneg (i ∧ i₁)

+-i-zero : ∀ a i → posneg i + a ≡ a
+-i-zero a i = (posneg i + a)
           ≡⟨ cong (λ x → x + a) (sym (posNegZero i)) ⟩
           ( pos 0 + a)
           ≡⟨ plus0Comm a ⟩
           a
           ∎
