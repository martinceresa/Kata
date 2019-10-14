{-# OPTIONS --safe --sized-types #-}
module SizedNats where

-- open import Agda.Builtin.Nat public
open import Agda.Builtin.Size public

{-
Description:
In this Kata you'll practice sized types.

Given a program:

sub : Nat -> Nat
sub zero n = zero
sub (suc m) zero = suc m
sub (suc m) (suc n) = sub m n

div : Nat -> Nat -> Nat
div zero n = zero
div (suc m) n = suc (div (sub m n) n)
Compiler will say, termination check failed. Don't change the program, but change the type signature, and make it work!

Kata name is from Linkin Park's song New Divide.

Based on: https://agda.readthedocs.io/en/v2.5.4.1/language/built-ins.html#sized-types
-}

-- | Sized Nats:
data Nat : {i : Size}-> Set where
     zero : {i : Size}-> Nat{↑ i}
     suc  : {i : Size}-> Nat{i} -> Nat{↑ i}

SubType = {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
DivType = {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}

sub : SubType
sub zero n = zero
sub (suc m) zero = suc m
sub (suc m) (suc n) = sub m n

div : DivType
div zero n = zero
div (suc m) n = suc (div (sub m n) n)
