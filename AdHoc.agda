{-# OPTIONS --safe #-}

module AdHoc where

open import Data.Char
open import Data.String hiding (length)
open import Data.List
open import Data.Integer as I
open import Data.Nat as N
open import Agda.Builtin.Nat using (_==_)
open import Data.Bool as B public

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Eq  {a} (A : Set a) : Set a where
  field
    _===_ : A -> A -> Bool

open Eq {{...}} public

instance
  eqNat : Eq ℕ
  _===_ {{eqNat}} =  Agda.Builtin.Nat._==_

  eqString : Eq String
  _===_ {{eqString}} =  Data.String._==_

  eqZ : Eq ℤ
  _===_ {{eqZ}} = λ{ (+_ n) (+_ n₁) → n === n₁
                   ; (+_ n) (-[1+_] n₁) → false
                   ; (-[1+_] n) (+_ n₁) → false
                   ; (-[1+_] n) (-[1+_] n₁) → n === n₁ }

  eqChar : Eq Char
  _===_ {{eqChar}} = Data.Char._==_

  eqBool : Eq Bool
  _===_ {{eqBool}} = λ x x₁ → not (x xor x₁)

  eqList : ∀ {a} {A : Set a} -> {{ eqA : Eq A}} -> Eq (List A)
  _===_ {{eqList}} [] [] = true
  _===_ {{eqList}} (x ∷ xs) (y ∷ ys) = xs === ys
  _===_ {{eqList}} _ _ = false


_=/=_ : {a : Level} {A : Set a} {{eqA : Eq A}} -> A → A → Bool
_=/=_ x y = not (x === y)
