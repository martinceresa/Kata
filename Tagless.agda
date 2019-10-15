module Tagless where

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Unit

record Language (r : Set → Set → Set) : Set₁ where
  field
    here   : ∀ {a h} → r (a × h) a
    before : ∀ {a h any} → r h a -> r (any × h) a
    lambda : ∀ {a b h} → r (a × h) b → r h (a → b)
    apply  : ∀ {a b h} → r h (a → b) → (r h a → r h b)

    loop   : ∀ {a h} → r h (a → a) → r h a

    nat    : ∀ {h} → ℕ → r h ℕ
    add    : ∀ {h} → r h ℕ → r h ℕ → r h ℕ
    down   : ∀ {h} → r h ℕ → r h ℕ    -- pred
    up     : ∀ {h} → r h ℕ → r h ℕ    -- succ
    mult   : ∀ {h} → r h ℕ → r h ℕ → r h ℕ
    gte    : ∀ {h} → r h ℕ → r h ℕ → r h Bool -- greater than or equal

    bool   : ∀ {h} → Bool → r h Bool
    and    : ∀ {h} → r h Bool → r h Bool → r h Bool
    or     : ∀ {h} → r h Bool → r h Bool → r h Bool
    neg    : ∀ {h} → r h Bool → r h Bool

    ifte   : ∀ {a h} → r h Bool → r h a → r h a → r h a
    -- if true then return left term, else return right term

open Language {{...}} -- use instance arguments to simulate type classes

Term : Set → Set₁
Term a = ∀ {r h} {{l : Language r}} → r h a

{-# TERMINATING #-} -- maybe you need this to implement loop
fix : ∀ {A : Set} → (A → A) → A
fix f = f (fix f)

interpret : ∀ {a} → Term a → a
interpret t = fix (λ x → {!t x!})
