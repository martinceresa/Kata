{-# OPTIONS --safe #-}
module StackMach where

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open ≤-Reasoning
open import Data.List.Properties
-- open import Preloaded

{- Preloaded: -}

-- {-# OPTIONS --safe #-}
-- module Preloaded where

open import Data.Nat public
open import Data.List public

data Expr : Set where
  const : ℕ → Expr
  plus : Expr → Expr → Expr

eval-expr : Expr → ℕ
eval-expr (const n) = n
eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2

eval-expr-tail' : Expr → ℕ → ℕ
eval-expr-tail' (const n) acc = n + acc
eval-expr-tail' (plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

eval-expr-tail : Expr → ℕ
eval-expr-tail e = eval-expr-tail' e 0

eval-expr-cont' : {A : Set} → Expr → (ℕ → A) → A
eval-expr-cont' (const n) k = k n
eval-expr-cont' (plus e1 e2) k = eval-expr-cont' e2 λ n2 →
                                 eval-expr-cont' e1 λ n1 → k (n1 + n2)

eval-expr-cont : Expr → ℕ
eval-expr-cont e = eval-expr-cont' e (λ n → n)

data Instr : Set where
  push : ℕ → Instr
  add : Instr

Prog = List Instr

Stack = List ℕ

run : Prog → Stack → Stack
run [] s = s
run (push n ∷ p) s = run p (n ∷ s)
run (add ∷ p) (a1 ∷ a2 ∷ s) = run p (a1 + a2 ∷ s)
run (add ∷ p) s = run p s

compile : Expr → Prog
compile (const n) = push n ∷ []
compile (plus e1 e2) = compile e1 ++ compile e2 ++ add ∷ []

{-
Url: https://www.codewars.com/kata/5cc10885658d6f001281038a
Description:
This kata is an excerpt from Induction Exercises by James Wilcox.

The trivial language
Here is the definition of a language (more precisely, its syntax tree) that supports addition of natural numbers:

data Expr : Set where
  const : ℕ → Expr
  plus : Expr → Expr → Expr
First, let's define ways to evaluate it. We start with a naive implementation:

eval-expr : Expr → ℕ
eval-expr (const n) = n
eval-expr (plus e1 e2) = eval-expr e1 + eval-expr e2
Then a partially tail-recursive one:

eval-expr-tail' : Expr → ℕ → ℕ
eval-expr-tail' (const n) acc = n + acc
eval-expr-tail' (plus e1 e2) acc = eval-expr-tail' e2 (eval-expr-tail' e1 acc)

eval-expr-tail : Expr → ℕ
eval-expr-tail e = eval-expr-tail' e 0
Then one using continuations:

eval-expr-cont' : {A : Set} → Expr → (ℕ → A) → A
eval-expr-cont' (const n) k = k n
eval-expr-cont' (plus e1 e2) k = eval-expr-cont' e2 λ n2 →
                                 eval-expr-cont' e1 λ n1 → k (n1 + n2)

eval-expr-cont : Expr → ℕ
eval-expr-cont e = eval-expr-cont' e (λ n → n)
Task 1. Prove that the various implementations of eval_expr are all equivalent.

Compiling to a simple stack machine
Now we want to compile the above language. Into what? A simple stack machine.

The machine has two instructions: Push n (push a natural number) and Add (pop two numbers from the stack and push their sum).

We also define run that, given a program and an initial stack, runs the program and returns the final stack.

data Instr : Set where
  push : ℕ → Instr
  add : Instr

Prog = List Instr

Stack = List ℕ

run : Prog → Stack → Stack
run [] s = s
run (push n ∷ p) s = run p (n ∷ s)
run (add ∷ p) (a1 ∷ a2 ∷ s) = run p (a1 + a2 ∷ s)
run (add ∷ p) s = run p s
Then we define a function to compile "the trivial language" into a program for "the simple stack machine".

compile : Expr → Prog
compile (const n) = push n ∷ []
compile (plus e1 e2) = compile e1 ++ compile e2 ++ add ∷ []
Task 2. Prove that, if you compile the language and run it on an empty stack, you get the expected result.
-}

-- Task 1 - 1. Prove that eval-expr-tail is equivalent to eval-expr.

-- Goal: eval-expr-tail' e₁ (eval-expr-tail' e 0) ≡
-- eval-expr e + eval-expr e₁
lemmaEvalExpr' : ∀ e n -> eval-expr-tail' e n ≡ eval-expr e + n
lemmaEvalExpr' (const x) n = refl
lemmaEvalExpr' (plus e e₁) n = begin-equality
                           eval-expr-tail' (plus e e₁) n ≡⟨ lemmaEvalExpr' e₁ (eval-expr-tail' e n) ⟩
                           eval-expr e₁ + eval-expr-tail' e n  ≡⟨ cong (eval-expr e₁ +_) (lemmaEvalExpr' e n) ⟩
                           eval-expr e₁ + (eval-expr e + n) ≡⟨ sym (+-assoc (eval-expr e₁) (eval-expr e) n) ⟩
                           (eval-expr e₁ + eval-expr e) + n ≡⟨ cong (λ x → x + n) (+-comm (eval-expr e₁) (eval-expr e)) ⟩
                           eval-expr (plus e e₁) + n ∎

eval-expr-tail-correct : ∀ e → eval-expr-tail e ≡ eval-expr e
eval-expr-tail-correct e = trans (lemmaEvalExpr'  e 0) (+-identityʳ (eval-expr e))

-- Task 1 - 2. Prove that eval-expr-cont is equivalent to eval-expr.

lemmaEvalCont : (e : Expr) (f : ℕ -> ℕ ) -> eval-expr-cont' e f ≡ ( f (eval-expr e) )
lemmaEvalCont (const x) f = refl
lemmaEvalCont (plus e e₁) f = trans (lemmaEvalCont  e₁ λ n2 → eval-expr-cont' e (λ n1 → f (n1 + n2)))
                            (lemmaEvalCont e λ n1 → f (n1 + eval-expr e₁))

eval-expr-cont-correct : ∀ e → eval-expr-cont e ≡ eval-expr e
eval-expr-cont-correct e = lemmaEvalCont e λ n → n

extraLemma : {A : Set} (xs ys zs ps : List A) -> (xs ++ ys ++ zs) ++ ps ≡ xs ++ ( ys ++ zs ++ ps)
extraLemma xs ys za ps = trans ( ++-assoc xs ( ys ++ za) ps)
                       (cong (xs ++_) (++-assoc ys za ps))
-- Task 2. Prove that you get the expected result when you compile and run the program.
lemmaCompile : ∀ e xs ys -> run (compile e ++ xs) ys ≡ run xs (eval-expr e ∷ ys)
lemmaCompile (const x) xs ys = refl
lemmaCompile (plus e e₁) xs ys = trans (cong (λ x → run x ys)
                               (extraLemma (compile e) (compile e₁) ( add ∷ [])  xs))
                               (trans (lemmaCompile  e ( compile e₁ ++ (add ∷ []) ++ xs)  ys)
                               (trans (lemmaCompile e₁ ( add ∷ [] ++ xs) (eval-expr e ∷ ys))
                               (cong (λ x → run xs (x ∷ ys)) (+-comm (eval-expr e₁) (eval-expr e)))))
compile-correct : ∀ e → run (compile e) [] ≡ eval-expr e ∷ []
compile-correct e = trans (cong (λ x → run x []) (sym (++-identityʳ (compile e))))
                    (lemmaCompile e [] [])
