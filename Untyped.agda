-- TODO
-- Export definition in another module

module Tapl.Untyped where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Term : Set where
   True : Term
   False : Term
   If : Term -> Term -> Term -> Term
   Zero : Term
   Succ : Term -> Term
   Pred : Term -> Term
   IsZero : Term -> Term

-- Integer normal form
data ⊂N : Term -> Set where
   Zero⊂N : ⊂N Zero
   Succ⊂N : {t : Term} -> ⊂N t -> ⊂N (Succ t)

data ⊥ : Set where

data ⊢ : Term -> Term -> Set where
   E-IFTRUE : {t₂ t₃ : Term} ->  ⊢ (If True t₂ t₃) t₂
   E-IFFALSE : {t₂ t₃ : Term} -> ⊢ (If False t₂ t₃) t₃
   E-IF : {t₁ t₂ t₃ t₁′ : Term} -> ⊢ t₁ t₁′ -> ⊢ (If t₁ t₂ t₃) (If t₁′ t₂ t₃)
   E-SUCC : { t₁ t₁′ : Term} -> ⊢ t₁ t₁′ -> ⊢ (Succ t₁) (Succ t₁′)
   E-PREDZERO : ⊢ (Pred Zero) Zero
   E-PREDSUCC : {t₁ t₂ : Term} -> (⊂N t₁) -> ⊢ (Pred (Succ t₁)) t₁
   E-PRED : {t₁ t₁′ : Term} -> ⊢ t₁ t₁′ -> ⊢ (Pred t₁) (Pred t₁′)
   E-ISZEROZERO : ⊢ (IsZero Zero) True
   E-ISZEROSUCC : {t₁ : Term} -> (⊂N t₁) -> ⊢ (IsZero (Succ t₁)) False
   E-ISZERO : {t₁ t₁′ : Term} -> ⊢ t₁ t₁′ -> ⊢ (IsZero t₁) (IsZero t₁′)

-- t₁ is integer in normal form
-- |­ t₁ t₂ is small step evalution with source t₁
-- If you give me proof of above two, I can construct something
-- which is unconstructable
lemma₁ : { t₁ t₂ : Term} -> ⊂N t₁ -> ⊢ t₁ t₂ -> ⊥
lemma₁ Zero⊂N ()
lemma₁ (Succ⊂N a) (E-SUCC b) = lemma₁ a b

-- t₁ is integer in normal form
-- |­ (Succ t₁) t₂ is small step evalution with source (Succ t₁)
-- If you give me proof of above two, I can construct something
-- which is unconstructable
lemma₂ : { t₁ t₂ : Term } -> ⊂N t₁ -> ⊢ (Succ t₁) t₂ -> ⊥
lemma₂ Zero⊂N (E-SUCC ())
lemma₂ (Succ⊂N a) (E-SUCC b) = lemma₂ a b

proof₁ : {t t₁ t₂ : Term} -> (⊢ t t₁) -> (⊢ t t₂) -> t₁ ≡ t₂
proof₁ E-IFTRUE E-IFTRUE = refl
proof₁ E-IFTRUE (E-IF ())
proof₁ E-IFFALSE E-IFFALSE = refl
proof₁ E-IFFALSE (E-IF ())
proof₁ (E-IF ()) E-IFTRUE
proof₁ (E-IF ()) E-IFFALSE
-- Induction hypothesis
proof₁ (E-IF p₁) (E-IF p₂) with proof₁ p₁ p₂
proof₁ (E-IF p₁) (E-IF p₂) | refl = refl
-- Induction hypothesis
proof₁ (E-SUCC p₁) (E-SUCC p₂) with proof₁ p₁ p₂
proof₁ (E-SUCC p₁) (E-SUCC p₂) | refl = refl
proof₁ E-PREDZERO E-PREDZERO = refl
proof₁ E-PREDZERO (E-PRED ())
proof₁ (E-PREDSUCC x) (E-PREDSUCC x₁) = refl
-- This is not possible courtesy lemma₁
proof₁ (E-PREDSUCC x) (E-PRED (E-SUCC p₂)) with lemma₁ x p₂
proof₁ (E-PREDSUCC x) (E-PRED (E-SUCC p₂)) | ()
proof₁ (E-PRED ()) E-PREDZERO
-- This is not possible courtesy lemma₁
proof₁ (E-PRED (E-SUCC p₁)) (E-PREDSUCC x) with lemma₁ x p₁
proof₁ (E-PRED (E-SUCC p₁)) (E-PREDSUCC x) | ()
-- A call to Induction
proof₁ (E-PRED p₁) (E-PRED p₂) with proof₁ p₁ p₂
proof₁ (E-PRED p₁) (E-PRED p₂) | refl = refl
proof₁ E-ISZEROZERO E-ISZEROZERO = refl
proof₁ E-ISZEROZERO (E-ISZERO ())
proof₁ (E-ISZEROSUCC x) (E-ISZEROSUCC x₁) = refl
-- This is not possible courtesy lemma₂
proof₁ (E-ISZEROSUCC x) (E-ISZERO p₂) with lemma₂ x p₂
proof₁ (E-ISZEROSUCC x) (E-ISZERO p₂) | ()
proof₁ (E-ISZERO ()) E-ISZEROZERO
-- lemma₂ to rescue
proof₁ (E-ISZERO p₁) (E-ISZEROSUCC x) with lemma₂ x p₁
proof₁ (E-ISZERO p₁) (E-ISZEROSUCC x) | ()
-- Final Induction
proof₁ (E-ISZERO p₁) (E-ISZERO p₂) with proof₁ p₁ p₂
proof₁ (E-ISZERO p₁) (E-ISZERO p₂) | refl = refl
