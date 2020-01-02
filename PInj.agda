{-# OPTIONS --without-K #-}

module PInj where

open import Codata.Delay renaming (length to dlength ; map to dmap )
open import Codata.Thunk

open import Relation.Binary.PropositionalEquality

open import Size
open import Level
open import Data.Product

record _⇔_ {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set ℓ where
  constructor pre-pinj 
  field 
    forward  : A -> Delay B ∞
    backward : B -> Delay A ∞ 

record _⊢_⇔_ (i : Size) {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set ℓ where
  constructor pre-pinj-i 
  field 
    forward  : A -> Delay B i
    backward : B -> Delay A i 

open _⇔_ 
open _⊢_⇔_ 

∞⊢⇔→⇔ : ∀ {ℓ} {A B : Set ℓ} -> ∞ ⊢ A ⇔ B -> A ⇔ B 
forward  (∞⊢⇔→⇔ h) = forward h
backward (∞⊢⇔→⇔ h) = backward h 

data _results-in_ {ℓ : Level} {A : Set ℓ} : Delay A ∞ -> A -> Set ℓ where
  now   : ∀ {a}   -> now a results-in a
  later : ∀ {a x} -> force x results-in a -> later x results-in a


bind-split : ∀ {ℓ} {A B : Set ℓ} (x : Delay A ∞) (f : A -> Delay B ∞) {b : B} 
             -> bind x f results-in b -> ∃ λ a -> x results-in a × f a results-in b 
bind-split (now x)   f r = x , now , r
bind-split (later x) f (later r) with  bind-split (force x) f r 
... | a , r₁ , r₂  = a , later r₁ , r₂

bind-step : 
  ∀ {ℓ} {A B : Set ℓ} (x : Delay A ∞) (f : A -> Delay B ∞) {a : A} {b : B} -> 
  x results-in a -> f a results-in b -> bind x f results-in b 
bind-step .(now _) f now fa-b = fa-b
bind-step (later x) f (later x-a) fa-b = 
  later (bind-step (force x) f x-a fa-b)
 
 

record PartialInjective {ℓ : Level} (A : Set ℓ) (B : Set ℓ) (f : A ⇔ B) : Set ℓ where
  field 
    forward-backward : 
      ∀ a b -> forward  f a results-in b -> backward f b results-in a 
    backward-forward : 
      ∀ b a -> backward f b results-in a -> forward f a results-in b 
    
open PartialInjective

idₚ : ∀ {ℓ} {A : Set ℓ} -> A ⇔ A 
idₚ = pre-pinj now now 

_∘_ : ∀ {ℓ} {A B C : Set ℓ} -> B ⇔ C -> A ⇔ B -> A ⇔ C 
forward  (g ∘ f) a = bind (forward f a) (forward g) 
backward (g ∘ f) c = bind (backward g c) (backward f)

idₚ-PartialInjective : ∀ {ℓ} {A : Set ℓ} -> PartialInjective A A idₚ 
forward-backward idₚ-PartialInjective a .a now = now
backward-forward idₚ-PartialInjective b .b now = now

pi-trans : ∀ {ℓ} {A B C : Set ℓ} -> ∀ (f : A ⇔ B) (g : B ⇔ C) -> 
           PartialInjective A B f -> PartialInjective B C g -> PartialInjective A C (g ∘ f)
forward-backward (pi-trans f g pf pg) a c r with bind-split (forward f a) (forward g) r  
... | b , fa-b , gb-c with forward-backward pg b c gb-c | forward-backward pf a b fa-b 
... | g'c-b | f'b-a  = bind-step (backward g c) (backward f) g'c-b f'b-a
backward-forward (pi-trans f g pf pg) c a r with bind-split (backward g c) (backward f) r
... | b , g'c-b , f'b-a with backward-forward pg c b g'c-b | backward-forward pf b a f'b-a 
... | gb-c | fa-b = bind-step (forward f a) (forward g) fa-b gb-c 

-- _∘ₚ_ : ∀ {ℓ} {A B C : Set ℓ} {i} -> 
--        PInj B C i -> PInj A B i -> PInj A C i 
-- _∘ₚ_ {i = i} g f  = pinj (λ x -> bind (forward f x) (forward g)) (λ x -> bind (backward g x) (backward f)) lemma1 {!!} 
--   where
--     lemma1 : ∀ a b -> 
--              Result i (bind (forward f a) (forward g)) b →
--              Result i (bind (backward g b) (backward f)) a
--     lemma1 a b r with forward f a | inspect (forward f) a 
--     lemma1 a b r | now x | [ eq ] with forward g x | inspect (forward g) x
--     lemma1 a b r | now x | [ eq ] | now   y | [ eq' ] = {!!}
--     lemma1 a b r | now x | [ eq ] | later y | [ eq' ] = {!!}
--     lemma1 a b r | later x | [ eq ] = {!!} 



  

