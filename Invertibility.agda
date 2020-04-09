{-# OPTIONS --without-K #-}

module Invertibility where

open import Size 
open import Codata.Delay renaming (length to dlength ; map to dmap )
open import Codata.Thunk using (Thunk ; force)
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Unary.All using (All ; [] ; _∷_)

open import Data.Product 

open import Syntax 
open import Value
open import Definitional 

open import Data.List using (List ; [] ; _∷_ ; length)
open import Data.Vec  using ([] ; _∷_)
 
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using () renaming (case_of_ to CASE_OF_)

open import Relation.Nullary
open import Data.Empty 

open import PInj
open _⊢F_⇔_

data _⟶_ : {A : Set} (m : DELAY A ∞) (v : A) -> Set₁ where 
  now⟶   : ∀ {A : Set} (v : A) -> Now v ⟶ v
  later⟶ : ∀ {A : Set} {x : Thunk (DELAY A) ∞} -> ∀ (v : A) 
             -> (ev : force x ⟶ v)
             -> Later x ⟶ v 
  bind⟶ : 
    ∀ {A B : Set} (m : DELAY A ∞) (f : A -> DELAY B ∞) (u : A) (v : B)
    -> m ⟶ u 
    -> f u ⟶ v 
    -> Bind m f ⟶ v 

module _ where
  open import Data.Nat 
  open import Data.Nat.Properties
  private
    -- steps 
    len : ∀ {A : Set} {m : Delay A ∞} -> m ⇓ -> ℕ 
    len (now _)   = ℕ.zero
    len (later x) = ℕ.suc (len x)

    -- Destruction cannot increase 'len'
    lemma : 
      ∀ {A B : Set} -> (m : Delay A ∞) (f : A -> Delay B ∞) 
      -> (mf⇓ : bind m f ⇓) -> Σ (m ⇓) λ m⇓ → Σ (f (extract m⇓) ⇓) λ fu⇓ -> (extract mf⇓ ≡ extract fu⇓ × len m⇓ ≤ len mf⇓ × len fu⇓ ≤ len mf⇓)
    lemma (now x) f bd = (now x) , bd , refl , z≤n , ≤-refl 
    lemma (later x) f (later bd) with lemma (force x) f bd 
    ... | m⇓ , f⇓ , eq , rel₁ , rel₂ = later m⇓ , f⇓ , eq , s≤s rel₁ , ≤-step rel₂ 
    
    aux : ∀ {A : Set} n -> (m : DELAY A ∞) -> (m⇓ : runD m ⇓) -> len m⇓ ≤ n -> m ⟶ extract m⇓ 
    aux n (Now x) (now .x) ctr = now⟶ x
    aux zero    (Later x) (later m⇓) ()
    aux (suc n) (Later x) (later m⇓) (s≤s ctr) = later⟶ _ (aux n (force x) m⇓ ctr)
    aux n (Bind m f) mf⇓ ctr with lemma (runD m) _ mf⇓ 
    ... | m⇓ , fu⇓ , eq , rel₁ , rel₂ with aux n m m⇓ (≤-trans rel₁ ctr) 
    ... | m⟶u with aux n (f (extract m⇓)) fu⇓ (≤-trans rel₂ ctr) 
    ... | fu⟶v rewrite eq = bind⟶ m f (extract m⇓) (extract fu⇓) m⟶u fu⟶v

  ⇓-⟶ : ∀ {A : Set} (m : DELAY A ∞)  -> (m⇓ : runD m ⇓) -> m ⟶ extract m⇓ 
  ⇓-⟶ m m⇓ = aux (len m⇓) m m⇓ (≤-refl) 

⟶-⇓ : ∀ {A : Set} (m : DELAY A ∞) (v : A)
        -> m ⟶ v -> Σ[ m⇓ ∈ runD m ⇓ ] (extract m⇓ ≡ v) 
⟶-⇓ .(Now v) v (now⟶ .v) = now v , refl
⟶-⇓ .(Later _) v (later⟶ .v m⟶v) with ⟶-⇓ _ v m⟶v
... | m⇓ , refl = later m⇓ , refl
⟶-⇓ .(Bind m f) v (bind⟶ m f u .v m⟶u fu⟶v) 
  with ⟶-⇓ _ u m⟶u | ⟶-⇓ _ v fu⟶v
... | m⇓ , refl | fu⇓ , refl = bind-⇓ m⇓ fu⇓ , lemma m⇓ fu⇓
  where
    lemma : 
      ∀ {ℓ} {A B : Set ℓ} {m : Delay A ∞} {f : A → Delay B ∞} 
      -> (m⇓ : m ⇓) -> (fu⇓ : f (extract m⇓) ⇓)
      -> extract (bind-⇓ m⇓ {f = f} fu⇓) ≡ extract fu⇓ 
    lemma (now a) fu⇓ = refl
    lemma {f = f} (later m⇓) fu⇓ rewrite lemma {f = f} m⇓ fu⇓ = refl

¬Never⟶ : ∀ {A : Set} {v : A} -> ¬ (Never ⟶ v)
¬Never⟶ (later⟶ _ x) = ¬Never⟶ x

now⟶≡ : ∀ {A : Set} {v v' : A} -> v' ≡ v -> Now v' ⟶ v 
now⟶≡ refl = now⟶ _

RValEnv-∅-canon : ∀ {Θ} (ρ : RValEnv Θ ∅) -> ρ ≡ emptyRValEnv
RValEnv-∅-canon {[]} [] = refl
RValEnv-∅-canon {x ∷ Θ} (skip ρ) = cong skip (RValEnv-∅-canon {Θ} ρ)

lkup-unlkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> (ok : varOk● Θ x Ξ) (ρ :  RValEnv Θ Ξ) -> unlkup ok (lkup ok ρ) ≡ ρ 
lkup-unlkup (there ok) (skip ρ) = cong skip (lkup-unlkup ok ρ)
lkup-unlkup (here ad) (x ∷ ρ) with all-zero-canon ad ρ 
... | refl = refl

split-merge : 
  ∀ {Θ Ξ₁ Ξ₂} 
  -> (ano : all-no-omega (Ξ₁ +ₘ Ξ₂))
  -> ∀ (ρ : RValEnv Θ (Ξ₁ +ₘ Ξ₂))
  -> mergeRValEnv ano (proj₁ (splitRValEnv ρ)) (proj₂ (splitRValEnv ρ)) ≡ ρ 
split-merge {[]} {[]} {[]} ano [] = refl
split-merge {x ∷ Θ} {Multiplicity₀.zero ∷ Ξ₁} {Multiplicity₀.zero ∷ Ξ₂} (px ∷ ano) (skip ρ) 
  rewrite split-merge {Θ} {Ξ₁} {Ξ₂} ano ρ = refl
split-merge {x ∷ Θ} {Multiplicity₀.zero ∷ Ξ₁} {one ∷ Ξ₂} (px ∷ ano) (v ∷ ρ) 
  rewrite split-merge {Θ} {Ξ₁} {Ξ₂} ano ρ = refl
split-merge {x ∷ Θ} {one ∷ Ξ₁} {Multiplicity₀.zero ∷ Ξ₂} (px ∷ ano) (v ∷ ρ) 
    rewrite split-merge {Θ} {Ξ₁} {Ξ₂} ano ρ = refl



forward-backward : 
  ∀ {Θ Ξ A}
  -> (ano : all-no-omega Ξ)
  -> (E : Residual Θ Ξ (A ●)) 
  -> let h = evalR ∞ ano E
     in ∀ ρ v -> Forward h ρ ⟶ v -> Backward h v ⟶ ρ

forward-backward ano unit● ρ v fwd with RValEnv-∅-canon ρ 
... | refl = now⟶ emptyRValEnv
forward-backward ano (letunit● E E₁) ρ v fwd with all-no-omega-dist _ _ ano
forward-backward ano (letunit● E E₁) ρ v (bind⟶ _ _ (unit refl) .v fwd fwd₁) | ano₁ , ano₂ = 
    let bwd  = forward-backward ano₁ E  _ _ fwd  
        bwd₁ = forward-backward ano₂ E₁ _ _ fwd₁ 
    in bind⟶ _ _ _ _ bwd₁ (bind⟶ _ _ _ _ bwd (now⟶≡ (split-merge ano ρ)))

forward-backward ano (pair● E₁ E₂) ρ (pair {Ξ₁ = []} {[]} spΞ v₁ v₂) fwd with all-no-omega-dist _ _ ano 
forward-backward ano (pair● E₁ E₂) ρ (pair {_} {[]} {[]} spΞ v₁ v₂) (bind⟶ _ _ _ _ fwd₁ (bind⟶ _ _ _ _ fwd₂ (now⟶ _))) | ano₁ , ano₂ = 
    let bwd₁ = forward-backward ano₁ E₁ _ _ fwd₁ 
        bwd₂ = forward-backward ano₂ E₂ _ _ fwd₂ 
    in bind⟶ _ _ _ _ bwd₁ (bind⟶ _ _ _ _ bwd₂ (now⟶≡ (split-merge ano ρ)))
forward-backward ano (letpair● E E₁) ρ v fwd 
  with all-no-omega-dist _ _ ano
forward-backward ano (letpair● E E₁) ρ v (bind⟶ _ _ (pair {Ξ₁ = []} {[]} refl v₁ v₂) .v fwd fwd₁) | ano₁ , ano₂ = 
   let bwd  = forward-backward ano₁ E _ _ fwd
       bwd₁ = forward-backward (one ∷ one ∷ ano₂) E₁ _ _ fwd₁ 
   in bind⟶ _ _ _ _ bwd₁ (bind⟶ _ _ _ _ bwd (now⟶≡ (split-merge ano ρ)))

forward-backward ano (inl● E) ρ _ (bind⟶ _ _ u _ fwd (now⟶ _)) = forward-backward ano E _ _ fwd
forward-backward ano (inr● E) ρ _ (bind⟶ _ _ u _ fwd (now⟶ _)) = forward-backward ano E _ _ fwd

forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v fwd 
  with all-no-omega-dist _ _ ano 
forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ _ _ (inl u) .v fwd (bind⟶ _ _ (red r₁) .v ev₁ (later⟶ .v (bind⟶ _ _ _ .v fwd₁ (bind⟶ _ _ (inl (unit refl)) .v ap (now⟶ _)))))) | ano₀ , ano- = 
  bind⟶ _ _ _ _ ap (
  bind⟶ _ _ _ _ ev₁ (later⟶ _ (
  bind⟶ _ _ _ _ (forward-backward (one ∷ ano-) r₁ _ _ fwd₁) (bind⟶ _ _ _ _ (forward-backward ano₀ E _ _ fwd) (now⟶≡ (split-merge ano ρ))))))
forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ _ _ (inl u) .v fwd (bind⟶ _ _ (red r₁) .v ev₁ (later⟶ .v (bind⟶ _ _ u₁ .v fwd₁ (bind⟶ _ _ (inr (unit refl)) .v ap nev))))) | ano₀ , ano- = ⊥-elim (¬Never⟶ nev)

forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ _ _ (inr u) .v fwd (bind⟶ _ _ (red r₁) .v ev₁ (later⟶ .v (bind⟶ _ _ u₁ .v fwd₁ (bind⟶ _ _ (inl (unit refl)) .v ap nev))))) | ano₀ , ano- = ⊥-elim (¬Never⟶ nev)
forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ _ _ (inr u) .v fwd (bind⟶ _ _ (red r₁) .v ev₁ (later⟶ .v (bind⟶ _ _ _ .v fwd₁ (bind⟶ _ _ (inr (unit refl)) .v ap (now⟶ _)))))) | ano₀ , ano- = 
  bind⟶ _ _ _ _ ap (
  bind⟶ _ _ _ _ ev₁ (later⟶ _ (
  bind⟶ _ _ _ _ (forward-backward (one ∷ ano-) r₁ _ _ fwd₁) (bind⟶ _ _ _ _ (forward-backward ano₀ E _ _ fwd) (now⟶≡ (split-merge ano ρ))))))


forward-backward ano (var● x ok) ρ .(lkup ok ρ) (now⟶ _) rewrite lkup-unlkup ok ρ = now⟶ ρ
forward-backward ano (pin E (clo .omega refl θ t)) ρ (pair {Ξ₁ = []} {[]} refl v₁ v₂) fwd 
  with all-no-omega-dist _ _ ano
forward-backward ano (pin E (clo .omega refl θ t)) ρ (pair {_} {[]} {[]} refl v₁ v₂) 
                (bind⟶ _ _ _ _ fwd (later⟶ _ (bind⟶ _ _ (red r) _ ev (bind⟶ _ _ _ _ fwd₂ (now⟶ _))))) | ano₁ , ano₂ =
  later⟶ ρ (bind⟶ _ _ _ _ ev 
              (bind⟶ _ _ _ ρ (forward-backward ano₂ r _ _ fwd₂) 
              (bind⟶ _ _ _ _ (forward-backward ano₁ E _ _ fwd) (now⟶≡ (split-merge ano ρ)))))


