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

-- m ⟶ v states that computation of m terminates in v. We prepare this 
-- for structural induction on the derivation. 
data _⟶_ : {A : Set} (m : DELAY A ∞) (v : A) -> Set₁ where 
  now⟶   : ∀ {A : Set} (v : A) -> Now v ⟶ v
  later⟶ : ∀ {A : Set} {x : Thunk (DELAY A) ∞} -> ∀ (v : A) 
             -> (ev : force x ⟶ v)
             -> Later x ⟶ v 
  bind⟶ : 
    ∀ {A B : Set} {m : DELAY A ∞} {f : A -> DELAY B ∞} (u : A) (v : B)
    -> m ⟶ u 
    -> f u ⟶ v 
    -> Bind m f ⟶ v 

-- We will check that m ⟶ v conincides with the termination of thawed
-- computation (d : runD m ⇓) that results in v (that is, extract d ≡
-- v).

module _ where
  open import Data.Nat 
  open import Data.Nat.Properties
  private
    -- It is unclear that we can prove the statement ⇓-⟶ by the
    -- indunction on m⇓, as it is not immediately clear that m⇓ does
    -- not involve infinite number of binds. So, we based ourselves on
    -- the number of 'later' and proves that the descruction of "bind"
    -- cannot increase the number ('lemma', below).

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
    ... | fu⟶v rewrite eq = bind⟶ {m = m} {f} (extract m⇓) (extract fu⇓) m⟶u fu⟶v


  ⇓-⟶ : ∀ {A : Set} (m : DELAY A ∞)  -> (m⇓ : runD m ⇓) -> m ⟶ extract m⇓ 
  ⇓-⟶ m m⇓ = aux (len m⇓) m m⇓ (≤-refl) 

-- In contrast, this direction is straightforward. 
⟶-⇓ : ∀ {A : Set} (m : DELAY A ∞) (v : A)
        -> m ⟶ v -> Σ[ m⇓ ∈ runD m ⇓ ] (extract m⇓ ≡ v) 
⟶-⇓ .(Now v) v (now⟶ .v) = now v , refl
⟶-⇓ .(Later _) v (later⟶ .v m⟶v) with ⟶-⇓ _ v m⟶v
... | m⇓ , refl = later m⇓ , refl
⟶-⇓ .(Bind m f) v (bind⟶ {m = m} {f} u .v m⟶u fu⟶v) 
  with ⟶-⇓ _ u m⟶u | ⟶-⇓ _ v fu⟶v
... | m⇓ , refl | fu⇓ , refl = bind-⇓ m⇓ fu⇓ , lemma m⇓ fu⇓
  where
    lemma : 
      ∀ {ℓ} {A B : Set ℓ} {m : Delay A ∞} {f : A → Delay B ∞} 
      -> (m⇓ : m ⇓) -> (fu⇓ : f (extract m⇓) ⇓)
      -> extract (bind-⇓ m⇓ {f = f} fu⇓) ≡ extract fu⇓ 
    lemma (now a) fu⇓ = refl
    lemma {f = f} (later m⇓) fu⇓ rewrite lemma {f = f} m⇓ fu⇓ = refl

-- Never does not terminate. 
¬Never⟶ : ∀ {A : Set} {v : A} -> ¬ (Never ⟶ v)
¬Never⟶ (later⟶ _ x) = ¬Never⟶ x

-- A useful variant of now⟶ 
now⟶≡ : ∀ {A : Set} {v v' : A} -> v' ≡ v -> Now v' ⟶ v 
now⟶≡ refl = now⟶ _

-- Several properties on value environments (for forward and backward
-- evaluations) and manipulations on them.

RValEnv-∅-canon : ∀ {Θ} (ρ : RValEnv Θ ∅) -> ρ ≡ emptyRValEnv
RValEnv-∅-canon {[]} [] = refl
RValEnv-∅-canon {x ∷ Θ} (skip ρ) = cong skip (RValEnv-∅-canon {Θ} ρ)

lkup-unlkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> (ok : varOk● Θ x Ξ) (ρ :  RValEnv Θ Ξ) -> unlkup ok (lkup ok ρ) ≡ ρ 
lkup-unlkup (there ok) (skip ρ) = cong skip (lkup-unlkup ok ρ)
lkup-unlkup (here ad) (x ∷ ρ) with all-zero-canon ad ρ 
... | refl = refl

unlkup-lkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> (ok : varOk● Θ x Ξ) (v : Value [] ∅ A) -> lkup ok (unlkup ok v) ≡ v
unlkup-lkup (there ok) v = unlkup-lkup ok v
unlkup-lkup (here ad) v = refl

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

merge-split : 
  ∀ {Θ Ξ₁ Ξ₂} 
  -> (ano : all-no-omega (Ξ₁ +ₘ Ξ₂))
  -> (ρ₁ : RValEnv Θ Ξ₁)
  -> (ρ₂ : RValEnv Θ Ξ₂)
  -> splitRValEnv (mergeRValEnv ano ρ₁ ρ₂) ≡ (ρ₁ , ρ₂)
merge-split {[]} {[]} {[]} ano [] [] = refl
merge-split {x ∷ Θ} {zero ∷ Ξ₁} {zero ∷ Ξ₂} (px ∷ ano) (skip ρ₁) (skip ρ₂) rewrite merge-split ano ρ₁ ρ₂ = refl
merge-split {x ∷ Θ} {zero ∷ Ξ₁} {one ∷ Ξ₂} (px ∷ ano) (skip ρ₁) (v ∷ ρ₂) rewrite merge-split ano ρ₁ ρ₂ = refl
merge-split {x ∷ Θ} {one ∷ Ξ₁} {zero ∷ Ξ₂} (_ ∷ ano) (v ∷ ρ₁) (skip ρ₂) rewrite merge-split ano ρ₁ ρ₂  = refl
merge-split {x ∷ Θ} {one ∷ Ξ₁} {one ∷ Ξ₂} (() ∷ ano) ρ₁ ρ₂
  

-- Round-trip properties (corresponds to Lemma 3.3 in the paper)

forward-backward : 
  ∀ {Θ Ξ A}
  -> (ano : all-no-omega Ξ)
  -> (E : Residual Θ Ξ (A ●)) 
  -> let h = evalR ∞ ano E
     in ∀ ρ v -> Forward h ρ ⟶ v -> Backward h v ⟶ ρ

forward-backward ano unit● ρ v fwd with RValEnv-∅-canon ρ 
... | refl = now⟶ emptyRValEnv
forward-backward ano (letunit● E E₁) ρ v fwd with all-no-omega-dist _ _ ano
forward-backward ano (letunit● E E₁) ρ v (bind⟶ (unit refl) .v fwd fwd₁) | ano₁ , ano₂ = 
    let bwd  = forward-backward ano₁ E  _ _ fwd  
        bwd₁ = forward-backward ano₂ E₁ _ _ fwd₁ 
    in bind⟶ _ _ bwd₁ (bind⟶ _ _ bwd (now⟶≡ (split-merge ano ρ)))

forward-backward ano (pair● E₁ E₂) ρ (pair {Ξ₁ = []} {[]} spΞ v₁ v₂) fwd with all-no-omega-dist _ _ ano 
forward-backward ano (pair● E₁ E₂) ρ (pair {_} {[]} {[]} spΞ v₁ v₂) (bind⟶ _ _ fwd₁ (bind⟶ _ _ fwd₂ (now⟶ _))) | ano₁ , ano₂ = 
    let bwd₁ = forward-backward ano₁ E₁ _ _ fwd₁ 
        bwd₂ = forward-backward ano₂ E₂ _ _ fwd₂ 
    in bind⟶ _ _ bwd₁ (bind⟶ _ _ bwd₂ (now⟶≡ (split-merge ano ρ)))
forward-backward ano (letpair● E E₁) ρ v fwd 
  with all-no-omega-dist _ _ ano
forward-backward ano (letpair● E E₁) ρ v (bind⟶ (pair {Ξ₁ = []} {[]} refl v₁ v₂) .v fwd fwd₁) | ano₁ , ano₂ = 
   let bwd  = forward-backward ano₁ E _ _ fwd
       bwd₁ = forward-backward (one ∷ one ∷ ano₂) E₁ _ _ fwd₁ 
   in bind⟶ _ _ bwd₁ (bind⟶ _ _ bwd (now⟶≡ (split-merge ano ρ)))

forward-backward ano (inl● E) ρ _ (bind⟶ u _ fwd (now⟶ _)) = forward-backward ano E _ _ fwd
forward-backward ano (inr● E) ρ _ (bind⟶ u _ fwd (now⟶ _)) = forward-backward ano E _ _ fwd

forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v fwd 
  with all-no-omega-dist _ _ ano 
forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ (inl u) .v fwd (bind⟶ (red r₁) .v ev₁ (later⟶ .v (bind⟶ _ .v fwd₁ (bind⟶ (inl (unit refl)) .v ap (now⟶ _)))))) | ano₀ , ano- = 
  bind⟶ _ _ ap (
  bind⟶ _ _ ev₁ (later⟶ _ (
  bind⟶ _ _ (forward-backward (one ∷ ano-) r₁ _ _ fwd₁) (bind⟶ _ _ (forward-backward ano₀ E _ _ fwd) (now⟶≡ (split-merge ano ρ))))))
forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ (inl u) .v fwd (bind⟶ (red r₁) .v ev₁ (later⟶ .v (bind⟶ u₁ .v fwd₁ (bind⟶ (inr (unit refl)) .v ap nev))))) | ano₀ , ano- = ⊥-elim (¬Never⟶ nev)

forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ (inr u) .v fwd (bind⟶ (red r₁) .v ev₁ (later⟶ .v (bind⟶ u₁ .v fwd₁ (bind⟶ (inl (unit refl)) .v ap nev))))) | ano₀ , ano- = ⊥-elim (¬Never⟶ nev)
forward-backward ano (case● E refl θ₁ t₁ θ₂ t₂ v₁) ρ v (bind⟶ (inr u) .v fwd (bind⟶ (red r₁) .v ev₁ (later⟶ .v (bind⟶ _ .v fwd₁ (bind⟶ (inr (unit refl)) .v ap (now⟶ _)))))) | ano₀ , ano- = 
  bind⟶ _ _ ap (
  bind⟶ _ _ ev₁ (later⟶ _ (
  bind⟶ _ _ (forward-backward (one ∷ ano-) r₁ _ _ fwd₁) (bind⟶ _ _ (forward-backward ano₀ E _ _ fwd) (now⟶≡ (split-merge ano ρ))))))


forward-backward ano (var● x ok) ρ .(lkup ok ρ) (now⟶ _) rewrite lkup-unlkup ok ρ = now⟶ ρ
forward-backward ano (pin E (clo .omega refl θ t)) ρ (pair {Ξ₁ = []} {[]} refl v₁ v₂) fwd 
  with all-no-omega-dist _ _ ano
forward-backward ano (pin E (clo .omega refl θ t)) ρ (pair {_} {[]} {[]} refl v₁ v₂) 
                (bind⟶ _ _ fwd (later⟶ _ (bind⟶ (red r) _ ev (bind⟶ _ _ fwd₂ (now⟶ _))))) | ano₁ , ano₂ =
  later⟶ ρ (bind⟶ _ _ ev 
              (bind⟶ _ ρ (forward-backward ano₂ r _ _ fwd₂) 
              (bind⟶ _ _ (forward-backward ano₁ E _ _ fwd) (now⟶≡ (split-merge ano ρ)))))


backward-forward : 
  ∀ {Θ Ξ A}
  -> (ano : all-no-omega Ξ)
  -> (E : Residual Θ Ξ (A ●)) 
  -> let h = evalR ∞ ano E
     in ∀ ρ v -> Backward h v ⟶ ρ -> Forward h ρ ⟶ v 

backward-forward ano unit● ρ (unit refl) bwd = now⟶ (unit refl)
backward-forward ano (letunit● E E₁) ρ v (bind⟶ ρ₂ _ bwd₂ (bind⟶ ρ₁ _ bwd₁ (now⟶ _))) with all-no-omega-dist _ _ ano 
... | ano₁ , ano₂ rewrite merge-split ano ρ₁ ρ₂  = 
  bind⟶ _ _ (backward-forward ano₁ E _ _ bwd₁) (backward-forward ano₂ E₁ _ _ bwd₂)

backward-forward ano (pair● E₁ E₂) ρ (pair {Ξ₁ = []} {[]} refl v₁ v₂) (bind⟶ ρ₁ _ bwd₁ (bind⟶ ρ₂ _ bwd₂ (now⟶ _)))
  with all-no-omega-dist _ _ ano 
... | ano₁ , ano₂ rewrite merge-split ano ρ₁ ρ₂ = 
  bind⟶ _ _ (backward-forward ano₁ E₁ _ _ bwd₁) (bind⟶ _ _ (backward-forward ano₂ E₂ _ _ bwd₂) (now⟶ (pair refl v₁ v₂)))

backward-forward ano (letpair● E E₁) ρ v (bind⟶ (v₁ ∷ v₂ ∷ ρ₂) _ bwd₂ (bind⟶ ρ₁ _ bwd₁ (now⟶ _)))
  with all-no-omega-dist _ _ ano
... | ano₁ , ano₂ rewrite merge-split ano ρ₁ ρ₂ = 
  bind⟶ _ _ (backward-forward ano₁ E _ _ bwd₁) (backward-forward (one ∷ one ∷ ano₂) E₁ _ _ bwd₂)

backward-forward ano (inl● E) ρ (inl v) bwd = bind⟶ _ _ (backward-forward ano E ρ v bwd) (now⟶ (inl v))
backward-forward ano (inl● E) ρ (inr v) bwd = ⊥-elim (¬Never⟶ bwd)

backward-forward ano (inr● E) ρ (inl v) bwd = ⊥-elim (¬Never⟶ bwd)
backward-forward ano (inr● E) ρ (inr v) bwd = bind⟶ _ _ (backward-forward ano E ρ v bwd) (now⟶ (inr v))

backward-forward 
  ano (case● E refl θ₁ t₁ θ₂ t₂ ϕ) ρ v 
  (bind⟶ u _ ap bwd)
  with all-no-omega-dist _ _ ano 
backward-forward 
  ano (case● E refl θ₁ t₁ θ₂ t₂ ϕ) ρ v 
  (bind⟶ (inl u) .ρ ap (bind⟶ (red r) _ ev (later⟶ _ (bind⟶ (v₁ ∷ ρ-) _ bwd- (bind⟶ ρ₀ _ bwd₀ (now⟶ _)))))) | ano₀ , ano- rewrite merge-split ano ρ₀ ρ- = 
  bind⟶ _ _ (backward-forward ano₀ E _ _ bwd₀) 
  (bind⟶ _ _ ev (later⟶ _ 
  (bind⟶ _ _ (backward-forward (one ∷ ano-) r _ _ bwd-) 
  (bind⟶ _ _ ap (now⟶ v)))))
backward-forward 
  ano (case● E refl θ₁ t₁ θ₂ t₂ ϕ) ρ v 
  (bind⟶ (inr u) .ρ ap (bind⟶ (red r) _ ev (later⟶ _ (bind⟶ (v₁ ∷ ρ-) _ bwd- (bind⟶ ρ₀ _ bwd₀ (now⟶ _)))))) | ano₀ , ano- rewrite merge-split ano ρ₀ ρ- = 
  bind⟶ _ _ (backward-forward ano₀ E _ _ bwd₀) 
  (bind⟶ _ _ ev (later⟶ _ 
  (bind⟶ _ _ (backward-forward (one ∷ ano-) r _ _ bwd-) 
  (bind⟶ _ _ ap (now⟶ v)))))

backward-forward ano (var● x ok) .(unlkup ok v) v (now⟶ _) rewrite unlkup-lkup ok v = now⟶ v

backward-forward ano (pin E (clo .omega refl θ t)) ρ (pair {_} {[]} {[]} refl v₁ v₂) 
  (later⟶ _ (bind⟶ (red r) _ ev (bind⟶ ρ₂ _ bwd₂ (bind⟶ ρ₁ _ bwd₁ (now⟶ _)))))
  with all-no-omega-dist _ _ ano 
... | ano₁ , ano₂ rewrite merge-split ano ρ₁ ρ₂ = 
  bind⟶ _ _ (backward-forward ano₁ E _ _ bwd₁) 
  (later⟶ _ (bind⟶ _ _ ev (bind⟶ _ _ (backward-forward ano₂ r _ _ bwd₂) (now⟶ (pair refl v₁ v₂)))))
