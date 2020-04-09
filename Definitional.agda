{-# OPTIONS --without-K #-}

{- 

Approx. 15 min is required to typecheck this file (for Agda 2.6.1).

-}

module Definitional where 

open import Syntax 

open import Data.Nat 
open import Data.Fin using (Fin ; suc; zero)

open import Data.List using (length ; [] ; _∷_ )
open import Data.List.Properties using (length-++)
open import Data.Vec  using ([] ; _∷_)
open import Data.Vec.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Level renaming (zero to lzero ; suc to lsuc)
open ≡-Reasoning

open import Function using () renaming (case_of_ to CASE_OF_)

open import Value 

module Interpreter where 
  open import Codata.Delay renaming (length to dlength ; map to dmap )
  open import Codata.Thunk

  open import PInj
  open _⊢_⇔_

  data RValEnv : (Θ : TyEnv) (Ξ : MultEnv (length Θ)) -> Set where
    []   : RValEnv [] [] 
    skip : ∀ {Θ Ξ A} -> RValEnv Θ Ξ -> RValEnv (A ∷ Θ) (zero ∷ Ξ)
    _∷_  : ∀ {Θ Ξ A} -> Value [] ∅ A -> RValEnv Θ Ξ -> RValEnv (A ∷ Θ) (one ∷ Ξ)

  emptyRValEnv : ∀ {Θ} -> RValEnv Θ ∅ 
  emptyRValEnv {[]} = []
  emptyRValEnv {_ ∷ _} = skip emptyRValEnv 

  splitRValEnv : ∀ {Θ Ξ₁ Ξ₂} -> RValEnv Θ (Ξ₁ +ₘ Ξ₂) -> RValEnv Θ Ξ₁ × RValEnv Θ Ξ₂ 
  splitRValEnv {[]} {[]} {[]} [] = [] , [] 
  splitRValEnv {_ ∷ Θ} {zero ∷ Ξ₁} {zero ∷ Ξ₂} (skip ρ) 
    with splitRValEnv ρ 
  ... | ρ₁ , ρ₂ = skip ρ₁ , skip ρ₂
  splitRValEnv {_ ∷ Θ} {zero ∷ Ξ₁} {one ∷ Ξ₂} (x ∷ ρ) 
    with splitRValEnv ρ 
  ... | ρ₁ , ρ₂ =  skip ρ₁ , x ∷ ρ₂ 
  splitRValEnv {_ ∷ Θ} {one ∷ Ξ₁} {zero ∷ Ξ₂} (x ∷ ρ) 
    with splitRValEnv ρ 
  ... | ρ₁ , ρ₂ = x ∷ ρ₁ , skip ρ₂ 

  mergeRValEnv : ∀ {Θ Ξ₁ Ξ₂} -> all-no-omega (Ξ₁ +ₘ Ξ₂) -> RValEnv Θ Ξ₁ -> RValEnv Θ Ξ₂ -> RValEnv Θ (Ξ₁ +ₘ Ξ₂)
  mergeRValEnv {.[]} {.[]} {.[]} _ [] [] = []
  mergeRValEnv {.(_ ∷ _)} {.(zero ∷ _)} {.(zero ∷ _)} (_ ∷ ano) (skip ρ₁) (skip ρ₂) = skip (mergeRValEnv ano ρ₁ ρ₂)
  mergeRValEnv {.(_ ∷ _)} {.(zero ∷ _)} {.(one ∷ _)} (_ ∷ ano) (skip ρ₁) (x ∷ ρ₂) = x ∷ (mergeRValEnv ano ρ₁ ρ₂)
  mergeRValEnv {.(_ ∷ _)} {.(one ∷ _)} {.(zero ∷ _)} (_ ∷ ano) (x ∷ ρ₁) (skip ρ₂) = x ∷ mergeRValEnv ano ρ₁ ρ₂
  mergeRValEnv {.(_ ∷ _)} {.(one ∷ _)} {.(one ∷ _)} (() ∷ ano) (x ∷ ρ₁) (x₁ ∷ ρ₂) 

  from-all-zero : ∀ {Θ Ξ} -> all-zero Ξ -> RValEnv Θ Ξ 
  from-all-zero {[]} {[]} [] = []
  from-all-zero {_ ∷ Θ} {.(zero ∷ _)} (refl ∷ az) = skip (from-all-zero az) 
  
  all-zero-canon : ∀ {Θ Ξ} -> (az : all-zero Ξ) -> (θ : RValEnv Θ Ξ) -> θ ≡ (from-all-zero az)
  all-zero-canon {[]} {[]} [] [] = refl
  all-zero-canon {_ ∷ Θ} {_ ∷ Ξ} (refl ∷ az) (skip θ) = cong skip (all-zero-canon az θ) 


  lkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> varOk● Θ x Ξ -> RValEnv Θ Ξ -> Value [] ∅ A 
  lkup (there ok) (skip ρ) = lkup ok ρ
  lkup (here ad) (x ∷ ρ) = x -- ad asserts ρ consists only of skip and []

  unlkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> varOk● Θ x Ξ -> Value [] ∅ A -> RValEnv Θ Ξ 
  unlkup (there ok) v = skip (unlkup ok v)
  unlkup (here ad) v = v ∷ from-all-zero ad 

  var●₀ : ∀ {A Θ} -> Residual (A ∷ Θ) (one ∷ ∅) (A ●) 
  var●₀ = var● vz (here all-zero-∅) 

  bindR : ∀ {ℓ : Level} {i Θ Ξ A} {r : Set ℓ} -> Delay (Value Θ Ξ (A ●)) i -> (Residual Θ Ξ (A ●) -> Delay r i) -> Delay r i 
  bindR x f = bind x λ { (red r) -> f r } 

  -- For the do trick for the pattern matching 
  -- See https://github.com/agda/agda/issues/2298
  _>>=_ : ∀ {a b : Level} {A : Set a} {B : A -> Set b} -> ∀ (x : A) -> (∀ x -> B x) -> B x 
  x >>= f = f x 

  apply : 
    ∀ {Θ Ξ₁ Ξ₂ A m B} i -> 
    all-no-omega (Ξ₁ +ₘ m ×ₘ Ξ₂) -> 
    Value Θ Ξ₁ (A # m ~> B) -> Value Θ Ξ₂ A -> Delay (Value Θ (Ξ₁ +ₘ m ×ₘ Ξ₂) B) i 

  evalR :
    ∀ {Θ Ξ A} i -> 
    all-no-omega Ξ -> Residual Θ Ξ (A ●) -> i ⊢ (RValEnv Θ Ξ) ⇔ Value [] ∅ A 

  eval : 
    ∀ {Θ Ξₑ Γ Δ Ξ A} i -> 
    all-no-omega (Ξₑ +ₘ Ξ) -> ValEnv Γ Δ Θ Ξₑ -> Term Γ Δ Θ Ξ A -> Delay (Value Θ (Ξₑ +ₘ Ξ) A) i 

  apply {Θ} {Ξ₁} {Ξ₂} i ano (clo {Ξ' = Ξ'} {Ξₜ = Ξₜ} m refl θ t) v with all-no-omega-dist _ _ ano
  ... | ano-'t , ano-m2 = later λ { .force {j} -> 
        let T = eval j (subst all-no-omega lemma ano) (tup _ _ refl (value-to-multM ano-m2 v) θ) t
        in subst (λ x -> Delay (Value Θ x _) j) (sym lemma) T  
      }
    where
      lemma : Ξ' +ₘ Ξₜ +ₘ m ×ₘ Ξ₂ ≡ m ×ₘ Ξ₂ +ₘ Ξ' +ₘ Ξₜ 
      lemma = trans (+ₘ-comm _ _)
                    (sym (+ₘ-assoc (m ×ₘ Ξ₂) Ξ' _))

  
  forward  (evalR i ano unit●) _ = now (unit refl)
  backward (evalR i ano unit●) _ = now emptyRValEnv

  forward  (evalR i ano (letunit● r₁ r₂)) ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    ρ₁ , ρ₂ <- splitRValEnv ρ 
    bind (forward (evalR i ano₁ r₁) ρ₁) λ { (unit eq) -> forward (evalR i ano₂ r₂) ρ₂ } 
  backward (evalR i ano (letunit● r₁ r₂)) v = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    bind (backward (evalR i ano₂ r₂) v) λ ρ₂ -> 
     bind (backward (evalR i ano₁ r₁) (unit refl)) λ ρ₁ -> 
      now (mergeRValEnv ano ρ₁ ρ₂) 
   
  forward  (evalR i ano (pair● r₁ r₂)) ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    ρ₁  , ρ₂  <- splitRValEnv ρ
    bind (forward (evalR i ano₁ r₁) ρ₁) λ v₁ -> 
     bind (forward (evalR i ano₂ r₂) ρ₂) λ v₂ -> 
      now (pair refl v₁ v₂)
      
  backward (evalR i ano (pair● {A = A} {B} r₁ r₂)) (pair {Ξ₁ = []} {[]} spΞ v₁ v₂) = do
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    bind (backward (evalR i ano₁ r₁) v₁) λ ρ₁ -> 
     bind (backward (evalR i ano₂ r₂) v₂) λ ρ₂ -> 
      now (mergeRValEnv ano ρ₁ ρ₂)

  forward (evalR i ano (letpair● r₁ r₂)) ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    ρ₁  , ρ₂  <- splitRValEnv ρ
    bind (forward (evalR i ano₁ r₁) ρ₁) λ { 
      (pair {Ξ₁ = []} {[]} spΞ v₁ v₂ ) -> 
        forward (evalR i (one ∷ one ∷ ano₂) r₂) (v₁ ∷ v₂ ∷ ρ₂)
     }
  
  backward (evalR i ano (letpair● r₁ r₂)) v = do 
    ano₁ , ano₂ <-  all-no-omega-dist _ _ ano 
    bind (backward (evalR i (one ∷ one ∷ ano₂) r₂) v) λ { (v₁ ∷ v₂ ∷ ρ₂) -> 
      bind (backward (evalR i ano₁ r₁) (pair refl v₁ v₂)) λ ρ₁ -> 
       now (mergeRValEnv ano ρ₁ ρ₂)
     }
  
  forward (evalR i ano (inl● r)) ρ = bind (forward (evalR i ano r) ρ) λ x -> now (inl x)
  backward (evalR i ano (inl● r)) v = 
    CASE v OF λ {
      (inl v₁) -> backward (evalR i ano r) v₁ ; 
      (inr v₂) -> never 
    }
  
  forward  (evalR i ano (inr● r)) ρ = bind (forward (evalR i ano r) ρ) λ x -> now (inr x)
  backward (evalR i ano (inr● r)) v = 
    CASE v OF λ { 
      (inl v₁) -> never ; 
      (inr v₂) -> backward (evalR i ano r) v₂
    }
  
  forward  (evalR i ano (case● {Γ₁ = Γ₁} {Γ₂} r refl θ₁ t₁ θ₂ t₂ f)) ρ = do 
    ano₀ , ano- <- all-no-omega-dist _ _ ano
    ρ₀  , ρ-  <- splitRValEnv ρ 
    bind (forward (evalR i ano₀ r) ρ₀) λ {
          (inl v₁) -> 
            bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₁ (compat-ext-here ext-id) θ₁) t₁) λ { (red r₁) -> 
              later λ { .force {j} -> 
                bind (forward (evalR j (one ∷ ano-) r₁) (v₁ ∷ ρ-)) λ v -> 
                 bind (apply j [] f v) λ { 
                   (inl _) -> now v ; 
                   (inr _) -> never 
                  }                 
              }   
            }
           ; 
          (inr v₂) -> 
            bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₂ (compat-ext-here ext-id) θ₂) t₂) λ { (red r₂) -> 
              later λ { .force {j} -> 
                bind (forward (evalR j (one ∷ ano-) r₂) (v₂ ∷ ρ-)) λ v -> 
                  bind (apply j [] f v) λ {
                    (inl _) -> never ; 
                    (inr _) -> now v 
                  }
               }
            }
        }
  
  backward (evalR i ano (case● {Γ₁ = Γ₁} {Γ₂} r refl θ₁ t₁ θ₂ t₂ f)) v = do 
    ano₀ , ano- <- all-no-omega-dist _ _ ano 
    bind (apply i [] f v) λ {
      (inl _) -> 
         bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₁ (compat-ext-here ext-id) θ₁) t₁) λ { (red r₁) -> 
           later λ { .force {j} -> 
               bind (backward (evalR j (one ∷ ano-) r₁) v) λ { (v₁ ∷ ρ-) -> 
                 bind (backward (evalR j ano₀ r) (inl v₁)) λ ρ₀ -> 
                     now (mergeRValEnv ano ρ₀ ρ-)                 
               }
            } 
         }
      ;
      (inr _) -> 
          bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₂ (compat-ext-here ext-id) θ₂) t₂) λ { (red r₂) -> 
            later λ where .force {j} -> 
                             bind (backward (evalR j (one ∷ ano-) r₂) v) λ { (v₂ ∷ ρ-) -> 
                               bind (backward (evalR j ano₀ r) (inr v₂)) λ ρ₀ -> 
                                 now (mergeRValEnv ano ρ₀ ρ-)
                             }
          }     
     }

  

  forward  (evalR i ano (var● x ok)) ρ = now (lkup ok ρ)
  backward (evalR i ano (var● x ok)) v  = now (unlkup ok v)

  forward (evalR i ano (pin r f))  ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano
    ρ₁  , ρ₂  <- splitRValEnv ρ
    bind (forward (evalR i ano₁ r) ρ₁) λ v₁ -> 
      CASE f OF λ { (clo .omega refl θ t) → 
        later λ { .force {j} -> 
           bind (eval j ano₂ (tup ∅ _ (∅-lid _) (mult-omega (weakenΘ-value extendΘ v₁) refl) θ) t) λ { 
            (red r₂) -> 
              -- maybe another delaying would be needed here
              bind (forward (evalR j ano₂ r₂) ρ₂) λ v₂ -> 
              now (pair refl v₁ v₂)
           }
        }
      } 
  
    
  backward (evalR i ano (pin r (clo .omega refl θ t))) (pair {Ξ₁ = []} {[]} refl v₁ v₂) = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    later λ { .force {j} -> 
      bindR (eval j ano₂ (tup ∅ _ (∅-lid _) (mult-omega (weakenΘ-value extendΘ v₁) refl) θ) t) λ r₂ -> 
        bind (backward (evalR j ano₂ r₂) v₂) λ ρ₂ -> 
        bind (backward (evalR j ano₁ r) v₁) λ ρ₁ -> 
        now (mergeRValEnv ano ρ₁ ρ₂) 
     } 

    
  eval {Θ} _ ano θ (var x ok) = now (subst (λ x -> Value Θ x _) (sym (∅-rid _)) (lookupVar θ ok))
  eval _ ano θ (abs m t) = now (clo m refl θ t) 

  eval {Θ} {Γ = Γ} i ano θ (app {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} {m = m} t₁ t₂)
      with separateEnv {Γ} Δ₁ (m ×ₘ Δ₂) θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ with eval i (proj₁ lemma) θ₁ t₁ | proj₂ lemma | weakenΔ-valEnv Γ θ₂ 
    where 
      lemma' : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₁ +ₘ m ×ₘ Ξ₂) ≡ (Ξₑ₁ +ₘ Ξ₁) +ₘ (Ξₑ₂ +ₘ m ×ₘ Ξ₂)
      lemma' = +ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ (m ×ₘ Ξ₂) 

      lemma : all-no-omega (Ξₑ₁ +ₘ Ξ₁) × all-no-omega (Ξₑ₂ +ₘ m ×ₘ Ξ₂)
      lemma = all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ (subst all-no-omega lemma' ano)  
  ... | T₁ | ano-e2m2 | Ξₑ₂' , θ₂' , refl with (subst all-no-omega (sym (×ₘ-dist m Ξₑ₂' _)) ano-e2m2)
  ... | ano-m[e2'2] with eval i (all-no-omega-dist-×ₘ m (Ξₑ₂' +ₘ Ξ₂) ano-m[e2'2]) θ₂' t₂
  ... | T₂ = 
    bind T₁ (λ { (clo {Ξ' = Ξ'} {Ξₜ = Ξₜ} m spΞ θf t) → bind T₂ λ v₂ -> 
      later λ { .force ->
        let lemma : m ×ₘ (Ξₑ₂' +ₘ Ξ₂) +ₘ Ξ' +ₘ Ξₜ ≡ Ξₑ₁ +ₘ m ×ₘ Ξₑ₂' +ₘ (Ξ₁ +ₘ m ×ₘ Ξ₂)
            lemma = 
              begin 
                m ×ₘ (Ξₑ₂' +ₘ Ξ₂) +ₘ Ξ' +ₘ Ξₜ 
              ≡⟨ +ₘ-assoc (m ×ₘ (Ξₑ₂' +ₘ Ξ₂)) Ξ' _ ⟩ 
                m ×ₘ (Ξₑ₂' +ₘ Ξ₂) +ₘ (Ξ' +ₘ Ξₜ)
              ≡⟨ cong (_ +ₘ_) spΞ ⟩ 
                m ×ₘ (Ξₑ₂' +ₘ Ξ₂) +ₘ (Ξₑ₁ +ₘ Ξ₁)         
              ≡⟨ cong (_+ₘ _) (×ₘ-dist m Ξₑ₂' Ξ₂) ⟩ 
                m ×ₘ Ξₑ₂' +ₘ m ×ₘ Ξ₂ +ₘ (Ξₑ₁ +ₘ Ξ₁)
              ≡⟨ +ₘ-transpose (m ×ₘ Ξₑ₂') (m ×ₘ Ξ₂) Ξₑ₁ _ ⟩ 
                m ×ₘ Ξₑ₂' +ₘ Ξₑ₁ +ₘ (m ×ₘ Ξ₂ +ₘ Ξ₁)
              ≡⟨ cong₂ (_+ₘ_) (+ₘ-comm _ _) (+ₘ-comm _ _) ⟩ 
                Ξₑ₁ +ₘ m ×ₘ Ξₑ₂' +ₘ (Ξ₁ +ₘ m ×ₘ Ξ₂) 
              ∎

            lemma-ano : all-no-omega (m ×ₘ (Ξₑ₂' +ₘ Ξ₂) +ₘ Ξ' +ₘ Ξₜ)
            lemma-ano = subst all-no-omega (sym lemma) ano 
              
        in (bind (eval _ lemma-ano (tup (m ×ₘ (Ξₑ₂' +ₘ Ξ₂)) Ξ' refl (value-to-multM ano-m[e2'2] v₂) θf) t) λ v ->  now (subst (λ Ξ -> Value Θ Ξ _) lemma v)  
       )}
    })
      
  eval {Γ = Γ} _ ano θ (unit ad) with discardable-has-no-resources {Γ} θ ad
  ... | refl = now (substV (sym (∅-lid _)) (unit refl))

  eval {Θ} {Ξₑ} {Γ} i ano θ (letunit {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} m t₀ t) 
    with separateEnv {Γ} (m ×ₘ Δ₀) Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with weakenΔ-valEnv Γ θ₁ 
  ... | Ξₑ₁' , θ₁' , refl 
    with subst all-no-omega (+ₘ-transpose (m ×ₘ Ξₑ₁') Ξₑ₂ (m ×ₘ Ξ₀) _) ano 
  ... | ano'
    with all-no-omega-dist (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) _ ano'
  ... | ano-me1'm0 , ano-e2 
    with eval i (all-no-omega-dist-×ₘ m (Ξₑ₁' +ₘ Ξ₀) (subst all-no-omega (sym (×ₘ-dist m Ξₑ₁' Ξ₀)) ano-me1'm0)) θ₁' t₀ 
  ... | T₀ = bind T₀ λ { (unit emp-e1'0) → 
      let lemma : Ξₑ₂ +ₘ Ξ ≡ (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ ((m ×ₘ Ξ₀) +ₘ Ξ)
          lemma = 
            begin 
              Ξₑ₂ +ₘ Ξ
            ≡⟨ sym (∅-lid _) ⟩ 
              ∅ +ₘ (Ξₑ₂ +ₘ Ξ) 
            ≡⟨ cong (_+ₘ (Ξₑ₂ +ₘ Ξ)) (sym (×ₘ∅ m)) ⟩ 
              m ×ₘ ∅ +ₘ (Ξₑ₂ +ₘ Ξ) 
            ≡⟨ cong (λ h -> m ×ₘ h +ₘ (Ξₑ₂ +ₘ Ξ)) (emp-e1'0) ⟩ 
              m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ (Ξₑ₂ +ₘ Ξ)
            ≡⟨ cong (_+ₘ _) (×ₘ-dist m Ξₑ₁' Ξ₀) ⟩ 
              m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ)          
            ≡⟨ +ₘ-transpose (m ×ₘ Ξₑ₁') (m ×ₘ Ξ₀) Ξₑ₂ Ξ ⟩ 
              (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ ((m ×ₘ Ξ₀) +ₘ Ξ)
            ∎
      in dmap (substV lemma) (eval i ano-e2 θ₂ t)
   }

  eval {Θ} {Ξₑ} {Γ} i ano θ (pair {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} t₁ t₂) 
    with separateEnv {Γ} Δ₁ Δ₂ θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ _) ano 
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano'
  ... | ano-e11 , ano-e22 
    with eval i ano-e11 θ₁ t₁ | eval i ano-e22 θ₂ t₂ 
  ... | T₁ | T₂ = bind T₁ λ v₁ -> 
                  bind T₂ λ v₂ -> now (pair (+ₘ-transpose Ξₑ₁ Ξ₁ Ξₑ₂ _) v₁ v₂) 

  eval {Θ} {Ξₑ} {Γ} i ano θ (letpair {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} m t₀ t) 
    with separateEnv {Γ} (m ×ₘ Δ₀) Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with weakenΔ-valEnv Γ θ₁ 
  ... | Ξₑ₁' , θ₁' , refl 
    with subst all-no-omega (+ₘ-transpose (m ×ₘ Ξₑ₁') Ξₑ₂ (m ×ₘ Ξ₀) Ξ) ano
  ... | ano' 
    with all-no-omega-dist (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) _ ano' 
  ... | ano-me1'm0 , ano-e2-  
    with subst all-no-omega (sym (×ₘ-dist m Ξₑ₁' _)) ano-me1'm0 
  ... | ano-m[e1'0]
    with all-no-omega-dist-×ₘ m _ ano-m[e1'0] 
  ... | ano-e1'0 
    with eval i ano-e1'0 θ₁' t₀ 
  ... | T₀  = bind T₀ λ { (pair {Ξ₁ = Ξ₁} {Ξ₂} spΞ v₁ v₂) → 
                   let ano-m[12] : all-no-omega (m ×ₘ (Ξ₁ +ₘ Ξ₂))
                       ano-m[12] = subst all-no-omega (cong (m ×ₘ_) (sym spΞ)) ano-m[e1'0] 

                       ano-m1m2 : all-no-omega (m ×ₘ Ξ₁ +ₘ m ×ₘ Ξ₂)
                       ano-m1m2 = subst all-no-omega (×ₘ-dist m Ξ₁ Ξ₂) ano-m[12]

                       an : all-no-omega (m ×ₘ Ξ₁) × all-no-omega (m ×ₘ Ξ₂) 
                       an = all-no-omega-dist (m ×ₘ Ξ₁) _ ano-m1m2         

                       eq : m ×ₘ Ξ₁ +ₘ (m ×ₘ Ξ₂ +ₘ Ξₑ₂) ≡ m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ Ξₑ₂
                       eq = begin
                              m ×ₘ Ξ₁ +ₘ (m ×ₘ Ξ₂ +ₘ Ξₑ₂)
                            ≡⟨ sym (+ₘ-assoc (m ×ₘ Ξ₁) (m ×ₘ Ξ₂) _) ⟩ 
                              m ×ₘ Ξ₁ +ₘ m ×ₘ Ξ₂ +ₘ Ξₑ₂
                            ≡⟨ cong (_+ₘ Ξₑ₂) (sym (×ₘ-dist m Ξ₁ Ξ₂)) ⟩ 
                              m ×ₘ (Ξ₁ +ₘ Ξ₂) +ₘ Ξₑ₂ 
                            ≡⟨ cong (_+ₘ Ξₑ₂) (cong (m ×ₘ_) spΞ) ⟩ 
                              m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂ 
                            ≡⟨ cong (_+ₘ Ξₑ₂) (×ₘ-dist m _ _) ⟩ 
                              m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ Ξₑ₂
                            ∎

                       θ' : ValEnv (_ ∷ _ ∷ Γ) (M→M₀ m ∷ M→M₀ m ∷ Δ) Θ (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ Ξₑ₂)
                       θ' = tup (m ×ₘ Ξ₁) _ eq (value-to-multM (proj₁ an) v₁)
                                  (tup (m ×ₘ Ξ₂) Ξₑ₂ refl (value-to-multM (proj₂ an) v₂) θ₂)

                       eq' : m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ Ξₑ₂ +ₘ Ξ ≡ (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ (m ×ₘ Ξ₀ +ₘ Ξ)
                       eq' = begin
                              m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ Ξₑ₂ +ₘ Ξ
                             ≡⟨ +ₘ-assoc (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) Ξₑ₂ _ ⟩ 
                              m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ)
                             ≡⟨ +ₘ-transpose (m ×ₘ Ξₑ₁') (m ×ₘ Ξ₀) Ξₑ₂ _ ⟩ 
                              (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ (m ×ₘ Ξ₀ +ₘ Ξ)
                             ∎ 
                           -- solve 4 (λ a b c d -> 
                           --                 ((a ⊞ b) ⊞ c) ⊞ d ⊜ 
                           --                 (a ⊞ c) ⊞ (b ⊞ d)) refl (m ×ₘ Ξₑ₁') (m ×ₘ Ξ₀) Ξₑ₂ Ξ
                   in dmap (substV eq') (eval i (subst all-no-omega (sym eq') ano) θ' t) 
              }


  eval i ano θ (inl t) = dmap inl (eval i ano θ t) 
  eval i ano θ (inr t) = dmap inr (eval i ano θ t)
  eval {Θ} {Ξₑ = Ξₑ} {Γ} i ano θ (case {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} m t₀ t₁ t₂) 
    with separateEnv {Γ} (m ×ₘ Δ₀) Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with weakenΔ-valEnv Γ θ₁ 
  ... | Ξₑ₁' , θ₁' , refl 
    with subst all-no-omega (+ₘ-transpose (m ×ₘ Ξₑ₁') Ξₑ₂ (m ×ₘ Ξ₀) Ξ) ano
  ... | ano' 
    with all-no-omega-dist (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) _ ano' 
  ... | ano-me1'm0 , ano-e2-  
    with subst all-no-omega (sym (×ₘ-dist m Ξₑ₁' _)) ano-me1'm0 
  ... | ano-m[e1'0]
    with all-no-omega-dist-×ₘ m _ ano-m[e1'0] 
  ... | ano-e1'0 
    with eval i ano-e1'0 θ₁' t₀ 
  ... | T₀ =  bind T₀ λ { 
                (inl v) → 
                  let θ' : ValEnv (_ ∷ Γ) (M→M₀ m ∷ Δ) Θ (m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂)
                      θ' = tup (m ×ₘ (Ξₑ₁' +ₘ Ξ₀)) Ξₑ₂ refl (value-to-multM ano-m[e1'0] v) θ₂
                  in dmap (substV lemma) (eval i (subst all-no-omega (sym lemma) ano) θ' t₁) ; 
                (inr v) →
                  let θ' : ValEnv (_ ∷ Γ) (M→M₀ m ∷ Δ) Θ (m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂)
                      θ' = tup (m ×ₘ (Ξₑ₁' +ₘ Ξ₀)) Ξₑ₂ refl (value-to-multM ano-m[e1'0] v) θ₂
                  in dmap (substV lemma) (eval i (subst all-no-omega (sym lemma) ano) θ' t₂) 
              }
      where
        lemma : m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂ +ₘ Ξ ≡ 
                (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ (m ×ₘ Ξ₀ +ₘ Ξ)
        lemma = 
          begin
            m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂ +ₘ Ξ
          ≡⟨ cong (λ x -> x +ₘ Ξₑ₂ +ₘ Ξ) (×ₘ-dist m Ξₑ₁' _) ⟩ 
            m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ Ξₑ₂ +ₘ Ξ 
          ≡⟨ +ₘ-assoc (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) Ξₑ₂ _ ⟩ 
            m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ)
          ≡⟨ +ₘ-transpose _ _ _ _ ⟩ 
           (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ (m ×ₘ Ξ₀ +ₘ Ξ)
          ∎

  eval i ano θ (roll t) = dmap roll (eval i ano θ t)
  eval i ano θ (unroll t) = 
   bind (eval i ano θ t) λ { (roll v) → later λ where .force -> now v  }


  eval {Γ = Γ} i ano θ (unit● ad) with discardable-has-no-resources {Γ} θ ad
  ... | refl = now (red (substR (sym (∅-lid _)) unit●))

  eval {Θ} {Ξₑ} {Γ} i ano θ (letunit● {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} t₀ t) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ <- separateEnv {Γ} Δ₀ Δ θ
    let lemma : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₀ +ₘ Ξ) ≡ Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ)
        lemma = +ₘ-transpose _ _ _ _ 
    let ano' = subst all-no-omega lemma ano 
    ano-e10 , ano-e2- <- all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano' 
    bindR (eval i ano-e10 θ₁ t₀) λ E₀ -> 
     bindR (eval i ano-e2- θ₂ t) λ E -> 
       now (red (substR (sym lemma) (letunit● E₀ E)))

  eval {Θ} {Ξₑ} {Γ} i ano θ (pair● {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} t₁ t₂) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ <- separateEnv {Γ} Δ₁ Δ₂ θ
    let lemma : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₁ +ₘ Ξ₂) ≡ Ξₑ₁ +ₘ Ξ₁ +ₘ (Ξₑ₂ +ₘ Ξ₂)
        lemma = +ₘ-transpose _ _ _ _ 
    let ano' = subst all-no-omega lemma ano
    ano-e11 , ano-e22 <- all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano' 
    bindR (eval i ano-e11 θ₁ t₁) λ E₁ -> 
      bindR (eval i ano-e22 θ₂ t₂) λ E₂ -> 
        now (red (substR (sym lemma) (pair● E₁ E₂)))  
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (letpair● {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} t₀ t) 
    with separateEnv {Γ} Δ₀ Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₀ _) ano 
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano' 
  ... | ano-e10 , ano-e2- 
    with eval i ano-e10 θ₁ t₀ | eval i (one ∷ one ∷ ano-e2-) (weakenΘ-valEnv Γ (compat-ext-here (compat-ext-here ext-id)) θ₂) t 
  ... | T₁ | T = 
    bind T₁ λ { (red E₁) -> 
     bind T  λ { (red E ) -> 
       now (red (substR (+ₘ-transpose Ξₑ₁ Ξ₀ _ _) (letpair● E₁ E)))
     }}

  eval i ano θ (inl● t) = 
    bindR (eval i ano θ t) λ E -> now (red (inl● E))
    
  
  eval i ano θ (inr● t) = 
    bindR (eval i ano θ t) λ E -> now (red (inr● E))    
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (case● {Δ₀ = Δ₀} {Δ} {Δ'} {Ξ₀ = Ξ₀} {Ξ} {Ξ'} t t₁ t₂ t₃) 
    with separateEnv {Γ} (Δ₀ +ₘ Δ) _ θ 
  ... | tup Ξₑ₁₂ Ξₑ₃ refl θ' θ₃
    with discardable-has-no-resources {Γ} θ₃ (omega×ₘ-discardable Δ') 
  ... | refl 
    with weakenΔ-valEnv Γ θ₃
  ... | Ξₑ₃' , θ₃' , eq
    with omega×ₘ∅-inv Ξₑ₃' eq 
  ... | refl 
    with separateEnv {Γ} Δ₀ Δ θ' 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega lemma ano | lemma 
    where
      open import Algebra.Solver.CommutativeMonoid (+ₘ-commutativeMonoid (length Θ)) 
                  renaming (_⊕_ to _⊞_)

      lemma : Ξₑ₁ +ₘ Ξₑ₂ +ₘ ∅ +ₘ (Ξ₀ +ₘ Ξ +ₘ omega ×ₘ Ξ') 
              ≡ (Ξₑ₁ +ₘ Ξ₀) +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ Ξ' 
      lemma = solve 5 (\a b c d e -> ((a ⊞ b) ⊞ id) ⊞ ((c ⊞ d) ⊞ e) 
                                     ⊜ ((a ⊞ c) ⊞ (b ⊞ d)) ⊞ e) refl Ξₑ₁ Ξₑ₂ Ξ₀ Ξ (omega ×ₘ Ξ')
  ... | ano' | lemma 
    with all-no-omega-dist ((Ξₑ₁ +ₘ Ξ₀) +ₘ (Ξₑ₂ +ₘ Ξ)) _ ano' 
  ... | ano'' , ano₃ 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano''
  ... | ano-e10 , ano-e2- 
    with all-no-omega-omega×ₘ Ξ' ano₃ 
  ... | refl
    with eval i ano-e10 θ₁ t | eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₃' t₃ 
  ... | T | T₃ = 
        bind T λ { (red r) ->
        bind T₃ λ { f -> 
          now (red (substR (trans lemma' (sym lemma))
            let f' = weakenΘ-value smashΘ (subst (λ x -> Value Θ x _) (∅-lid ∅) f)
            in (case● r refl θ₂ t₁ θ₂ t₂ f')))
      -- case● (subst all-no-omega lemma' ano') r refl ano-e2- θ₂ t₁ θ₂ t₂ f
        }
        }
      where
        lemma' : Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) 
                 ≡ Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ ∅
        lemma' = 
          sym (trans (cong (λ x -> Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ x)
                           (×ₘ∅ omega))
                     (∅-rid (Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) )))

        -- lemma' : Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ ∅                   
        --          ≡ Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ (∅ +ₘ ∅) 
        -- lemma' = cong (λ x -> Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ x) (sym (∅-lid _))

 
  eval {Θ} {Ξₑ} {Γ} i ano θ (var● x ad ok) 
    with discardable-has-no-resources {Γ} θ ad
  ... | refl = now (red (substR (sym (∅-lid _)) (var● x ok)))

  eval {Θ} {Ξₑ} {Γ} i ano θ (pin {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} t₁ t₂) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂  <- separateEnv {Γ} Δ₁ Δ₂ θ 
    let ano' = subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ _) ano
    ano-e11 , ano-e22 <- all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano' 
    bindR (eval i ano-e11 θ₁ t₁) λ r -> 
      bind (eval i ano-e22 θ₂ t₂) λ v -> 
        now (red (substR (+ₘ-transpose _ _ _ _) (pin r v)))
     
    
  
  eval {Γ = Γ} i ano θ (unlift e) = do
    Ξ' , θ' , refl <- weakenΔ-valEnv Γ θ
    ano₁ , ano₂  <- all-no-omega-dist _ _ ano 
    refl <- all-no-omega-omega×ₘ _ ano₁  
    refl <- all-no-omega-omega×ₘ _ ano₂ 
    bind (eval i (subst all-no-omega (sym (∅-lid ∅)) all-no-omega-∅ ) θ' e) λ v -> 
      bindR (apply i (one ∷ subst all-no-omega (sym lemma₁) all-no-omega-∅) (weakenΘ-value (compat-ext-here ext-id) v) (red var●₀)) λ r -> 
        now (substV (sym lemma₂) (inj refl (weakenΘ-residual (compat-skip smashΘ) (substR (cong (one ∷_) lemma₁) r) )))
    where
      open import Data.Vec.Properties using (map-id) 
      lemma₁ : ∀ {n} -> ∅ +ₘ ∅ +ₘ Data.Vec.map (λ y -> y) ∅ ≡ ∅ {n}
      lemma₁ {n} rewrite map-id (∅ {n}) | ∅-rid {n} ∅ = ∅-lid ∅ 

      lemma₂ : ∀ {n} -> omega ×ₘ ∅ +ₘ omega ×ₘ ∅ ≡ ∅ {n} 
      lemma₂ {n} rewrite ×ₘ∅ {n} omega | ∅-lid {n} ∅ = refl 
    
  eval {Γ = Γ} i ano θ (fapp e₁ e₂) = do 
    anoₑ , ano'  <- all-no-omega-dist _ _ ano 
    ano₁ , ano'' <- all-no-omega-dist _ _ ano'
    refl <- all-no-omega-omega×ₘ _ ano''     
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂  <- separateEnv {Γ} _ _ θ 
    Ξₑ₂' , θ₂' , refl <- weakenΔ-valEnv Γ θ₂
    ano₁' , _ <- all-no-omega-dist _ _ (subst all-no-omega lemma' ano)
    bind (eval i ano₁' θ₁ e₁) λ { 
      (inj spΞ r) → do 
        refl , refl <- ∅+ₘ∅-inv _ _ (sym spΞ)
        refl <- all-no-omega-omega×ₘ _ (subst all-no-omega (∅-lid _) anoₑ)         
        bind (eval i (subst all-no-omega (sym (∅-lid ∅)) all-no-omega-∅) θ₂' e₂) λ v -> later λ { .force {j} -> 
           bind (forward (evalR j (one ∷ all-no-omega-∅) r) (weakenΘ-value smashΘ (substV (∅-lid ∅) v) ∷ [])) λ v' -> 
            now (substV (sym lemma) (weakenΘ-value extendΘ v'))
         } 
     } 
    where
      lemma' : ∀ {n} {Ξₑ₁ Ξ₁ X Y : MultEnv n} -> Ξₑ₁ +ₘ X +ₘ (Ξ₁ +ₘ Y) ≡ Ξₑ₁ +ₘ Ξ₁ +ₘ (X +ₘ Y)
      lemma' {n} {A} {B} {C} {D} = +ₘ-transpose A C B D 

      lemma : ∀ {n} -> ∅ +ₘ omega ×ₘ ∅ +ₘ (∅ +ₘ omega ×ₘ ∅) ≡ ∅ {n} 
      lemma {n} rewrite ×ₘ∅ {n} omega | ∅-lid {n} ∅ = ∅-lid ∅

  eval {Γ = Γ} i ano θ (bapp e₁ e₂) = do 
    anoₑ , ano'  <- all-no-omega-dist _ _ ano 
    ano₁ , ano'' <- all-no-omega-dist _ _ ano'
    refl <- all-no-omega-omega×ₘ _ ano''     
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂  <- separateEnv {Γ} _ _ θ 
    Ξₑ₂' , θ₂' , refl <- weakenΔ-valEnv Γ θ₂
    ano₁' , _ <- all-no-omega-dist _ _ (subst all-no-omega lemma' ano)
    bind (eval i ano₁' θ₁ e₁) λ { 
      (inj spΞ r) → do 
        refl , refl <- ∅+ₘ∅-inv _ _ (sym spΞ)
        refl <- all-no-omega-omega×ₘ _ (subst all-no-omega (∅-lid _) anoₑ)         
        bind (eval i (subst all-no-omega (sym (∅-lid ∅)) all-no-omega-∅) θ₂' e₂) λ v -> later λ { .force {j} -> 
          bind (backward (evalR j (one ∷ all-no-omega-∅) r) (weakenΘ-value smashΘ (substV (∅-lid ∅) v))) λ { (v' ∷ []) -> 
             now (substV (sym lemma) (weakenΘ-value extendΘ v'))
           }
           -- bind (forward (evalR j (one ∷ all-no-omega-∅) r) (weakenΘ-value smashΘ (substV (∅-lid ∅) v) ∷ [])) λ v' -> 
           --  now (substV (sym lemma) (weakenΘ-value extendΘ v'))
         } 
     } 
    where
      lemma' : ∀ {n} {Ξₑ₁ Ξ₁ X Y : MultEnv n} -> Ξₑ₁ +ₘ X +ₘ (Ξ₁ +ₘ Y) ≡ Ξₑ₁ +ₘ Ξ₁ +ₘ (X +ₘ Y)
      lemma' {n} {A} {B} {C} {D} = +ₘ-transpose A C B D 

      lemma : ∀ {n} -> ∅ +ₘ omega ×ₘ ∅ +ₘ (∅ +ₘ omega ×ₘ ∅) ≡ ∅ {n} 
      lemma {n} rewrite ×ₘ∅ {n} omega | ∅-lid {n} ∅ = ∅-lid ∅
      
  
  -- eval {Θ} {Ξₑ} {Γ} i ano θ (fwd {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} {A = A} {B} t₁ t₂) 
  --   with separateEnv {Γ} (omega ×ₘ Δ₁) (omega ×ₘ Δ₂) θ
  -- ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
  --   with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ (omega ×ₘ Ξ₁) (omega ×ₘ Ξ₂)) ano
  -- ... | ano' 
  --   with weakenΔ-valEnv Γ θ₁ | weakenΔ-valEnv Γ θ₂ 
  -- ... | Ξₑ₁' , θ₁' , refl | Ξₑ₂' , θ₂' , refl 
  --   with all-no-omega-dist (omega ×ₘ Ξₑ₁' +ₘ omega ×ₘ Ξ₁) _ ano'
  -- ... | ano₁ , ano₂ 
  --   with all-no-omega-dist (omega ×ₘ Ξₑ₁') _ ano₁ | all-no-omega-dist (omega ×ₘ Ξₑ₂') _ ano₂ 
  -- ... | ano-me1' , ano-m1 | ano-me2' , ano-m2 
  --   with all-no-omega-omega×ₘ _ ano-me1' | all-no-omega-omega×ₘ _ ano-m1 | all-no-omega-omega×ₘ _ ano-me2' | all-no-omega-omega×ₘ _ ano-m2 
  -- ... | refl | refl | refl | refl 
  --   with eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₁' t₁ | eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₂' t₂ 
  -- ... | T₁ | T₂ = 
  --   bind T₁ λ f -> 
  --   bind (subst (λ x -> Delay (Value Θ x A) i) (∅-lid ∅) T₂) λ v -> 
  --     bind (apply i (one ∷ subst all-no-omega lemma₁ all-no-omega-∅) (weakenΘ-value (compat-ext-here ext-id) f) (red var●₀)) λ { (red bx) -> 
  --       later λ { .force {k} -> 
  --         bind (forward (evalR k (one ∷ all-no-omega-∅) (substR (cong (one ∷_) (sym lemma₁)) bx)) (weakenΘ-value smashΘ v ∷ emptyRValEnv)) λ { v' -> 
  --           now (substV lemma₂ (weakenΘ-value extendΘ v'))
  --         }
  --       }
  --   }
  --   where
  --     open import Data.Vec.Properties using (map-id) 
  --     lemma₁ : ∀ {n} -> ∅ {n} ≡ ∅ +ₘ ∅ +ₘ Data.Vec.map (λ y -> y) ∅ 
  --     lemma₁ {_} = sym (trans (cong₂ (_+ₘ_) (∅-lid ∅) (map-id ∅)) (∅-lid ∅))  
   
  --     lemma₂ : ∀ {n} -> (∅ {n} ≡ (omega ×ₘ ∅ +ₘ omega ×ₘ ∅) +ₘ (omega ×ₘ ∅ +ₘ omega ×ₘ ∅))
  --     lemma₂ {_} = sym (trans (cong₂ (_+ₘ_) (cong₂ (_+ₘ_) (×ₘ∅ omega) (×ₘ∅ omega)) (cong₂ (_+ₘ_) (×ₘ∅ omega) (×ₘ∅ omega)))
  --                                    (trans (cong (_+ₘ (∅ +ₘ ∅)) (∅-lid ∅)) 
  --                                          (trans (∅-lid _) (∅-lid ∅))))
      

  
  -- eval {Θ} {Ξₑ} {Γ} i ano θ (bwd {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} {A = A} {B} t₁ t₂)
  --     with separateEnv {Γ} (omega ×ₘ Δ₁) (omega ×ₘ Δ₂) θ
  -- ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
  --   with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ (omega ×ₘ Ξ₁) (omega ×ₘ Ξ₂)) ano
  -- ... | ano' 
  --   with weakenΔ-valEnv Γ θ₁ | weakenΔ-valEnv Γ θ₂ 
  -- ... | Ξₑ₁' , θ₁' , refl | Ξₑ₂' , θ₂' , refl 
  --   with all-no-omega-dist (omega ×ₘ Ξₑ₁' +ₘ omega ×ₘ Ξ₁) _ ano'
  -- ... | ano₁ , ano₂ 
  --   with all-no-omega-dist (omega ×ₘ Ξₑ₁') _ ano₁ | all-no-omega-dist (omega ×ₘ Ξₑ₂') _ ano₂ 
  -- ... | ano-me1' , ano-m1 | ano-me2' , ano-m2 
  --   with all-no-omega-omega×ₘ _ ano-me1' | all-no-omega-omega×ₘ _ ano-m1 | all-no-omega-omega×ₘ _ ano-me2' | all-no-omega-omega×ₘ _ ano-m2 
  -- ... | refl | refl | refl | refl 
  --   with eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₁' t₁ | eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₂' t₂ 
  -- ... | T₁ | T₂ = 
  --   bind T₁ λ f -> 
  --   bind (subst (λ x -> Delay (Value Θ x B) i) (∅-lid ∅) T₂) λ v' -> 
  --     bind (apply i (one ∷ subst all-no-omega lemma₁ all-no-omega-∅) (weakenΘ-value (compat-ext-here ext-id) f) (red var●₀)) λ { (red bx) -> 
  --       later λ { .force {k} -> 
  --         bind (backward (evalR k (one ∷ all-no-omega-∅) (substR (cong (one ∷_) (sym lemma₁)) bx)) (weakenΘ-value smashΘ v')) λ { (v ∷ _) -> 
  --         now (substV lemma₂ (weakenΘ-value extendΘ v)) 
  --       }
  --       } 
  --     }
  --   where
  --     open import Data.Vec.Properties using (map-id) 
  --     lemma₁ : ∀ {n} -> ∅ {n} ≡ ∅ +ₘ ∅ +ₘ Data.Vec.map (λ y -> y) ∅ 
  --     lemma₁ {_} = sym (trans (cong₂ (_+ₘ_) (∅-lid ∅) (map-id ∅)) (∅-lid ∅))  
   
  --     lemma₂ : ∀ {n} -> (∅ {n} ≡ (omega ×ₘ ∅ +ₘ omega ×ₘ ∅) +ₘ (omega ×ₘ ∅ +ₘ omega ×ₘ ∅))
  --     lemma₂ {_} = sym (trans (cong₂ (_+ₘ_) (cong₂ (_+ₘ_) (×ₘ∅ omega) (×ₘ∅ omega)) (cong₂ (_+ₘ_) (×ₘ∅ omega) (×ₘ∅ omega)))
  --                                    (trans (cong (_+ₘ (∅ +ₘ ∅)) (∅-lid ∅)) 
  --                                          (trans (∅-lid _) (∅-lid ∅))))


open Interpreter public 
