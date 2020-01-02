{-# OPTIONS --without-K #-}

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

_ = 1  

module Interpreter where 
  open import Codata.Delay renaming (length to dlength ; map to dmap )
  open import Codata.Thunk

  eval : 
    ∀ {Θ Ξₑ Γ Δ Ξ A} i -> 
    all-no-omega (Ξₑ +ₘ Ξ) -> ValEnv Γ Δ Θ Ξₑ -> Term Γ Δ Θ Ξ A -> Delay (Value Θ (Ξₑ +ₘ Ξ) A) i 

{-
  eval {Θ} _ ano θ (var x ok) = now (subst (λ x -> Value Θ x _) (sym (∅-rid _)) (lookupVar θ ok))
  eval _ ano θ (abs m t) = now (clo m refl ano θ t) 


  eval {Θ} {Γ = Γ} i ano θ (app {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} {m = m} t₁ t₂)
      with separateEnv {Γ} Δ₁ (m ×ₘ Δ₂) θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ with eval i (proj₁ lemma) θ₁ t₁ | proj₂ lemma | weakenΔ-valEnv Γ θ₂ 
    where 
      open import Algebra.Solver.CommutativeMonoid (+ₘ-commutativeMonoid (length Θ)) 
                renaming (_⊕_ to _⊞_)

      lemma' : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₁ +ₘ m ×ₘ Ξ₂) ≡ (Ξₑ₁ +ₘ Ξ₁) +ₘ (Ξₑ₂ +ₘ m ×ₘ Ξ₂)
      lemma' = solve 4 (λ x y z w -> (x ⊞ y) ⊞ (z ⊞ w) ⊜ (x ⊞ z) ⊞ (y ⊞ w)) refl Ξₑ₁ Ξₑ₂ Ξ₁ _ 

      lemma : all-no-omega (Ξₑ₁ +ₘ Ξ₁) × all-no-omega (Ξₑ₂ +ₘ m ×ₘ Ξ₂)
      lemma = all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ (subst all-no-omega lemma' ano)  
  ... | T₁ | ano-e2m2 | Ξₑ₂' , θ₂' , refl with (subst all-no-omega (sym (×ₘ-dist m Ξₑ₂' _)) ano-e2m2)
  ... | ano-m[e2'2] with eval i (all-no-omega-dist-×ₘ m (Ξₑ₂' +ₘ Ξ₂) ano-m[e2'2]) θ₂' t₂
  ... | T₂ = 
    bind T₁ (λ { (clo {Ξ' = Ξ'} {Ξₜ = Ξₜ} m spΞ _ θf t) → bind T₂ λ v₂ -> 
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
              ≡⟨ solve 4 (λ x y z w -> (x ⊞ y) ⊞ (z ⊞ w) ⊜ (z ⊞ x) ⊞ (w ⊞ y)) refl (m ×ₘ Ξₑ₂') (m ×ₘ Ξ₂) Ξₑ₁ Ξ₁ ⟩ 
                Ξₑ₁ +ₘ m ×ₘ Ξₑ₂' +ₘ (Ξ₁ +ₘ m ×ₘ Ξ₂) 
              ∎

            lemma-ano : all-no-omega (m ×ₘ (Ξₑ₂' +ₘ Ξ₂) +ₘ Ξ' +ₘ Ξₜ)
            lemma-ano = subst all-no-omega (sym lemma) ano 
              
        in (bind (eval _ lemma-ano (tup (m ×ₘ (Ξₑ₂' +ₘ Ξ₂)) Ξ' refl (value-to-multM ano-m[e2'2] v₂) θf) t) λ v ->  now (subst (λ Ξ -> Value Θ Ξ _) lemma v)  
       )}
    })
    where 
      open import Algebra.Solver.CommutativeMonoid (+ₘ-commutativeMonoid (length Θ)) 
                renaming (_⊕_ to _⊞_)
      
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
                  bind T₂ λ v₂ -> now (pair (+ₘ-transpose Ξₑ₁ Ξ₁ Ξₑ₂ _) ano v₁ v₂) 

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
  ... | T₀  = bind T₀ λ { (pair {Ξ₁ = Ξ₁} {Ξ₂} spΞ _ v₁ v₂) → 
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
                       eq' = solve 4 (λ a b c d -> 
                                           ((a ⊞ b) ⊞ c) ⊞ d ⊜ 
                                           (a ⊞ c) ⊞ (b ⊞ d)) refl (m ×ₘ Ξₑ₁') (m ×ₘ Ξ₀) Ξₑ₂ Ξ
                   in dmap (substV eq') (eval i (subst all-no-omega (sym eq') ano) θ' t) 
              }
        where 
          open import Algebra.Solver.CommutativeMonoid (+ₘ-commutativeMonoid (length Θ)) 
                      renaming (_⊕_ to _⊞_)


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
        open import Algebra.Solver.CommutativeMonoid (+ₘ-commutativeMonoid (length Θ)) 
                    renaming (_⊕_ to _⊞_)

        lemma : m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂ +ₘ Ξ ≡ 
                (m ×ₘ Ξₑ₁' +ₘ Ξₑ₂) +ₘ (m ×ₘ Ξ₀ +ₘ Ξ)
        lemma = 
          trans (cong (λ x -> x +ₘ Ξₑ₂ +ₘ Ξ) (×ₘ-dist m Ξₑ₁' Ξ₀)) (
                solve 4 (λ a b c d -> (((a ⊞ b) ⊞ c) ⊞ d) ⊜ (a ⊞ c) ⊞ (b ⊞ d)) refl 
                        (m ×ₘ Ξₑ₁') (m ×ₘ Ξ₀) Ξₑ₂ Ξ
          )  

  eval i ano θ (roll t) = dmap roll (eval i ano θ t)
  eval i ano θ (unroll t) = 
   bind (eval i ano θ t) λ { (roll v) → later λ where .force -> now v  }


  eval {Γ = Γ} i ano θ (unit● ad) with discardable-has-no-resources {Γ} θ ad
  ... | refl = now (red (substR (sym (∅-lid _)) unit●))

  eval {Θ} {Ξₑ} {Γ} i ano θ (letunit● {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} _ t₀ t) 
    with separateEnv {Γ} Δ₀ Δ θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₀ _) ano 
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano' 
  ... | ano-e10 , ano-e2- 
    with eval i ano-e10 θ₁ t₀ | eval i ano-e2- θ₂ t 
  ... | T₀ | T = 
      bind T₀ λ { (red E₀) -> 
      bind T  λ { (red E) -> 
         now (red (substR (+ₘ-transpose _ _ _ _) (letunit● ano' E₀ E))) 
      }} 

  eval {Θ} {Ξₑ} {Γ} i ano θ (pair● {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} _ t₁ t₂) 
    with separateEnv {Γ} Δ₁ Δ₂ θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ _) ano
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano' 
  ... | ano-e11 , ano-e22 with eval i ano-e11 θ₁ t₁ | eval i ano-e22 θ₂ t₂
  ... | T₁ | T₂ = 
    bind T₁ λ { (red E₁) -> 
    bind T₂ λ { (red E₂) -> 
      now (red (substR (+ₘ-transpose _ _ _ _) (pair● ano' E₁ E₂)))
    }}
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (letpair● {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} anoLet t₀ t) 
    with separateEnv {Γ} Δ₀ Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₀ _) ano 
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano' 
  ... | ano-e10 , ano-e2- 
    with eval i ano-e10 θ₁ t₀ | eval i (one ∷ one ∷ ano-e2-) (weakenΘ-valEnv Γ (ext-here (ext-here ext-id)) θ₂) t 
  ... | T₁ | T = 
    bind T₁ λ { (red E₁) -> 
     bind T  λ { (red E ) -> 
       now (red (substR (+ₘ-transpose Ξₑ₁ Ξ₀ _ _) (letpair● ano' E₁ E)))
     }}

  eval i ano θ (inl● t) = 
    bind (eval i ano θ t) λ { (red E) -> 
      now (red (inl● E))
    }
  
  eval i ano θ (inr● t) = 
    bind (eval i ano θ t) λ { (red E) -> 
      now (red (inr● E))
    }
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (case● {Δ₀ = Δ₀} {Δ} {Δ'} {Ξ₀ = Ξ₀} {Ξ} {Ξ'} ano₁ t t₁ t₂ t₃) 
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
          now (red (substR (trans (sym lemma') (sym lemma)) (case● (subst all-no-omega lemma' ano') r refl ano-e2- θ₂ t₁ θ₂ t₂ f)))
        }
        }
      where
        lemma' : Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ ∅                   
                 ≡ Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ (∅ +ₘ ∅) 
        lemma' = cong (λ x -> Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ x) (sym (∅-lid _))

 
  eval {Θ} {Ξₑ} {Γ} i ano θ (var● x ad ok) 
    with discardable-has-no-resources {Γ} θ ad
  ... | refl = now (red (substR (sym (∅-lid _)) (var● x ok)))
-}

  eval {Θ} {Ξₑ} {Γ} i ano θ (pin {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} ano₁ t₁ t₂) 
    with separateEnv {Γ} Δ₁ Δ₂ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ _) ano
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano' 
  ... | ano-e11 , ano-e22 with eval i ano-e11 θ₁ t₁ | eval i ano-e22 θ₂ t₂
  ... | T₁ | T₂ = 
      bind T₁ λ { (red r) -> 
      bind T₂ λ { v -> 
        now (red (substR (+ₘ-transpose _ _ _ _) (pin ano' r v)))
      }}
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (fwd {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} {A = A} {B} _ t₁ t₂) 
    with separateEnv {Γ} (omega ×ₘ Δ₁) (omega ×ₘ Δ₂) θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ (omega ×ₘ Ξ₁) (omega ×ₘ Ξ₂)) ano
  ... | ano' 
    with weakenΔ-valEnv Γ θ₁ | weakenΔ-valEnv Γ θ₂ 
  ... | Ξₑ₁' , θ₁' , refl | Ξₑ₂' , θ₂' , refl 
    with all-no-omega-dist (omega ×ₘ Ξₑ₁' +ₘ omega ×ₘ Ξ₁) _ ano'
  ... | ano₁ , ano₂ 
    with all-no-omega-dist (omega ×ₘ Ξₑ₁') _ ano₁ | all-no-omega-dist (omega ×ₘ Ξₑ₂') _ ano₂ 
  ... | ano-me1' , ano-m1 | ano-me2' , ano-m2 
    with all-no-omega-omega×ₘ _ ano-me1' | all-no-omega-omega×ₘ _ ano-m1 | all-no-omega-omega×ₘ _ ano-me2' | all-no-omega-omega×ₘ _ ano-m2 
  ... | refl | refl | refl | refl 
    with eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₁' t₁ | eval i (subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ₂' t₂ 
  ... | T₁ | T₂ = 
      bind T₁ λ { (clo {Ξ' = Ξ'} {Γ' = Γ'} {Δ'} {Ξₜ = Ξₜ}   m spΞ _ θf t) -> 
      bind T₂ λ { v -> 
          later λ { .force {j} -> 
          CASE ∅+ₘ∅-inv Ξ' Ξₜ (trans spΞ (∅-lid ∅)) OF λ { 
             ( refl , refl ) -> 
               let  x : Residual (A ∷ Θ) (one ∷ ∅) (A ●) 
                    x = var● vz (here all-zero-∅) 

                    θ' : ValEnv (A ● ∷ Γ') (one ∷ Δ') (A ∷ Θ) (one ∷ ∅)
                    θ' = tup _ ∅ (∅-rid _) (mult-one (red x)) (weakenΘ-valEnv Γ' (ext-here ext-id) θf)

                    Tf = eval j (one ∷ subst all-no-omega (sym (∅-lid _)) all-no-omega-∅) θ' (weakenΘ-term (ext-here ext-id) t)
               in
               bind Tf λ { (red bx) -> 
                 {!
                 
            !} 
               }
          }          
          } 
      }}

  
  eval {Θ} {Ξₑ} {Γ} i ano θ (bwd {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} ano₁ t₁ t₂) = {!!} 

