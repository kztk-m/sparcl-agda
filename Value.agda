{-# OPTIONS --without-K #-}

open import Level renaming (zero to lzero ; suc to lsuc)
open import Syntax
open import Data.List using (length ; [] ; _∷_ ) renaming ( _++_ to _++L_ ) 
open import Data.Vec  using ([] ; _∷_  ) renaming ( _++_ to _++V_ )

open import Data.Vec.All using (All ; [] ; _∷_)
open import Data.Nat 

open import Data.Product
open import Function using () renaming (case_of_ to case*_of_)

open import Size
open import Relation.Binary.PropositionalEquality

Dom : ∀ ℓ -> Set (lsuc ℓ)
Dom ℓ = (Θ : TyEnv) -> (Ξ : MultEnv (length Θ)) -> Set ℓ 

data _⊛_ {ℓ : Level} 
         (F : Dom ℓ)
         (G : Dom ℓ) 
         (Θ : TyEnv) (Ξ : MultEnv (length Θ)) : Set ℓ where 
     tup : ∀ Ξ₁ Ξ₂ -> (spΞ : Ξ₁ +ₘ Ξ₂ ≡ Ξ) -> 
           (fst : F Θ Ξ₁) -> (snd : G Θ Ξ₂) -> (F ⊛ G) Θ Ξ

data mult {ℓ : Level} (F : Dom ℓ) : (m : Multiplicity₀) -> Dom ℓ where
  mult-zero : 
    ∀ {Θ Ξ} -> 
    (eq : Ξ ≡ ∅) -> 
    mult F zero Θ Ξ

  mult-one : 
    ∀ {Θ Ξ} -> 
    (v : F Θ Ξ) -> mult F one Θ Ξ
  mult-omega : 
    ∀ {Θ Ξ} -> 
    (v : F Θ ∅) -> (eq : Ξ ≡ ∅) -> mult F omega Θ Ξ

data Residual (Θ : TyEnv) : MultEnv (length Θ) -> Ty zero -> {i : Size} -> Set 
data Value (Θ : TyEnv) : MultEnv (length Θ) -> Ty zero -> {i : Size} -> Set 
ValEnv : 
  (Γ : TyEnv) -> (Δ : MultEnv (length Γ)) -> {i : Size} -> 
  (Θ : TyEnv) -> MultEnv (length Θ) -> Set

ValEnv [] Δ {i}            = λ Θ Ξ -> Ξ ≡ ∅ 
ValEnv (A ∷ Γ) (m ∷ Δ) {i} = 
  mult (V A) m ⊛ ValEnv Γ Δ {i}
  where
    V : Ty zero -> Dom 0ℓ 
    V A Θ Ξ = Value Θ Ξ A {i} 
  

data Value Θ where 
  clo :
    ∀ {Ξ Ξ' Γ' Δ' A B Ξₜ i} -> 
    (m : Multiplicity) -> 
    (spΞ : Ξ' +ₘ Ξₜ ≡ Ξ) -> 
    (ano : all-no-omega Ξ) -> 
    (θ : ValEnv Γ' Δ' {i} Θ Ξ' ) -> 
    (t : Term (A ∷ Γ') (M→M₀ m ∷ Δ') Θ Ξₜ B) ->
    Value Θ Ξ (A # m ~> B) {↑ i} 

  unit : 
    ∀ {Ξ i} -> 
    (eq : ∅ ≡ Ξ) -> 
    Value Θ Ξ tunit {↑ i} 

  pair : 
    ∀ {Ξ Ξ₁ Ξ₂ A B i} -> 
    (spΞ : Ξ₁ +ₘ Ξ₂ ≡ Ξ) ->
    (ano : all-no-omega Ξ) -> 
    Value Θ Ξ₁ A {i} ->
    Value Θ Ξ₂ B {i} ->
    Value Θ Ξ (A ⊗ B) {↑ i} 

  inl  : 
    ∀ {Ξ} {A B i} -> 
    Value Θ Ξ A {i} -> 
    Value Θ Ξ (A ⊕ B) {↑ i} 

  inr : 
    ∀ {Ξ} {A B i} -> 
    Value Θ Ξ B {i} -> 
    Value Θ Ξ (A ⊕ B) {↑ i} 

  roll : 
    ∀ {Ξ F i} -> 
    Value Θ Ξ (substTy F (μ F)) {i} -> 
    Value Θ Ξ (μ F) {↑ i} 

  red : 
    ∀ {Ξ A i} -> 
    Residual Θ Ξ (A ●) {i} -> 
    Value Θ Ξ (A ●) {↑ i} 

data Residual Θ where 
  unit● : 
    ∀ {i} ->
    Residual Θ ∅ (tunit ●) {↑ i} 

  letunit● : 
    ∀ {Ξ₀ Ξ A i} -> 
    (ano : all-no-omega (Ξ₀ +ₘ Ξ)) -> 
    Residual Θ Ξ₀ (tunit ●) {i} ->
    Residual Θ Ξ  (A ●) {i} -> 
    Residual Θ (Ξ₀ +ₘ Ξ) (A ●) {↑ i} 

  pair● : 
    ∀ {Ξ₁ Ξ₂ A B i} -> 
    (ano : all-no-omega (Ξ₁ +ₘ Ξ₂)) -> 
    Residual Θ Ξ₁ (A ●) {i} -> 
    Residual Θ Ξ₂ (B ●) {i} -> 
    Residual Θ (Ξ₁ +ₘ Ξ₂) ((A ⊗ B) ●) {↑ i} 

  letpair● : 
    ∀ {Ξ₀ Ξ A B C i} -> 
    (ano : all-no-omega (Ξ₀ +ₘ Ξ)) -> 
    Residual Θ Ξ₀ ((A ⊗ B) ●) {i} -> 
    Residual (A ∷ B ∷ Θ) (one ∷ one ∷ Ξ) (C ●) {i} -> 
    Residual Θ (Ξ₀ +ₘ Ξ) (C ●) {↑ i}
  
  inl● : 
    ∀ {Ξ} {A B} {i} -> 
    Residual Θ Ξ (A ●) {i} -> 
    Residual Θ Ξ ((A ⊕ B) ●) {↑ i} 

  inr● : 
    ∀ {Ξ} {A B} {i} -> 
    Residual Θ Ξ (B ●) {i} -> 
    Residual Θ Ξ ((A ⊕ B) ●) {↑ i} 

  case● : 
    ∀ {Ξ₀ Ξ Ξ' Ξₑ Ξₜ Γ₁ Γ₂ Δ₁ Δ₂ A B C i} -> 
    (ano : all-no-omega (Ξ₀ +ₘ Ξ +ₘ omega ×ₘ Ξ')) -> 
    Residual Θ Ξ₀ ((A ⊕ B) ●) {i} ->
    (spΞ : Ξₑ +ₘ Ξₜ ≡ Ξ) -> 
    (ano₁ : all-no-omega Ξ) -> 
    (θ₁ : ValEnv Γ₁ Δ₁ {i} Θ Ξₑ) ->
    (t₁ : Term Γ₁ Δ₁ (A ∷ Θ) (one ∷ Ξₜ) (C ●)) -> 
    (θ₂ : ValEnv Γ₂ Δ₂ {i} Θ Ξₑ) ->
    (t₂ : Term Γ₂ Δ₂ (B ∷ Θ) (one ∷ Ξₜ) (C ●)) -> 
    (v : Value Θ Ξ' (C # omega ~> tbool) {i}) -> 
    Residual Θ (Ξ₀ +ₘ Ξ +ₘ omega ×ₘ Ξ') (C ●) {↑ i} 


  var● : ∀ {Ξ A i} -> 
         (x : Θ ∋ A) -> (ok : varOk● Θ x Ξ) ->
         Residual Θ Ξ (A ●) {↑ i}

  pin : ∀ {Ξ₁ Ξ₂ A B i} -> 
        (ano : all-no-omega (Ξ₁ +ₘ Ξ₂)) -> 
        Residual Θ Ξ₁ (A ●) {i} ->          
        (v : Value    Θ Ξ₂ (A # omega ~> B ●) {i}) -> 
        Residual Θ (Ξ₁ +ₘ Ξ₂) ((A ⊗ B) ●) {↑ i} 

open ≡-Reasoning

discardable-has-no-resources : ∀ {Γ Δ Θ Ξ} -> ValEnv Γ Δ Θ Ξ -> All discardable Δ -> Ξ ≡ ∅ 
discardable-has-no-resources {[]} {Δ} θ ad = θ
discardable-has-no-resources {A ∷ Γ} {.omega ∷ Δ} (tup .∅ Ξ₂ spΞ (mult-omega v refl) snd) (omega ∷ ad) = 
     begin 
      _
     ≡⟨ sym spΞ ⟩ 
      ∅ +ₘ Ξ₂ 
     ≡⟨ ∅-lid Ξ₂ ⟩ 
      Ξ₂ 
     ≡⟨ discardable-has-no-resources {Γ} {Δ} snd ad ⟩ 
      ∅ 
     ∎    
discardable-has-no-resources {A ∷ Γ} {.zero ∷ Δ} (tup .∅ Ξ₂ spΞ (mult-zero refl) snd) (zero ∷ ad) = 
     begin 
      _
     ≡⟨ sym spΞ ⟩ 
      ∅ +ₘ Ξ₂ 
     ≡⟨ ∅-lid Ξ₂ ⟩ 
      Ξ₂ 
     ≡⟨ discardable-has-no-resources {Γ} {Δ} snd ad ⟩ 
      ∅ 
     ∎    

lookupVar : ∀ {Γ Δ Θ Ξ A} {x : Γ ∋ A} -> ValEnv Γ Δ Θ Ξ -> varOk Γ x Δ -> Value Θ Ξ A 
lookupVar (tup .(∅) Ξ₂ spΞ (mult-omega v refl) snd) (there omega ok) with (trans (sym (∅-lid _)) spΞ)
... | refl = lookupVar snd ok
lookupVar (tup .∅ Ξ₂ spΞ (mult-zero refl) snd) (there zero ok) with (trans (sym (∅-lid _)) spΞ)
... | refl = lookupVar snd ok
lookupVar {Γ = A ∷ Γ} {Δ = m ∷ Δ} (tup Ξ₁ Ξ₂ spΞ fst snd) (here u ad) with discardable-has-no-resources {Γ} {Δ} snd ad 
... | refl with trans (sym (∅-rid _)) spΞ 
lookupVar {A ∷ Γ} {.omega ∷ Δ} (tup .∅ .∅ spΞ (mult-omega v refl) snd) (here omega ad) | refl | refl = v
lookupVar {A ∷ Γ} {.one ∷ Δ} (tup Ξ₁ .∅ spΞ (mult-one v) snd) (here one ad) | refl | refl = v 


separateEnv : ∀ {Γ Θ Ξ} -> ∀ Δ₁ Δ₂ -> 
              ValEnv Γ (Δ₁ +ₘ Δ₂) Θ Ξ -> 
              (ValEnv Γ Δ₁ ⊛ ValEnv Γ Δ₂) Θ Ξ
separateEnv {[]} Δ₁ Δ₂ refl = tup ∅ ∅ (∅-lid ∅) refl refl
separateEnv {A ∷ Γ} (m₁ ∷ Δ₁) (m₂ ∷ Δ₂) (tup Ξ₁ Ξ₂ spΞ fst snd) with separateEnv {Γ} Δ₁ Δ₂ snd 
separateEnv {A ∷ Γ} {Θ = Θ} {Ξ = Ξ} (zero ∷ Δ₁) (m₂ ∷ Δ₂) (tup Ξ₁ Ξ₂ spΞ fst snd) | tup Ξ₁' Ξ₂' spΞ₂ θ₁ θ₂ = 
            tup Ξ₁' (Ξ₁ +ₘ Ξ₂') lemma (tup ∅ Ξ₁'   (∅-lid _) (mult-zero refl) θ₁)
                                             (tup Ξ₁ Ξ₂' refl      fst θ₂) 
  where
    open import Algebra.Solver.CommutativeMonoid (+ₘ-commutativeMonoid (length Θ)) 
                renaming (_⊕_ to _⊞_)

    lemma : Ξ₁' +ₘ (Ξ₁ +ₘ Ξ₂') ≡ Ξ
    lemma = 
      begin
        Ξ₁' +ₘ (Ξ₁ +ₘ Ξ₂')  
      ≡⟨ solve 3 (λ x y z -> x ⊞ (y ⊞ z) ⊜ y ⊞ (x ⊞ z)) refl Ξ₁' Ξ₁ Ξ₂' ⟩ 
        Ξ₁ +ₘ (Ξ₁' +ₘ Ξ₂')
      ≡⟨ cong (_ +ₘ_) spΞ₂ ⟩ 
        Ξ₁ +ₘ Ξ₂ 
      ≡⟨ spΞ ⟩ 
        Ξ
      ∎
     
            
separateEnv {A ∷ Γ} {Ξ = Ξ} (one ∷ Δ₁) (zero ∷ Δ₂) (tup Ξ₁ Ξ₂ spΞ fst snd) | tup Ξ₁' Ξ₂' spΞ₂ θ₁ θ₂ = 
  tup (Ξ₁ +ₘ Ξ₁') Ξ₂' lemma (tup Ξ₁ Ξ₁' refl fst θ₁)
                               (tup ∅   Ξ₂' (∅-lid _) (mult-zero refl) θ₂)
  where
    lemma : Ξ₁ +ₘ Ξ₁' +ₘ Ξ₂' ≡ Ξ
    lemma = 
      begin
        Ξ₁ +ₘ Ξ₁' +ₘ Ξ₂' 
      ≡⟨ +ₘ-assoc Ξ₁ Ξ₁' _ ⟩ 
        Ξ₁ +ₘ (Ξ₁' +ₘ Ξ₂')
      ≡⟨ cong (_ +ₘ_) spΞ₂ ⟩ 
        Ξ₁ +ₘ Ξ₂ 
      ≡⟨ spΞ ⟩ 
        Ξ
      ∎
separateEnv {A ∷ Γ} (one ∷ Δ₁) (one ∷ Δ₂) (tup .(∅) .(Ξ₁' +ₘ Ξ₂') refl (mult-omega v refl) snd) | tup Ξ₁' Ξ₂' refl θ₁ θ₂ = 
  tup Ξ₁' Ξ₂' (sym (∅-lid _)) (tup ∅ Ξ₁' (∅-lid _) (mult-one v) θ₁)
                                (tup ∅ Ξ₂' (∅-lid _) (mult-one v) θ₂)
separateEnv {A ∷ Γ} (one ∷ Δ₁) (omega ∷ Δ₂) (tup .(∅) .(Ξ₁' +ₘ Ξ₂') refl (mult-omega v refl) snd) | tup Ξ₁' Ξ₂' refl θ₁ θ₂ = 
  tup Ξ₁' Ξ₂' (sym (∅-lid _)) (tup ∅ Ξ₁' (∅-lid _) (mult-one v) θ₁)
                                (tup ∅ Ξ₂' (∅-lid _) (mult-omega v refl) θ₂)

separateEnv {A ∷ Γ} (omega ∷ Δ₁) (zero ∷ Δ₂) (tup .(∅) .(Ξ₁' +ₘ Ξ₂') refl (mult-omega v refl) snd) | tup Ξ₁' Ξ₂' refl θ₁ θ₂ = 
  tup Ξ₁' Ξ₂' (sym (∅-lid _)) (tup ∅ Ξ₁' (∅-lid _) (mult-omega v refl) θ₁)
                                (tup ∅ Ξ₂' (∅-lid _) (mult-zero refl) θ₂)

separateEnv {A ∷ Γ} (omega ∷ Δ₁) (one ∷ Δ₂) (tup .(∅) .(Ξ₁' +ₘ Ξ₂') refl (mult-omega v refl) snd) | tup Ξ₁' Ξ₂' refl θ₁ θ₂ =
   tup Ξ₁' Ξ₂' (sym (∅-lid _)) (tup ∅ Ξ₁' (∅-lid _) (mult-omega v refl) θ₁)
                                 (tup ∅ Ξ₂' (∅-lid _) (mult-one v) θ₂)

separateEnv {A ∷ Γ} (omega ∷ Δ₁) (omega ∷ Δ₂) (tup .(∅) .(Ξ₁' +ₘ Ξ₂') refl (mult-omega v refl) snd) | tup Ξ₁' Ξ₂' refl θ₁ θ₂ = 
  tup Ξ₁' Ξ₂' (sym (∅-lid _)) (tup ∅ Ξ₁' (∅-lid _) (mult-omega v refl) θ₁)
                                (tup ∅ Ξ₂' (∅-lid _) (mult-omega v refl) θ₂)

-- weakenΔ-valEnv : ∀ Γ {m Δ Θ Ξ} -> ValEnv Γ (m ×ₘ Δ) Θ Ξ -> ValEnv Γ Δ Θ Ξ
-- weakenΔ-valEnv [] θ = θ
-- weakenΔ-valEnv (A ∷ Γ) {one} {mₓ ∷ Δ} (tup Ξ₁ Ξ₂ refl fst snd) = tup Ξ₁ Ξ₂ refl fst (weakenΔ-valEnv Γ snd)
-- weakenΔ-valEnv (A ∷ Γ) {omega} {zero ∷ Δ} (tup Ξ₁ Ξ₂ refl fst snd) = tup Ξ₁ Ξ₂ refl fst (weakenΔ-valEnv Γ snd)
-- weakenΔ-valEnv (A ∷ Γ) {omega} {one ∷ Δ} (tup .(replicate zero) Ξ₂ refl (mult-omega v refl) snd) = tup ∅ Ξ₂ refl (mult-one v) (weakenΔ-valEnv Γ snd)
-- weakenΔ-valEnv (A ∷ Γ) {omega} {omega ∷ Δ} (tup Ξ₁ Ξ₂ refl fst snd) = tup Ξ₁ Ξ₂ refl fst (weakenΔ-valEnv Γ snd) 

weakenΔ-valEnv : ∀ Γ {m Δ Θ Ξ} -> ValEnv Γ (m ×ₘ Δ) Θ Ξ -> ∃[ Ξ' ] (ValEnv Γ Δ Θ Ξ' × m ×ₘ Ξ' ≡ Ξ)
weakenΔ-valEnv [] {m} θ = ∅ , refl , trans (×ₘ∅ m) (sym θ)
weakenΔ-valEnv (_ ∷ Γ) {Δ = mₓ ∷ Δ} (tup Ξ₁ Ξ₂ refl fst snd) with weakenΔ-valEnv Γ snd 
weakenΔ-valEnv (_ ∷ Γ) {one} {mₓ ∷ Δ} (tup Ξ₁ .(Data.Vec.map (λ y → y) Ξ') refl fst snd) | Ξ' , θ' , refl = Ξ₁ +ₘ Ξ' , tup Ξ₁ Ξ' refl fst θ' , lemma
  where
    open import Data.Vec.Properties using (map-id) 

    lemma : Data.Vec.map (λ x -> x) (Ξ₁ +ₘ Ξ') ≡ Ξ₁ +ₘ Data.Vec.map (λ x -> x) Ξ'
    lemma = begin
              Data.Vec.map (λ x -> x) (Ξ₁ +ₘ Ξ') 
            ≡⟨ map-id _ ⟩ 
              Ξ₁ +ₘ Ξ' 
            ≡⟨ cong (_ +ₘ_) (sym (map-id _)) ⟩ 
              Ξ₁ +ₘ Data.Vec.map (λ x -> x) Ξ'
            ∎
    
weakenΔ-valEnv (_ ∷ Γ) {omega} {zero ∷ Δ} (tup .(∅) .(Data.Vec.map (mul₀ omega) Ξ') refl (mult-zero refl) snd) | Ξ' , θ' , refl = Ξ' , tup ∅ Ξ' (∅-lid _) (mult-zero refl) θ' , sym (∅-lid _)
weakenΔ-valEnv (_ ∷ Γ) {omega} {one ∷ Δ} (tup .(∅) .(Data.Vec.map (mul₀ omega) Ξ') refl (mult-omega v refl) snd) | Ξ' , θ' , refl = Ξ' , tup ∅ Ξ' (∅-lid _) (mult-one v) θ' , sym (∅-lid _)
weakenΔ-valEnv (_ ∷ Γ) {omega} {omega ∷ Δ} (tup .(∅) .(Data.Vec.map (mul₀ omega) Ξ') refl (mult-omega v refl) snd) | Ξ' , θ' , refl = Ξ' , tup ∅ Ξ' (∅-lid _) (mult-omega v refl) θ' , sym (∅-lid _)


{- 
I don't know why but the following functions do not pass termination check, 
when --without-K is turning on. 
-} 


weakenΘ-value : 
  ∀ {Θ Ξ Θ' Ξ' A i} -> 
  compatΘ Θ Ξ Θ' Ξ' -> 
  Value Θ Ξ A {i} -> Value Θ' Ξ' A
weakenΘ-residual :  
  ∀ {Θ Ξ Θ' Ξ' A i} -> 
  compatΘ Θ Ξ Θ' Ξ' -> 
  Residual Θ Ξ A {i} -> Residual Θ' Ξ' A

weakenΘ-valEnv : 
  ∀ Γ {Δ Θ Ξ Θ' Ξ' i} -> 
  compatΘ Θ Ξ Θ' Ξ' -> 
  ValEnv Γ Δ {i} Θ Ξ -> ValEnv Γ Δ Θ' Ξ' 

weakenΘ-mult :
  ∀ {Θ Ξ Θ' Ξ' m A i} -> 
  compatΘ Θ Ξ Θ' Ξ' -> 
  mult (λ Θ Ξ -> Value Θ Ξ A {i}) m Θ  Ξ -> 
  mult (λ Θ Ξ -> Value Θ Ξ A) m Θ' Ξ' 

weakenΘ-value ext (clo {Γ' = Γ'} m refl ano θ t) = 
  case* compatΘ-split ext of λ { 
    (_ , _ , ext₁ , ext₂ , refl) -> 
      clo m refl (compatΘ-preserves-all-no-omega ext ano) 
                 (weakenΘ-valEnv Γ' ext₁ θ)
                 (weakenΘ-term ext₂ t) 
  }
--  with compatΘ-preserves-all-no-omega ext ano | compatΘ-split ext 
-- ... | ano' | _ , _ , ext₁ , ext₂ , refl = 
--   clo m refl ano' {!!} (weakenΘ-term ext₂ t)
--   clo m refl ano' (weakenΘ-valEnv Γ' ext₁ θ) (weakenΘ-term ext₂ t)
weakenΘ-value ext (unit refl) = 
  case* compatΘ-∅ ext of 
  λ { refl -> unit refl } 
-- with compatΘ-∅ ext 
-- ... | refl = unit refl
weakenΘ-value ext (pair refl ano v₁ v₂) = 
  case* compatΘ-split ext of λ {
   (_ , _ , ext₁ , ext₂ , refl) -> 
     pair refl (compatΘ-preserves-all-no-omega ext ano) 
            (weakenΘ-value ext₁ v₁) (weakenΘ-value ext₂ v₂)
  } 
weakenΘ-value ext (inl v) = inl (weakenΘ-value ext v)
weakenΘ-value ext (inr v) = inr (weakenΘ-value ext v)
weakenΘ-value ext (roll v) = roll (weakenΘ-value ext v)
weakenΘ-value ext (red x) = red (weakenΘ-residual ext x) 


weakenΘ-mult ext (mult-zero refl) = 
  case* compatΘ-∅ ext  of λ {
    refl -> mult-zero refl
  }
-- with compatΘ-∅ ext 
-- ... | refl = mult-zero refl
weakenΘ-mult ext (mult-one v) = mult-one (weakenΘ-value ext v)
weakenΘ-mult ext (mult-omega v refl) = 
  case* compatΘ-∅ ext of λ { 
    refl -> mult-omega (weakenΘ-value ext v) refl 
  }
-- with compatΘ-∅ ext 
-- ... | refl = mult-omega (weakenΘ-value ext v) refl 


weakenΘ-valEnv [] ext refl = 
  case* compatΘ-∅ ext of λ {
    refl -> refl
  } 
weakenΘ-valEnv (_ ∷ Γ) {_ ∷ Δ} ext (tup Ξ₁ Ξ₂ refl mv θ) = 
  case* compatΘ-split ext of λ { 
    (Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl) -> 
      tup Ξ₁' Ξ₂' refl (weakenΘ-mult ext₁ mv) (weakenΘ-valEnv Γ ext₂ θ)  
  }  
 
weakenΘ-residual ext unit● = 
  case* compatΘ-∅ ext of λ { 
    refl -> unit●
  }

weakenΘ-residual ext (letunit● ano r₁ r₂) = 
  case* compatΘ-split ext of λ {
    (_ , _ , ext₁ , ext₂ , refl) -> 
      letunit● (compatΘ-preserves-all-no-omega ext ano) 
               (weakenΘ-residual ext₁ r₁)
               (weakenΘ-residual ext₂ r₂)
  }

weakenΘ-residual ext (pair● ano r₁ r₂) = 
  case* compatΘ-split ext of λ {
    (_ , _ , ext₁ , ext₂ , refl) -> 
      pair● (compatΘ-preserves-all-no-omega ext ano) 
               (weakenΘ-residual ext₁ r₁)
               (weakenΘ-residual ext₂ r₂)
  }

weakenΘ-residual ext (letpair● ano r₁ r₂) = 
  case* compatΘ-split ext of λ {
    (_ , _ , ext₁ , ext₂ , refl) -> 
      letpair● (compatΘ-preserves-all-no-omega ext ano) 
               (weakenΘ-residual ext₁ r₁)
               (weakenΘ-residual (compat-skip (compat-skip ext₂)) r₂)
  }
  
weakenΘ-residual ext (inl● r) = inl● (weakenΘ-residual ext r)
weakenΘ-residual ext (inr● r) = inr● (weakenΘ-residual ext r)
weakenΘ-residual ext (case● {Γ₁ = Γ₁} {Γ₂} ano r refl ano₁ θ₁ t₁ θ₂ t₂ v) with compatΘ-split ext 
... | _ , _ , ext₁₂ , ext₃ , refl with compatΘ-split ext₁₂ 
... | _ , _ , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₃ 
... | _ , ext₃' , refl with compatΘ-split ext₂ 
... | _ , _ , extₑ , extₜ , refl = 
    case● (compatΘ-preserves-all-no-omega ext ano)
          (weakenΘ-residual ext₁ r)
          refl 
          (compatΘ-preserves-all-no-omega ext₂ ano₁)
          (weakenΘ-valEnv Γ₁ extₑ θ₁)
          (weakenΘ-term   (compat-skip extₜ) t₁) 
          (weakenΘ-valEnv Γ₂ extₑ θ₂)
          (weakenΘ-term   (compat-skip extₜ) t₂) 
          (weakenΘ-value  ext₃' v) 
  
weakenΘ-residual ext (var● x ok) = 
  case* compatΘ-preserves-varOk● ext ok of λ {
    (x' , ok') -> var● x' ok'
  }

weakenΘ-residual ext (pin ano r v) = 
  case* compatΘ-split ext of λ {
    (_ , _ , ext₁ , ext₂ , refl) -> 
       pin (compatΘ-preserves-all-no-omega ext ano)
           (weakenΘ-residual ext₁ r) 
           (weakenΘ-value ext₂ v)
  }





-- weakenΘ-valEnv []       ext refl with compatΘ-∅ ext 
-- ... | refl  = refl
-- weakenΘ-valEnv (x ∷ Γ) {m ∷ Δ} ext (tup Ξ₁ Ξ₂ refl mv θ) with compatΘ-split ext
-- weakenΘ-valEnv (x ∷ Γ) {_ ∷ Δ} ext (tup .∅ Ξ₂ refl (mult-zero refl) θ) | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-∅ ext₁ 
-- ... | refl = tup Ξ₁' Ξ₂' refl (mult-zero refl) (weakenΘ-valEnv Γ ext₂ θ) 
-- weakenΘ-valEnv (x ∷ Γ) {_ ∷ Δ} ext (tup Ξ₁ Ξ₂ refl (mult-one v) θ) | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl = tup Ξ₁' Ξ₂' refl (mult-one (weakenΘ-value ext₁ v)) (weakenΘ-valEnv Γ ext₂ θ)  
-- weakenΘ-valEnv (x ∷ Γ) {_ ∷ Δ} ext (tup .∅ Ξ₂ refl (mult-omega v refl) θ) | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-∅ ext₁ 
-- ... | refl = tup Ξ₁' Ξ₂' refl (mult-omega (weakenΘ-value ext₁ v) refl) (weakenΘ-valEnv Γ ext₂ θ) 


-- tup Ξ₁' Ξ₂' refl {!!} (weakenΘ-valEnv Γ ext₂ θ)  

-- weakenΘ-value : ∀ {Θ} {Ξ : MultEnv (length Θ)} {A B} Θ₀ -> 
--                   (eq : length Θ₀ + length Θ ≡ length (Θ₀ ++L Θ)) -> 
--                   (eq' : length Θ₀ + suc (length Θ) ≡ length (Θ₀ ++L B ∷ Θ)) -> 
--                   Value (Θ₀ ++L Θ) (subst MultEnv eq (∅ {length Θ₀} ++V Ξ)) A -> 
--                   Value (Θ₀ ++L B ∷ Θ) (subst MultEnv eq' (∅ ++V zero ∷ Ξ)) A
-- weakenΘ-red : ∀ {Θ} {Ξ : MultEnv (length Θ)} {A B} Θ₀ -> 
--                   (eq : length Θ₀ + length Θ ≡ length (Θ₀ ++L Θ)) -> 
--                   (eq' : length Θ₀ + suc (length Θ) ≡ length (Θ₀ ++L B ∷ Θ)) -> 
--                   Residual (Θ₀ ++L Θ) (subst MultEnv eq (∅ {length Θ₀} ++V Ξ)) A -> 
--                   Residual (Θ₀ ++L B ∷ Θ) (subst MultEnv eq' (∅ ++V zero ∷ Ξ)) A

-- weakenΘ-value Θ₀ eq eq' (clo m spΞ ano θ t) = {!!}
-- weakenΘ-value Θ₀ eq eq' (unit eq₁) = unit {!!}
-- weakenΘ-value Θ₀ eq eq' (pair spΞ ano v₁ v₂) = {!!}
-- weakenΘ-value Θ₀ eq eq' (inl v) = inl (weakenΘ-value Θ₀ eq eq' v)
-- weakenΘ-value Θ₀ eq eq' (inr v) = inr (weakenΘ-value Θ₀ eq eq' v)
-- weakenΘ-value Θ₀ eq eq' (roll v) = roll (weakenΘ-value Θ₀ eq eq' v)
-- weakenΘ-value Θ₀ eq eq' (red x) = red (weakenΘ-red Θ₀ eq eq' x) 

-- weakenΘ-valEnv : ∀ Γ {Δ Θ Ξ A} -> ValEnv Γ Δ Θ Ξ -> ValEnv Γ Δ (A ∷ Θ) (zero ∷ Ξ)
-- weakenΘ-valEnv [] θ = cong (_∷_ zero) θ
-- weakenΘ-valEnv (_ ∷ Γ) {m ∷ Δ} (tup Ξ₁ Ξ₂ spΞ fst snd) = 
--   {!tup Ξ₁ (!} 

-- all-no-omega-omega×ₘ : ∀ {n} (Δ : MultEnv n) -> all-no-omega (omega ×ₘ Δ) -> omega ×ₘ Δ ≡ Δ 
-- all-no-omega-omega×ₘ [] ano = refl
-- all-no-omega-omega×ₘ (zero ∷ Δ) (px ∷ ano) = cong (_∷_ zero) (all-no-omega-omega×ₘ Δ ano) 

-- multiply-value : 
--   ∀ {Θ m Ξ A} -> 
--   all-no-omega (m ×ₘ Ξ) -> Value Θ Ξ A -> Value Θ (m ×ₘ Ξ) A
-- multiply-value {Θ = Θ} {m = one} ano v = subst (λ x -> Value Θ x _) (sym (one×ₘ _)) v  
-- multiply-value {Θ = Θ} {omega} {Ξ} ano v with all-no-omega-omega×ₘ Ξ ano 
-- ... | eq  = subst (λ x -> Value Θ x _) (sym eq) v 

value-to-mult : 
  ∀ {Θ m Ξ A} -> 
  all-no-omega (m ×ₘ Ξ) -> Value Θ Ξ A -> mult (λ Θ' Ξ' -> Value Θ' Ξ' A) (M→M₀ m) Θ Ξ
value-to-mult {m = one} ano v = mult-one v
value-to-mult {m = omega} {Ξ} ano v with all-no-omega-omega×ₘ Ξ ano
... | refl = mult-omega v refl 

value-to-multM : 
  ∀ {Θ m Ξ A} -> 
  all-no-omega (m ×ₘ Ξ) -> Value Θ Ξ A -> mult (λ Θ' Ξ' -> Value Θ' Ξ' A) (M→M₀ m) Θ (m ×ₘ Ξ)
value-to-multM {Θ} {one} ano v = mult-one (subst (λ x -> Value Θ x _) (sym (one×ₘ _)) v )
value-to-multM {Θ} {omega} {Ξ} ano v with all-no-omega-omega×ₘ Ξ ano
... | refl = mult-omega v (×ₘ∅ _)


substV : ∀ {Θ Ξ Ξ' A} -> Ξ ≡ Ξ' -> Value Θ Ξ A -> Value Θ Ξ' A
substV refl v = v

substR : ∀ {Θ Ξ Ξ' A} -> Ξ ≡ Ξ' -> Residual Θ Ξ A -> Residual Θ Ξ' A
substR refl E = E

