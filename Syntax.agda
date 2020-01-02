{-# OPTIONS --without-K #-}

open import Data.Nat 
open import Data.List renaming (_++_ to _++L_ )
open import Data.Vec  renaming (_++_ to _++V_ ) 
open import Data.Fin hiding (_+_ ; _≤_ )
open import Data.Product
open import Data.Maybe

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Algebra 
open import Level renaming (zero to lzero ; suc to lsuc)

open import Function using () renaming (case_of_ to CASE_OF_) 

data Multiplicity : Set where 
  one   : Multiplicity 
  omega : Multiplicity

data Multiplicity₀ : Set where
  zero  : Multiplicity₀
  one   : Multiplicity₀
  omega : Multiplicity₀

M→M₀ : Multiplicity -> Multiplicity₀
M→M₀ one = one 
M→M₀ omega = omega 

TyCon : Set 
TyCon = ℕ 

data Ty : ℕ -> Set where 
  _⊕_    : ∀ {n} -> Ty n -> Ty n -> Ty n 
  tunit  : ∀ {n} -> Ty n 
  _⊗_   : ∀ {n} -> Ty n -> Ty n -> Ty n 
  Un     : ∀ {n} -> Multiplicity -> Ty n -> Ty n 
  _#_~>_ : ∀ {n} -> Ty n -> Multiplicity -> Ty n -> Ty n 
  _●     : ∀ {n} -> Ty n -> Ty n 
  μ_    : ∀ {n} -> Ty (suc n) -> Ty n 
  tvar   : ∀ {n} -> Fin n -> Ty n 

_⊸_ : ∀ {n} -> Ty n -> Ty n -> Ty n
t ⊸ t' = t # one ~> t' 

infixr 4 _⊗_ 
infixr 1 _⊕_ 
infixr 0 _#_~>_ 
infixr 0 _⊸_ 

tbool : Ty zero 
tbool = tunit ⊕ tunit 

module _ where 
  open import Data.Nat.Properties
  private 
    lemma : ∀ {m n} -> m ≤ n -> ∃[ k ] (k + m ≡ n)
    lemma {n = n} z≤n = n , +-identityʳ n
    lemma (s≤s r) with lemma r 
    ... | k , refl = k , +-suc k _ 

    weakenVarK : ∀ {m n k} -> k + m ≡ n -> Fin m -> Fin (k + m) 
    weakenVarK {k = 0F} refl  x = x
    weakenVarK {n = suc n} {suc k} eq x = suc (weakenVarK {n = n} {k = k} (suc-injective eq) x) 

  weakenVar : ∀ {m n} -> m ≤ n -> Fin m -> Fin n 
  weakenVar r x with lemma r 
  ... | k , r' = subst Fin r' (weakenVarK r' x)

  substTyVar : ∀ {m n k} -> m + n ≤ k -> Fin (m + suc n) -> Ty k -> Ty k
  substTyVar {0F} r 0F t = t
  substTyVar {0F} r (suc x) t = tvar (weakenVar r x)  
  substTyVar {suc m} {k = suc k} r 0F t = tvar zero 
  substTyVar {suc m} (s≤s r) (suc x) t = substTyVar {m} (≤-trans r (≤-step ≤-refl)) x t 

  weaken : ∀ {m n} -> m ≤ n -> Ty m -> Ty n 
  weaken r (t ⊕ t₁) = weaken r t ⊕ weaken r t₁
  weaken r tunit =  tunit 
  weaken r (t ⊗ t₁) = weaken r t ⊗ weaken r t₁
  weaken r (Un x t) = Un x (weaken r t)
  weaken r (t # x ~> t₁) = weaken r t # x ~> weaken r t₁
  weaken r (t ●) = weaken r t ●
  weaken r (μ t) = μ (weaken (s≤s r) t)
  weaken r (tvar x) = tvar (weakenVar r x)  

  substTyGen : ∀ {m n} -> Ty (m + suc n) -> Ty (m + n) -> Ty (m + n) 
  substTyGen (s₁ ⊕ s₂) t = substTyGen s₁ t ⊕ substTyGen s₂ t 
  substTyGen tunit t = tunit 
  substTyGen (s₁ ⊗ s₂) t = substTyGen s₁ t ⊗ substTyGen s₂ t 
  substTyGen (Un x s) t = Un x (substTyGen s t)
  substTyGen (s # x ~> s₁) t = substTyGen s t # x ~> substTyGen s₁ t
  substTyGen (s ●) t = (substTyGen s t) ●
  substTyGen {m} (μ s) t = μ (substTyGen {m = suc m} s (weaken (n≤1+n _) t))
  substTyGen (tvar x) t = substTyVar ≤-refl x t  

  substTy : ∀ {n} -> Ty (suc n) -> Ty n -> Ty n 
  substTy = substTyGen {zero}

module TyExamples where 
  nat : ∀ {n} -> Ty n
  nat = μ (tunit ⊕ tvar zero) 

  natlist : ∀ {n} -> Ty n 
  natlist = μ (tunit ⊕ (nat ⊗ tvar zero))

TyEnv : Set 
TyEnv = List (Ty zero) 

MultEnv : ∀ ℕ -> Set 
MultEnv n = Vec Multiplicity₀ n 

-- MultEnvL : ∀ ℕ -> Set 
-- MultEnvL n = Vec (Maybe MultiplicityL) n 

-- _×ₘ_ : Multiplicity -> Multiplicity -> Multiplicity
-- one ×ₘ   m = m 
-- omega ×ₘ m = omega 

mul₀ : Multiplicity₀ -> Multiplicity₀ -> Multiplicity₀
mul₀ zero y = zero
mul₀ one y = y 
mul₀ omega zero = zero
mul₀ omega one = omega
mul₀ omega omega = omega 

mul₀-m-zero : ∀ m -> mul₀ m zero ≡ zero 
mul₀-m-zero zero = refl
mul₀-m-zero one = refl
mul₀-m-zero omega = refl 

_×ₘ_ : ∀{n} -> Multiplicity -> MultEnv n -> MultEnv n
m ×ₘ Γ = Data.Vec.map (mul₀ (M→M₀ m)) Γ

-- _+ₑ_ : ∀ {n} -> MultEnv n -> MultEnv n -> MultEnv n 
-- [] +ₑ [] = []
-- (just _ ∷ Δ₁) +ₑ (just _  ∷ Δ₂) = just omega ∷ Δ₁ +ₑ Δ₂
-- (just x ∷ Δ₁) +ₑ (nothing ∷ Δ₂) = just x ∷ Δ₁ +ₑ Δ₂
-- (nothing ∷ Δ₁) +ₑ (x₁ ∷ Δ₂) = x₁ ∷ Δ₁ +ₑ Δ₂  

add₀ : Multiplicity₀ -> Multiplicity₀ -> Multiplicity₀
add₀ zero m = m 
add₀ one zero  = one 
add₀ one one   = omega
add₀ one omega = omega 
add₀ omega _   = omega 

add₀-m-zero : ∀ m -> add₀ m zero ≡ m 
add₀-m-zero zero = refl
add₀-m-zero one = refl
add₀-m-zero omega = refl 

add₀-comm : ∀ x y -> add₀ x y ≡ add₀ y x 
add₀-comm zero zero = refl
add₀-comm zero one = refl
add₀-comm zero omega = refl
add₀-comm one zero = refl
add₀-comm one one = refl
add₀-comm one omega = refl
add₀-comm omega zero = refl
add₀-comm omega one = refl
add₀-comm omega omega = refl 

add₀-assoc : ∀ x y z -> add₀ (add₀ x y) z ≡ add₀ x (add₀ y z)
add₀-assoc zero y z = refl
add₀-assoc one zero z = refl
add₀-assoc one one zero = refl
add₀-assoc one one one = refl
add₀-assoc one one omega = refl
add₀-assoc one omega z = refl
add₀-assoc omega y z = refl 

mul₀-dist-add₀ : ∀ x y z -> mul₀ x (add₀ y z) ≡ add₀ (mul₀ x y) (mul₀ x z)
mul₀-dist-add₀ zero y z = refl
mul₀-dist-add₀ one y z = refl
mul₀-dist-add₀ omega zero z = refl
mul₀-dist-add₀ omega one zero = refl
mul₀-dist-add₀ omega one one = refl
mul₀-dist-add₀ omega one omega = refl
mul₀-dist-add₀ omega omega z = refl 

infixr 7 _×ₘ_ 
infixl 6 _+ₘ_ 

_+ₘ_ : ∀ {n} -> MultEnv n -> MultEnv n -> MultEnv n 
[] +ₘ [] = [] 
(m₁ ∷ Δ₁) +ₘ (m₂ ∷ Δ₂) = add₀ m₁ m₂ ∷ (Δ₁ +ₘ Δ₂)

+ₘ-comm : ∀ {n} -> ∀ (Δ₁ Δ₂ : MultEnv n) -> Δ₁ +ₘ Δ₂ ≡ Δ₂ +ₘ Δ₁ 
+ₘ-comm [] [] = refl
+ₘ-comm (x₁ ∷ Δ₁) (x₂ ∷ Δ₂) = 
  begin
    add₀ x₁ x₂ ∷ Δ₁ +ₘ Δ₂
    ≡⟨ cong (_∷ Δ₁ +ₘ Δ₂) (add₀-comm x₁ x₂) ⟩ 
    add₀ x₂ x₁ ∷ Δ₁ +ₘ Δ₂ 
    ≡⟨ cong (add₀ x₂ x₁ ∷_) (+ₘ-comm Δ₁ Δ₂) ⟩ 
    add₀ x₂ x₁ ∷ Δ₂ +ₘ Δ₁
  ∎

+ₘ-assoc : ∀ {n} -> ∀ (Δ₁ Δ₂ Δ₃ : MultEnv n) -> 
           (Δ₁ +ₘ Δ₂) +ₘ Δ₃ ≡ Δ₁ +ₘ (Δ₂ +ₘ Δ₃)
+ₘ-assoc [] [] [] = refl 
+ₘ-assoc (x₁ ∷ Δ₁) (x₂ ∷ Δ₂) (x₃ ∷ Δ₃) = 
  begin  
   add₀ (add₀ x₁ x₂) x₃ ∷ Δ₁ +ₘ Δ₂ +ₘ Δ₃ 
   ≡⟨ cong₂ (_∷_) (add₀-assoc x₁ x₂ _) (+ₘ-assoc Δ₁ Δ₂ _) ⟩ 
   add₀ x₁ (add₀ x₂ x₃) ∷ Δ₁ +ₘ (Δ₂ +ₘ Δ₃)
  ∎

∅ : ∀ {n} -> MultEnv n 
∅ = Data.Vec.replicate zero 

∅-lid : ∀ {n} (Δ : MultEnv n) -> ∅ +ₘ Δ ≡ Δ
∅-lid [] = refl
∅-lid (x ∷ Δ) = cong (x ∷_) (∅-lid Δ)

∅-rid : ∀ {n} (Δ : MultEnv n) -> Δ +ₘ ∅ ≡ Δ 
∅-rid [] = refl 
∅-rid (x ∷ Δ) = cong₂ (_∷_) (add₀-m-zero x) (∅-rid Δ)  

+ₘ-commutativeMonoid : ∀ (n : ℕ) -> CommutativeMonoid 0ℓ 0ℓ 
+ₘ-commutativeMonoid n = record
                           { Carrier = MultEnv n
                           ; _≈_ = _≡_
                           ; _∙_ = _+ₘ_
                           ; ε = ∅
                           ; isCommutativeMonoid = record { 
                             isSemigroup = record { isMagma = record { isEquivalence =  Relation.Binary.PropositionalEquality.isEquivalence  ; 
                                                                       ∙-cong = cong₂ (_+ₘ_) } ; 
                                                    assoc = +ₘ-assoc } ; 
                             identityˡ = ∅-lid ; 
                             comm = +ₘ-comm }
                           } 


+ₘ-transpose : 
  ∀ {n} (Δ₁ Δ₂ Δ₃ Δ₄ : MultEnv n) -> 
  ((Δ₁ +ₘ Δ₂) +ₘ (Δ₃ +ₘ Δ₄)) ≡ ((Δ₁ +ₘ Δ₃) +ₘ (Δ₂ +ₘ Δ₄))
+ₘ-transpose Δ₁ Δ₂ Δ₃ Δ₄ = 
  begin
    (Δ₁ +ₘ Δ₂) +ₘ (Δ₃ +ₘ Δ₄)
  ≡⟨ +ₘ-assoc Δ₁ Δ₂ _ ⟩ 
    Δ₁ +ₘ (Δ₂ +ₘ (Δ₃ +ₘ Δ₄))
  ≡⟨ cong (Δ₁ +ₘ_) (+ₘ-comm Δ₂ _) ⟩ 
    (Δ₁ +ₘ ((Δ₃ +ₘ Δ₄) +ₘ Δ₂)) 
  ≡⟨ cong (Δ₁ +ₘ_) (+ₘ-assoc Δ₃ Δ₄ _) ⟩ 
    (Δ₁ +ₘ (Δ₃ +ₘ (Δ₄ +ₘ Δ₂)))
  ≡⟨ cong (Δ₁ +ₘ_) (cong (Δ₃ +ₘ_) (+ₘ-comm Δ₄ _)) ⟩ 
    (Δ₁ +ₘ (Δ₃ +ₘ (Δ₂ +ₘ Δ₄))) 
  ≡⟨ sym (+ₘ-assoc Δ₁ Δ₃ _) ⟩ 
    ((Δ₁ +ₘ Δ₃) +ₘ (Δ₂ +ₘ Δ₄)) 
  ∎


one×ₘ : ∀ {n} (Δ : MultEnv n) -> one ×ₘ Δ ≡ Δ
one×ₘ [] = refl
one×ₘ (x ∷ Δ) = cong (_∷_ x) (one×ₘ Δ) 

×ₘ∅ : ∀ {n} m -> m ×ₘ ∅ {n} ≡ ∅ {n}
×ₘ∅ {zero} m = refl
×ₘ∅ {suc n} one   = cong (_∷_ zero) (×ₘ∅ one)
×ₘ∅ {suc n} omega = cong (_∷_ zero) (×ₘ∅ omega)

module _ where
  open import Data.Vec.Properties 

  omega×ₘ∅-inv : ∀ {n} (Δ : MultEnv n) -> omega ×ₘ Δ ≡ ∅ -> Δ ≡ ∅ 
  omega×ₘ∅-inv [] eq = refl
  omega×ₘ∅-inv (x ∷ Δ) eq with  ∷-injective eq 
  omega×ₘ∅-inv (zero ∷ Δ) eq | eq₁ , eq₂ = cong (zero ∷_) (omega×ₘ∅-inv Δ eq₂) 

  add₀-0-0-inv : ∀ x y -> add₀ x y ≡ zero -> x ≡ zero × y ≡ zero 
  add₀-0-0-inv zero zero eq = refl , refl
  add₀-0-0-inv one zero ()
  add₀-0-0-inv one one ()
  add₀-0-0-inv one omega () 

  ∅+ₘ∅-inv : ∀ {n} (Δ₁ Δ₂ : MultEnv n) -> Δ₁ +ₘ Δ₂ ≡ ∅ -> Δ₁ ≡ ∅ × Δ₂ ≡ ∅ 
  ∅+ₘ∅-inv [] [] eq = refl , refl
  ∅+ₘ∅-inv (x₁ ∷ Δ₁) (x₂ ∷ Δ₂) eq with ∷-injective eq 
  ... | eq₁ , eq₂ with add₀-0-0-inv x₁ x₂ eq₁ | ∅+ₘ∅-inv Δ₁ Δ₂ eq₂ 
  ... | refl , refl | refl , refl = refl , refl 

×ₘ-dist : ∀ {n} m (Δ₁ Δ₂ : MultEnv n) -> 
          (m ×ₘ (Δ₁ +ₘ Δ₂)) ≡ (m ×ₘ Δ₁) +ₘ (m ×ₘ Δ₂)
×ₘ-dist m [] [] = refl
×ₘ-dist m (x₁ ∷ Δ₁) (x₂ ∷ Δ₂) = 
  cong₂ (_∷_) (mul₀-dist-add₀ (M→M₀ m) x₁ x₂) (×ₘ-dist m Δ₁ Δ₂) 

open import Data.Vec.Relation.Unary.All 

data no-omega : (m : Multiplicity₀) -> Set where
  zero : no-omega zero 
  one  : no-omega one 

no-omega-dist : ∀ x y -> no-omega (add₀ x y) -> no-omega x × no-omega y 
no-omega-dist zero y noω   = zero , noω
no-omega-dist one zero noω = one , zero 

all-zero : ∀ {n} -> Vec Multiplicity₀ n -> Set 
all-zero = All (λ x -> x ≡ zero) 

all-zero-∅ : ∀ {n} -> all-zero {n} ∅
all-zero-∅ {zero}  = []
all-zero-∅ {suc n} = refl ∷ all-zero-∅ {n} 
 
all-zero-∅-inv : ∀ {n} -> (Δ : MultEnv n) -> all-zero {n} Δ -> Δ ≡ ∅ 
all-zero-∅-inv .[] [] = refl
all-zero-∅-inv .(zero ∷ _) (refl ∷ az) = cong (_∷_ zero) (all-zero-∅-inv _ az) 

all-no-omega : ∀ {n} -> Vec Multiplicity₀ n -> Set 
all-no-omega = All no-omega 

all-no-omega-∅ : ∀ {n} -> all-no-omega (∅ {n})
all-no-omega-∅ {zero}  = []
all-no-omega-∅ {suc n} = zero ∷ all-no-omega-∅ 


all-no-omega-dist : ∀ {n} (Δ₁ Δ₂ : MultEnv n) -> all-no-omega (Δ₁ +ₘ Δ₂) -> 
                    all-no-omega Δ₁ × all-no-omega Δ₂
all-no-omega-dist [] [] ano = [] , []
all-no-omega-dist (x₁ ∷ Δ₁) (x₂ ∷ Δ₂) (noω ∷ ano) 
  with no-omega-dist x₁ x₂ noω | all-no-omega-dist Δ₁ Δ₂ ano
... | no₁ , no₂ | ano₁ , ano₂ = no₁ ∷ ano₁ , no₂ ∷ ano₂ 

×ₘ-split : ∀ {n} m (Δ : MultEnv n)  -> ∃[ Δ' ] (m ×ₘ Δ ≡ Δ +ₘ Δ' )
×ₘ-split m [] = [] , refl
×ₘ-split m (x ∷ Δ) with ×ₘ-split m Δ
×ₘ-split one (x ∷ Δ) | Δ' , eq = zero ∷ Δ' , cong₂ (_∷_) (sym (add₀-m-zero x)) eq
×ₘ-split omega (zero ∷ Δ) | Δ' , eq = zero ∷ Δ' , cong (_∷_ zero) eq
×ₘ-split omega (one ∷ Δ) | Δ' , eq = one ∷ Δ' , cong (_∷_ omega) eq
×ₘ-split omega (omega ∷ Δ) | Δ' , eq = one ∷ Δ' , cong (_∷_ omega) eq 


all-no-omega-dist-×ₘ : 
  ∀ {n} m (Δ : MultEnv n) -> 
  all-no-omega (m ×ₘ Δ) -> all-no-omega Δ
all-no-omega-dist-×ₘ m [] ano = []
all-no-omega-dist-×ₘ one (x ∷ Δ) (px ∷ ano) = px ∷ (all-no-omega-dist-×ₘ one Δ ano)
all-no-omega-dist-×ₘ omega (zero ∷ Δ) (px ∷ ano) = zero ∷ all-no-omega-dist-×ₘ omega Δ ano 

all-no-omega-weaken-right : 
  ∀ {n} {Δ₁ Δ₂ : MultEnv n} {m} -> 
  all-no-omega (Δ₁ +ₘ m ×ₘ Δ₂) -> all-no-omega (Δ₁ +ₘ Δ₂)
all-no-omega-weaken-right {Δ₁ = Δ₁} {Δ₂} {m} ano with ×ₘ-split m Δ₂ 
... | Δ' , eq with all-no-omega-dist (Δ₁ +ₘ Δ₂) Δ' (subst all-no-omega lemma ano) 
  where
    lemma : Δ₁ +ₘ m ×ₘ Δ₂ ≡ Δ₁ +ₘ Δ₂ +ₘ Δ'
    lemma = begin
              Δ₁ +ₘ m ×ₘ Δ₂
            ≡⟨ cong (Δ₁ +ₘ_) eq ⟩ 
              Δ₁ +ₘ (Δ₂ +ₘ Δ') 
            ≡⟨ sym (+ₘ-assoc Δ₁ Δ₂ _) ⟩ 
             Δ₁ +ₘ Δ₂ +ₘ Δ'
            ∎
... | ano₁ , _ = ano₁
  

all-no-omega-omega×ₘ : ∀ {n} (Δ : MultEnv n) -> all-no-omega (omega ×ₘ Δ) -> Δ ≡ ∅ 
all-no-omega-omega×ₘ [] ano = refl
all-no-omega-omega×ₘ (zero ∷ Δ) (px ∷ ano) = cong (_∷_ zero) (all-no-omega-omega×ₘ Δ ano) 

-- data _×ₑ_is_ : ∀ {n} -> Multiplicity -> MultEnvL n -> MultEnvL n -> Set where
--   one-×ₑ     : ∀ {n} {Ξ : MultEnvL n} -> one ×ₑ Ξ is Ξ
--   omega-×ₑ   : ∀ {n} {Ξ : MultEnvL n} -> All (λ x -> x ≡ nothing) Ξ -> omega ×ₑ Ξ is Ξ

-- _+L_ : ∀ {n} -> MultEnvL n -> MultEnvL n -> Maybe (MultEnvL n) 
-- [] +L [] = just []
-- (just x ∷ Ξ₁) +L (just x₁ ∷ Ξ₂) = nothing
-- (just x ∷ Ξ₁) +L (nothing ∷ Ξ₂) with Ξ₁ +L Ξ₂ 
-- ... | nothing = nothing 
-- ... | just Ξ = just (just x ∷ Ξ)
-- (nothing ∷ Ξ₁) +L (x₁ ∷ Ξ₂) with Ξ₁ +L Ξ₂ 
-- ... | nothing = nothing
-- ... | just Ξ = just (x₁ ∷ Ξ) 

-- replicate-nothing-is-all-nothing : ∀ {ℓ n A} -> All (λ x -> x ≡ nothing {ℓ} {A}) {n = n} (Data.Vec.replicate {ℓ} {n = n} nothing)
-- replicate-nothing-is-all-nothing {n = 0F}    = []
-- replicate-nothing-is-all-nothing {n = suc n} = refl ∷ replicate-nothing-is-all-nothing 

-- all-nothing-is-replicate-nothing : ∀ {ℓ n} {A : Set ℓ} {Ξ : Vec (Maybe A) n} -> All (λ x -> x ≡ nothing) Ξ -> Ξ ≡ Data.Vec.replicate nothing
-- all-nothing-is-replicate-nothing [] = refl
-- all-nothing-is-replicate-nothing (refl ∷ all-nothing-Ξ) with all-nothing-is-replicate-nothing all-nothing-Ξ 
-- ... | refl = refl 

-- _M×ₑ_is_ : ∀ {n} -> Maybe Multiplicity -> MultEnvL n -> MultEnvL n -> Set
-- just π M×ₑ Ξ is Ξ' = π ×ₑ Ξ is Ξ'
-- nothing M×ₑ Ξ is Ξ' = (Ξ ≡ Data.Vec.replicate nothing) × (Ξ' ≡ Data.Vec.replicate nothing)

-- data _+ₑ_is_ : ∀ {n} -> MultEnvL n -> MultEnvL n -> MultEnvL n -> Set where 
--   []+[]is[] : [] +ₑ [] is [] 
--   n+n-step  : ∀ {n} {Ξ₁ Ξ₂ Ξ : MultEnvL n} -> 
--               Ξ₁ +ₑ Ξ₂ is Ξ -> (nothing ∷ Ξ₁) +ₑ (nothing ∷ Ξ₂) is (nothing ∷ Ξ)
--   n+j-step  : ∀ {n} {Ξ₁ Ξ₂ Ξ : MultEnvL n} -> 
--               Ξ₁ +ₑ Ξ₂ is Ξ -> (nothing ∷ Ξ₁) +ₑ (just one ∷ Ξ₂) is (just one ∷ Ξ)
--   j+n-step  : ∀ {n} {Ξ₁ Ξ₂ Ξ : MultEnvL n} -> 
--               Ξ₁ +ₑ Ξ₂ is Ξ -> (just one ∷ Ξ₁) +ₑ (nothing ∷ Ξ₂) is (just one ∷ Ξ)

-- _+ₑ_is_ : ∀ {n} -> MultEnvL n -> MultEnvL n -> MultEnvL n -> Set
-- Ξ₁ +ₑ Ξ₂ is Ξ = Ξ₁ +L Ξ₂ ≡ just Ξ

-- infixl 6 _+ₑ_ 
-- infixl 6 _+L_ 
-- infixr 7 _×ₑ_ 

-- +L-comm : ∀ {n} (Ξ₁ Ξ₂ : MultEnvL n) -> 
--           Ξ₁ +L Ξ₂ ≡ Ξ₂ +L Ξ₁ 
-- +L-comm [] [] = refl
-- +L-comm (just x ∷ Ξ₁) (just x₁ ∷ Ξ₂) = refl
-- +L-comm (just x ∷ Ξ₁) (nothing ∷ Ξ₂) with Ξ₁ +L Ξ₂ | Ξ₂ +L Ξ₁ | +L-comm Ξ₁ Ξ₂  
-- +L-comm (just x ∷ Ξ₁) (nothing ∷ Ξ₂) | just x₁ | .(just x₁) | refl = refl
-- +L-comm (just x ∷ Ξ₁) (nothing ∷ Ξ₂) | nothing | .nothing | refl = refl
-- +L-comm (nothing ∷ Ξ₁) (just x ∷ Ξ₂) with Ξ₁ +L Ξ₂ | Ξ₂ +L Ξ₁ | +L-comm Ξ₁ Ξ₂  
-- +L-comm (nothing ∷ Ξ₁) (just x ∷ Ξ₂) | just x₁ | .(just x₁) | refl = refl
-- +L-comm (nothing ∷ Ξ₁) (just x ∷ Ξ₂) | nothing | .nothing | refl = refl
-- +L-comm (nothing ∷ Ξ₁) (nothing ∷ Ξ₂) with Ξ₁ +L Ξ₂ | Ξ₂ +L Ξ₁ | +L-comm Ξ₁ Ξ₂  
-- ... | _ | _ | refl = refl 

-- +ₑ-is-commutative : ∀ {n} {Ξ₁ Ξ₂ Ξ : MultEnvL n} -> 
--                     Ξ₁ +ₑ Ξ₂ is Ξ -> Ξ₂ +ₑ Ξ₁ is Ξ 
-- +ₑ-is-commutative {Ξ₁ = Ξ₁} eq = subst (λ x -> x ≡ just _) (+L-comm Ξ₁ _) eq
-- -- +ₑ-is-commutative []+[]is[] = []+[]is[]
-- -- +ₑ-is-commutative (n+n-step w) = n+n-step (+ₑ-is-commutative w)
-- -- +ₑ-is-commutative (n+j-step w) = j+n-step (+ₑ-is-commutative w)
-- -- +ₑ-is-commutative (j+n-step w) = n+j-step (+ₑ-is-commutative w) 




-- Ξ+ₑreplicate-nothing-is-Ξ : ∀ {n} (Ξ : MultEnvL n) -> Ξ +ₑ (Data.Vec.replicate nothing) is Ξ 
-- Ξ+ₑreplicate-nothing-is-Ξ [] = refl
-- Ξ+ₑreplicate-nothing-is-Ξ (just x ∷ Ξ) with Ξ +L Data.Vec.replicate nothing | Ξ+ₑreplicate-nothing-is-Ξ Ξ
-- ... | _ | refl = refl
-- Ξ+ₑreplicate-nothing-is-Ξ (nothing ∷ Ξ) with Ξ +L Data.Vec.replicate nothing | Ξ+ₑreplicate-nothing-is-Ξ Ξ
-- ... | _ | refl = refl 
-- -- Ξ+ₑreplicate-nothing-is-Ξ {0F} {[]} = []+[]is[]
-- -- Ξ+ₑreplicate-nothing-is-Ξ {suc n} {just one ∷ Ξ} = j+n-step Ξ+ₑreplicate-nothing-is-Ξ
-- -- Ξ+ₑreplicate-nothing-is-Ξ {suc n} {nothing ∷ Ξ}  = n+n-step Ξ+ₑreplicate-nothing-is-Ξ 

-- replicate-nothing+ₑΞ-is-Ξ : ∀ {n} (Ξ : MultEnvL n) -> Data.Vec.replicate nothing +ₑ Ξ is Ξ 
-- replicate-nothing+ₑΞ-is-Ξ Ξ = +ₑ-is-commutative {Ξ₁ = Ξ} (Ξ+ₑreplicate-nothing-is-Ξ Ξ)

-- +ₑ-partial-func : ∀ {n} {Ξ₁ Ξ₂ Ξ' Ξ''} -> 
--                   Ξ₁ +ₑ Ξ₂ is Ξ' -> Ξ₁ +ₑ Ξ₂ is Ξ' 

-- +ₑ-preserves-all-nothing : ∀ {n} {Ξ₁ Ξ₂ Ξ : MultEnvL n} -> 
--                            Ξ₁ +ₑ Ξ₂ is Ξ -> all-nothing Ξ₁ -> all-nothing Ξ₂ -> all-nothing Ξ
-- +ₑ-preserves-all-nothing {Ξ₁ = []} {[]} {[]} eq all₁ all₂ = []
-- +ₑ-preserves-all-nothing {Ξ₁ = .nothing ∷ Ξ₁} {.nothing ∷ Ξ₂} eq (refl ∷ all₁) (refl ∷ all₂) 
--   with Ξ₁ +L Ξ₂ | inspect (λ x -> x +L Ξ₂) Ξ₁
-- +ₑ-preserves-all-nothing {_} {.nothing ∷ Ξ₁} {.nothing ∷ Ξ₂} () (refl ∷ all₁) (refl ∷ all₂) | nothing | [ eq' ] 
-- +ₑ-preserves-all-nothing {_} {.nothing ∷ Ξ₁} {.nothing ∷ Ξ₂} refl (refl ∷ all₁) (refl ∷ all₂) | just Ξ | [ eq' ] = refl ∷ (+ₑ-preserves-all-nothing eq' all₁ all₂) 
-- -- +ₑ-preserves-all-nothing []+[]is[] all-nothing-Ξ₁ all-nothing-Ξ₂ = []
-- -- +ₑ-preserves-all-nothing (n+n-step Ξ₁+Ξ₂-is-Ξ) (px ∷ all-nothing-Ξ₁) (px₁ ∷ all-nothing-Ξ₂) =
-- --   refl ∷
-- --     +ₑ-preserves-all-nothing Ξ₁+Ξ₂-is-Ξ all-nothing-Ξ₁ all-nothing-Ξ₂
-- -- +ₑ-preserves-all-nothing (n+j-step Ξ₁+Ξ₂-is-Ξ) all-nothing-Ξ₁ (() ∷ all-nothing-Ξ₂)
-- -- +ₑ-preserves-all-nothing (j+n-step Ξ₁+Ξ₂-is-Ξ) (() ∷ all-nothing-Ξ₁) all-nothing-Ξ₂ 

data _∋_ : ∀ TyEnv  -> Ty zero -> Set where
  vz : ∀ {Γ : TyEnv} {a : Ty zero} -> (a ∷ Γ) ∋ a 
  vs : ∀ {Γ : TyEnv} {a b : Ty zero} -> Γ ∋ a -> (b ∷ Γ) ∋ a

data discardable : Multiplicity₀ -> Set where 
  omega : discardable omega
  zero  : discardable zero

omega×ₘ-discardable : ∀ {n} (Δ : MultEnv n) ->  All discardable (omega ×ₘ Δ) 
omega×ₘ-discardable [] = [] 
omega×ₘ-discardable (zero ∷ Δ)  = zero ∷ omega×ₘ-discardable Δ
omega×ₘ-discardable (one ∷ Δ)   = omega ∷ omega×ₘ-discardable Δ
omega×ₘ-discardable (omega ∷ Δ) = omega ∷ omega×ₘ-discardable Δ 

data usable : Multiplicity₀ -> Set where
  omega : usable omega
  one   : usable one 

data varOk : (Γ : TyEnv) {a : Ty zero} -> Γ ∋ a -> (Δ : MultEnv (length Γ)) -> Set where
  -- var-there-ω : ∀ {Γ : TyEnv} {a b} {x : Γ ∋ a} {Δ} -> varOk x Δ -> varOk (vs {b = b} x) (just omega ∷ Δ)
  -- var-there-0  : ∀ {Γ : TyEnv} {a b} {x : Γ ∋ a} {Δ} -> varOk x Δ -> varOk (vs {b = b} x) (nothing    ∷ Δ)
  there : 
    ∀ {Γ : TyEnv} {m a b} {x : Γ ∋ a} {Δ} -> 
    (d : discardable m) -> 
    (ok : varOk Γ x Δ) ->
    varOk (b ∷ Γ) (vs x) (m  ∷ Δ) 
  here    : 
    ∀ {Γ : TyEnv} {a} {Δ} {m} -> 
      (u : usable m) -> 
      (ad : All discardable Δ) -> 
      varOk (a ∷ Γ) vz (m ∷ Δ) 

data varOk● : (Θ : TyEnv) {a : Ty zero} -> Θ ∋ a -> (Ξ : MultEnv (length Θ)) -> Set where
  there :
    ∀ {Θ : TyEnv} {a b} {x : Θ ∋ a} {Ξ} -> 
    (ok : varOk● Θ x Ξ) ->
    varOk● (b ∷ Θ) (vs x) (zero ∷ Ξ) 
    
  here : 
    ∀ {Θ : TyEnv} {a} {Ξ} -> 
    (ad : all-zero Ξ) -> 
    varOk● (a ∷ Θ) vz (one ∷ Ξ) 


-- data varOk● : ∀ {Θ : TyEnv} {a} -> Θ ∋ a -> (Ξ : MultEnvL (length Θ)) -> Set where
--   var-there-0 : ∀ {Θ} {a b} {x : Θ ∋ a} {Ξ} -> varOk● x Ξ -> varOk● (vs {b = b} x) (nothing ∷ Ξ)
--   var-here    : ∀ {Θ} {a} {Ξ} -> all-nothing Ξ -> varOk● (vz {Γ = Θ} {a = a})  (just one ∷ Ξ)



data Term : ∀ (Γ : TyEnv) -> MultEnv (length Γ) -> (Θ : TyEnv) -> MultEnv (length Θ) -> Ty zero -> Set where 
  var  : 
    ∀ {Γ Δ Θ A} -> 
    (x : Γ ∋ A) -> (ok : varOk Γ x Δ) -> 
    Term Γ Δ Θ ∅ A 
  
  abs  : 
    ∀ {Γ Δ Θ Ξ A B} -> (m : Multiplicity) -> 
    Term (A ∷ Γ) (M→M₀ m ∷ Δ) Θ Ξ B -> 
    Term Γ Δ Θ Ξ (A # m ~> B)

  app : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B m} -> 
    Term Γ Δ₁ Θ Ξ₁ (A # m ~> B) -> 
    Term Γ Δ₂ Θ Ξ₂ A -> 
    Term Γ (Δ₁ +ₘ m ×ₘ Δ₂) Θ (Ξ₁ +ₘ m ×ₘ Ξ₂) B 

  unit : 
    ∀ {Γ Δ Θ} -> 
    (ad : All discardable Δ) -> 
    Term Γ Δ Θ ∅ tunit 

  letunit : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ A} -> 
    (m : Multiplicity) -> 
    Term Γ Δ₀ Θ Ξ₀ tunit ->
    Term Γ Δ  Θ Ξ  A -> 
    Term Γ (m ×ₘ Δ₀ +ₘ Δ) Θ (m ×ₘ Ξ₀ +ₘ Ξ) A

  pair : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
    Term Γ Δ₁ Θ Ξ₁ A -> 
    Term Γ Δ₂ Θ Ξ₂ B -> 
    Term Γ (Δ₁ +ₘ Δ₂) Θ (Ξ₁ +ₘ Ξ₂) (A ⊗ B) 

  letpair : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ A B C} -> 
    (m : Multiplicity) -> 
    Term Γ Δ₀ Θ Ξ₀ (A ⊗ B) -> 
    Term (A ∷ B ∷ Γ) (M→M₀ m ∷ M→M₀ m ∷ Δ) Θ Ξ C -> 
    Term Γ (m ×ₘ Δ₀ +ₘ Δ) Θ (m ×ₘ Ξ₀ +ₘ Ξ) C

  
  inl  : 
    ∀ {Γ Δ Θ Ξ} {A B} -> 
    Term Γ Δ Θ Ξ A -> 
    Term Γ Δ Θ Ξ (A ⊕ B) 

  inr : 
    ∀ {Γ Δ Θ Ξ} {A B} -> 
    Term Γ Δ Θ Ξ B -> 
    Term Γ Δ Θ Ξ (A ⊕ B) 

  case : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ A B C} -> 
    (m : Multiplicity) -> 
    Term Γ Δ₀ Θ Ξ₀ (A ⊕ B) ->
    Term (A ∷ Γ) (M→M₀ m ∷ Δ) Θ Ξ C -> 
    Term (B ∷ Γ) (M→M₀ m ∷ Δ) Θ Ξ C -> 
    Term Γ (m ×ₘ Δ₀ +ₘ Δ) Θ (m ×ₘ Ξ₀ +ₘ Ξ) C 

  roll : 
    ∀ {Γ Δ Θ Ξ F} -> 
    Term Γ Δ Θ Ξ (substTy F (μ F)) -> 
    Term Γ Δ Θ Ξ (μ F) 

  unroll :
    ∀ {Γ Δ Θ Ξ F} -> 
    Term Γ Δ Θ Ξ (μ F) -> 
    Term Γ Δ Θ Ξ (substTy F (μ F))

  unit● : 
    ∀ {Γ Δ Θ} -> 
    (ad : All discardable Δ) -> 
    Term Γ Δ Θ ∅ (tunit ●)

  letunit● : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ A} -> 
    (ano : all-no-omega (Ξ₀ +ₘ Ξ)) -> 
    Term Γ Δ₀ Θ Ξ₀ (tunit ●) ->
    Term Γ Δ  Θ Ξ  (A ●) -> 
    Term Γ (Δ₀ +ₘ Δ) Θ (Ξ₀ +ₘ Ξ) (A ●)

  pair● : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
    (ano : all-no-omega (Ξ₁ +ₘ Ξ₂)) -> 
    Term Γ Δ₁ Θ Ξ₁ (A ●) -> 
    Term Γ Δ₂ Θ Ξ₂ (B ●) -> 
    Term Γ (Δ₁ +ₘ Δ₂) Θ (Ξ₁ +ₘ Ξ₂) ((A ⊗ B) ●)

  letpair● : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ A B C} -> 
    (ano : all-no-omega (Ξ₀ +ₘ Ξ)) -> 
    Term Γ Δ₀ Θ Ξ₀ ((A ⊗ B) ●) -> 
    Term Γ Δ  (A ∷ B ∷ Θ) (one ∷ one ∷ Ξ) (C ●) -> 
    Term Γ (Δ₀ +ₘ Δ) Θ (Ξ₀ +ₘ Ξ) (C ●) 
  
  inl● : 
    ∀ {Γ Δ Θ Ξ} {A B} -> 
    Term Γ Δ Θ Ξ (A ●) -> 
    Term Γ Δ Θ Ξ ((A ⊕ B) ●)

  inr● : 
    ∀ {Γ Δ Θ Ξ} {A B} -> 
    Term Γ Δ Θ Ξ (B ●) -> 
    Term Γ Δ Θ Ξ ((A ⊕ B) ●)

  case● : 
    ∀ {Γ Δ₀ Δ Δ' Θ Ξ₀ Ξ Ξ' A B C} -> 
    (ano : all-no-omega (Ξ₀ +ₘ Ξ +ₘ omega ×ₘ Ξ')) -> 
    Term Γ Δ₀ Θ Ξ₀ ((A ⊕ B) ●) ->
    Term Γ Δ  (A ∷ Θ) (one ∷ Ξ) (C ●) -> 
    Term Γ Δ  (B ∷ Θ) (one ∷ Ξ) (C ●) -> 
    Term Γ Δ' Θ Ξ' (C # omega ~> tbool) -> 
    Term Γ (Δ₀ +ₘ Δ +ₘ omega ×ₘ Δ') Θ (Ξ₀ +ₘ Ξ +ₘ omega ×ₘ Ξ') (C ●)


  var● : ∀ {Γ Δ Θ Ξ A} -> 
         (x : Θ ∋ A) -> 
         (ad : All discardable Δ) -> varOk● Θ x Ξ ->
         Term Γ Δ Θ Ξ (A ●)

  pin : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
        (ano : all-no-omega (Ξ₁ +ₘ Ξ₂)) -> 
        Term Γ Δ₁ Θ Ξ₁ (A ●) ->          
        Term Γ Δ₂ Θ Ξ₂ (A # omega ~> B ●)  -> 
        Term Γ (Δ₁ +ₘ Δ₂) Θ (Ξ₁ +ₘ Ξ₂) (B ●)

  fwd : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
    (ano : all-no-omega (omega ×ₘ Ξ₁ +ₘ omega ×ₘ Ξ₂)) -> 
    Term Γ Δ₁ Θ Ξ₁ (A ● ⊸ B ●) -> 
    Term Γ Δ₂ Θ Ξ₂ A -> 
    Term Γ (omega ×ₘ Δ₁ +ₘ omega ×ₘ Δ₂) Θ (omega ×ₘ Ξ₁ +ₘ omega ×ₘ Ξ₂) B  

  bwd : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
    (ano : all-no-omega (omega ×ₘ Ξ₁ +ₘ omega ×ₘ Ξ₂)) -> 
    Term Γ Δ₁ Θ Ξ₁ (A ● ⊸ B ●) -> 
    Term Γ Δ₂ Θ Ξ₂ B -> 
    Term Γ (omega ×ₘ Δ₁ +ₘ omega ×ₘ Δ₂) Θ (omega ×ₘ Ξ₁ +ₘ omega ×ₘ Ξ₂) A

data extendΘ : (Θ : TyEnv)  (Ξ : MultEnv (length Θ)) 
                (Θ' : TyEnv) (Ξ' : MultEnv (length Θ')) -> Set where 
  ext-[] : 
    extendΘ [] [] [] [] 
     
  ext-here : 
    ∀ {Θ Ξ Θ' Ξ' A} -> 
    extendΘ Θ Ξ Θ' Ξ' -> 
    extendΘ Θ Ξ (A ∷ Θ') (zero ∷ Ξ')

  ext-there : 
    ∀ {Θ Ξ Θ' Ξ' A m } -> 
    extendΘ Θ Ξ Θ' Ξ' -> 
    extendΘ (A ∷ Θ) (m ∷ Ξ) (A ∷ Θ') (m ∷ Ξ')

ext-id : ∀ {Θ Ξ} ->  extendΘ Θ Ξ Θ Ξ
ext-id {[]} {[]}         = ext-[]
ext-id {_ ∷ Θ} {_ ∷ Ξ} = ext-there (ext-id {Θ} {Ξ})

extendΘ-∅ : ∀ {Θ Θ' Ξ'} -> extendΘ Θ ∅ Θ' Ξ' -> Ξ' ≡ ∅ 
extendΘ-∅ ext-[] = refl 
extendΘ-∅ (ext-here  ext) = cong (_∷_ zero) (extendΘ-∅ ext)
extendΘ-∅ (ext-there ext) = cong (_∷_ zero) (extendΘ-∅ ext) 

extendΘ-split : 
  ∀ {Θ Ξ₁ Ξ₂ Θ' Ξ'} -> 
  extendΘ Θ (Ξ₁ +ₘ Ξ₂) Θ' Ξ' -> 
    ∃ λ (Ξ₁' : MultEnv (length Θ')) -> ∃ λ (Ξ₂' : MultEnv (length Θ')) -> 
      extendΘ Θ Ξ₁ Θ' Ξ₁' × extendΘ Θ Ξ₂ Θ' Ξ₂' × Ξ₁' +ₘ Ξ₂' ≡ Ξ' 
extendΘ-split {[]} {[]} {[]} ext-[] = ∅ , ∅ , ext-[] , ext-[] , refl
extendΘ-split {[]} {[]} {[]} (ext-here ext) with extendΘ-split ext 
... | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl = zero ∷ Ξ₁' , zero ∷ Ξ₂' , ext-here ext₁ , ext-here ext₂ ,  refl
extendΘ-split {x ∷ Θ} {x₁ ∷ Ξ₁} {x₂ ∷ Ξ₂} (ext-here ext) with extendΘ-split {x ∷ Θ} {x₁ ∷ Ξ₁} {x₂ ∷ Ξ₂} ext
... | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl = zero ∷ Ξ₁' , zero ∷ Ξ₂' , ext-here ext₁ , ext-here ext₂ ,  refl  
extendΘ-split {x ∷ Θ} {x₁ ∷ Ξ₁} {x₂ ∷ Ξ₂} (ext-there ext) with extendΘ-split ext 
... | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl = x₁ ∷ Ξ₁' , x₂ ∷ Ξ₂' , ext-there ext₁ , ext-there ext₂ , refl 

extendΘ-preserves-all-no-omega : 
  ∀ {Θ Ξ Θ' Ξ'} -> 
  extendΘ Θ Ξ Θ' Ξ' -> all-no-omega Ξ -> all-no-omega Ξ' 
extendΘ-preserves-all-no-omega ext-[] ano = ano
extendΘ-preserves-all-no-omega (ext-here ext) ano = zero ∷ extendΘ-preserves-all-no-omega ext ano
extendΘ-preserves-all-no-omega (ext-there ext) (px ∷ ano) = px ∷ extendΘ-preserves-all-no-omega ext ano 

extendΘ-preserves-all-zero :
  ∀ {Θ Ξ Θ' Ξ'} -> 
  extendΘ Θ Ξ Θ' Ξ' -> all-zero Ξ -> all-zero Ξ' 
extendΘ-preserves-all-zero ext-[] az = az
extendΘ-preserves-all-zero (ext-here ext) az = refl ∷ extendΘ-preserves-all-zero ext az
extendΘ-preserves-all-zero (ext-there ext) (px ∷ az) = px ∷ extendΘ-preserves-all-zero ext az 

extendΘ-var : 
  ∀ { Θ Ξ Θ' Ξ' A } -> 
  extendΘ Θ Ξ Θ' Ξ' -> Θ ∋ A -> Θ' ∋ A 
extendΘ-var (ext-here ext) x = vs (extendΘ-var ext x)
extendΘ-var (ext-there ext) vz = vz
extendΘ-var (ext-there ext) (vs x) = vs (extendΘ-var ext x) 

extendΘ-preserves-varOk● : 
  ∀ {Θ Ξ Θ' Ξ' A} {x : Θ ∋ A} -> 
  extendΘ Θ Ξ Θ' Ξ' -> varOk● Θ x Ξ -> ∃ λ (x' : Θ' ∋ A) -> varOk● Θ' x' Ξ' 
extendΘ-preserves-varOk● {x = x} (ext-here ext) ok with extendΘ-preserves-varOk● ext ok 
... | x' , ok' = vs x' , there ok'
extendΘ-preserves-varOk● (ext-there ext) (there ok) with extendΘ-preserves-varOk● ext ok 
... | x' , ok' = vs x' , there ok'
extendΘ-preserves-varOk● (ext-there ext) (here ad) = vz , here (extendΘ-preserves-all-zero ext ad) 
 

extendΘ-×ₘ : 
  ∀ {Θ m Ξ Θ' Ξ'} -> 
  extendΘ Θ (m ×ₘ Ξ) Θ' Ξ' -> 
   ∃ λ (Ξ'' : MultEnv (length Θ')) -> 
     extendΘ Θ Ξ Θ' Ξ'' × m ×ₘ Ξ'' ≡ Ξ' 
extendΘ-×ₘ {[]} {m} {[]} ext-[] = [] , ext-[] , refl
extendΘ-×ₘ {[]} {m} {[]} (ext-here ext) with extendΘ-×ₘ {m = m} ext 
... | Ξ' , ext' , refl  = 
      zero ∷ Ξ' , ext-here ext' , cong (_∷ m ×ₘ Ξ') (mul₀-m-zero _) 
extendΘ-×ₘ {_ ∷ Θ} {m} {n ∷ Ξ} (ext-here ext) with extendΘ-×ₘ {m = m} ext 
... | Ξ' , ext' , refl  = 
      zero ∷ Ξ' , ext-here ext' , cong (_∷ m ×ₘ Ξ') (mul₀-m-zero _)  
extendΘ-×ₘ {_ ∷ Θ} {m} {n ∷ Ξ} (ext-there ext) with extendΘ-×ₘ {m = m} ext 
... | Ξ' , ext' , refl  = 
    n ∷ Ξ' , ext-there ext' , refl 


weakenΘ-term : ∀ {Γ Δ Θ Ξ Θ' Ξ' A} -> 
                  extendΘ Θ Ξ Θ' Ξ' -> 
                  Term Γ Δ Θ  Ξ A -> 
                  Term Γ Δ Θ' Ξ' A 
weakenΘ-term ext (var x ok) with extendΘ-∅ ext 
... | refl = var x ok
weakenΘ-term ext (abs m t) = abs m (weakenΘ-term ext t)
weakenΘ-term ext (app t₁ t₂) with extendΘ-split ext 
... | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl with extendΘ-×ₘ ext₂ 
... | Ξ₂'' , ext₂' , refl = app (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂' t₂) 
weakenΘ-term ext (unit ad) with extendΘ-∅ ext 
... | refl = unit ad
weakenΘ-term ext (letunit m t₁ t₂) with extendΘ-split ext 
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with extendΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = letunit m (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (pair t₁ t₂) with extendΘ-split ext 
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = pair (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂) 
weakenΘ-term ext (letpair m t₁ t₂) with extendΘ-split ext  
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with extendΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = letpair m (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (inl t) = inl (weakenΘ-term ext t)
weakenΘ-term ext (inr t) = inr (weakenΘ-term ext t)
weakenΘ-term ext (case m t₀ t₁ t₂) with extendΘ-split ext  
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with extendΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = case m (weakenΘ-term ext₁' t₀) (weakenΘ-term ext₂ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (roll t)   = roll (weakenΘ-term ext t)
weakenΘ-term ext (unroll t) = unroll (weakenΘ-term ext t)
weakenΘ-term ext (unit● ad) with extendΘ-∅ ext 
... | refl  = unit● ad
weakenΘ-term ext (letunit● ano t₁ t₂) 
  with extendΘ-preserves-all-no-omega ext ano | extendΘ-split ext
... | ano' | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = letunit● ano' (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (pair● ano t₁ t₂)
  with extendΘ-preserves-all-no-omega ext ano | extendΘ-split ext
... | ano' | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = pair● ano' (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (letpair● ano t₁ t₂) 
  with extendΘ-preserves-all-no-omega ext ano | extendΘ-split ext
... | ano' | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = letpair● ano' (weakenΘ-term ext₁ t₁) (weakenΘ-term (ext-there (ext-there ext₂)) t₂)
weakenΘ-term ext (inl● t) = inl● (weakenΘ-term ext t)
weakenΘ-term ext (inr● t) = inr● (weakenΘ-term ext t)
weakenΘ-term ext (case● ano t t₁ t₂ t₃) with extendΘ-preserves-all-no-omega ext ano 
... | ano' with extendΘ-split ext 
... | _ , _ , ext₁₂ , ext₃ , refl with extendΘ-split ext₁₂ 
... | _ , _ , ext₁ , ext₂ , refl with extendΘ-×ₘ ext₃ 
... | _ , ext₃' , refl = case● ano' (weakenΘ-term ext₁ t) (weakenΘ-term (ext-there ext₂) t₁) (weakenΘ-term (ext-there ext₂) t₂) (weakenΘ-term ext₃' t₃)
weakenΘ-term ext (var● x ad ok) with extendΘ-preserves-varOk● ext ok 
... | x' , ok' = var● x' ad ok'
weakenΘ-term ext (pin ano t₁ t₂) 
  with extendΘ-preserves-all-no-omega ext ano | extendΘ-split ext
... | ano' | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = pin ano' (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (fwd ano t₁ t₂) 
  with extendΘ-preserves-all-no-omega ext ano | extendΘ-split ext
... | ano' | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl 
  with extendΘ-×ₘ ext₁ | extendΘ-×ₘ ext₂ 
... | Ξ₁'' , ext₁' , refl | Ξ₂'' , ext₂' , refl = fwd ano' (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂' t₂) 
weakenΘ-term ext (bwd ano t₁ t₂) 
  with extendΘ-preserves-all-no-omega ext ano | extendΘ-split ext
... | ano' | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl   
  with extendΘ-×ₘ ext₁ | extendΘ-×ₘ ext₂ 
... | Ξ₁'' , ext₁' , refl | Ξ₂'' , ext₂' , refl = bwd ano' (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂' t₂)  
  

--   app  : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ σ π τ} -> 
--          ∀ {πΞ₂} -> π ×ₑ Ξ₂ is πΞ₂ -> 
--          ∀ {Ξ₁+πΞ₂} -> Ξ₁ +L πΞ₂ ≡ just Ξ₁+πΞ₂ -> 
--          Term Γ Δ₁ Θ Ξ₁ (σ # π ~> τ) ->          
--          Term Γ Δ₂ Θ Ξ₂ σ -> 
--          Term Γ (Δ₁ +ₑ π ×ₑ Δ₂) Θ Ξ₁+πΞ₂ τ

--   pair : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ σ τ} -> 
--          ∀ {Ξ₁+Ξ₂} -> Ξ₁ +L Ξ₂ ≡ just Ξ₁+Ξ₂ -> 
--          Term Γ Δ₁ Θ Ξ₁ σ -> 
--          Term Γ Δ₂ Θ Ξ₂ τ -> 
--          Term Γ (Δ₁ +ₑ Δ₂) Θ (Ξ₁+Ξ₂) (σ ⊗ τ) 

--   letpair : 
--          ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ σ τ τ'} -> (π : Multiplicity) -> 
--          ∀ {πΞ₀} {Ξ'} -> 
--          π ×ₑ Ξ₀ is πΞ₀ -> πΞ₀ +L Ξ ≡ just Ξ' -> 
--          Term Γ Δ₀ Θ Ξ₀ (σ ⊗ τ) -> 
--          Term (σ ∷ τ ∷ Γ) (just π ∷ just π ∷ Δ) Θ Ξ τ' -> 
--          Term Γ (π ×ₑ Δ₀ +ₑ Δ) Θ Ξ' τ' 
         
--   inl  : ∀ {Γ Δ Θ Ξ} {σ τ} -> 
--          Term Γ Δ Θ Ξ σ -> 
--          Term Γ Δ Θ Ξ (σ ⊕ τ) 

--   inr : ∀ {Γ Δ Θ Ξ} {σ τ} -> 
--          Term Γ Δ Θ Ξ τ -> 
--          Term Γ Δ Θ Ξ (σ ⊕ τ) 

--   case : ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ σ τ τ'} -> (π : Multiplicity) -> 
--          ∀ {πΞ₀} {Ξ'} -> 
--          π ×ₑ Ξ₀ is πΞ₀ -> πΞ₀ +L Ξ ≡ just Ξ' -> 
--          Term Γ Δ₀ Θ Ξ₀ (σ ⊕ τ) ->
--          Term (σ ∷ Γ) (just π ∷ Δ) Θ Ξ τ' -> 
--          Term (τ ∷ Γ) (just π ∷ Δ) Θ Ξ τ' -> 
--          Term Γ (π ×ₑ Δ₀ +ₑ Δ) Θ Ξ' τ' 

--   unit : ∀ {Γ Δ Θ Ξ} -> 
--          All discardable Δ -> 
--          all-nothing Ξ -> 
--          Term Γ Δ Θ Ξ tunit 

--   letunit : 
--           ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ τ} -> (π : Multiplicity) -> 
--           ∀ {πΞ₀} {Ξ'} -> 
--           π ×ₑ Ξ₀ is πΞ₀ -> πΞ₀ +L Ξ ≡ just Ξ' -> 
--           Term Γ Δ₀ Θ Ξ₀ tunit ->
--           Term Γ Δ Θ Ξ τ -> 
--           Term Γ (π ×ₑ Δ₀ +ₑ Δ) Θ Ξ' τ

--   roll : ∀ {Γ Δ Θ Ξ τ} -> 
--          Term Γ Δ Θ Ξ (substTy τ (μ τ)) -> 
--          Term Γ Δ Θ Ξ (μ τ) 

--   unroll : ∀ {Γ Δ Θ Ξ τ} -> 
--            Term Γ Δ Θ Ξ (μ τ) -> 
--            Term Γ Δ Θ Ξ (substTy τ (μ τ))
  

--   unit● : ∀ {Γ Δ Θ Ξ} -> 
--           All discardable Δ -> 
--           all-nothing Ξ -> 
--           Term Γ Δ Θ Ξ (tunit ●)

--   letunit● : 
--           ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ τ} -> 
--           ∀ {Ξ'} -> 
--           Ξ₀ +ₑ Ξ is Ξ' -> 
--           Term Γ Δ₀ Θ Ξ₀ (tunit ●) ->
--           Term Γ Δ Θ Ξ (τ ●)  -> 
--           Term Γ (Δ₀ +ₑ Δ) Θ Ξ' (τ ●)

--   pair● : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ σ τ} -> 
--          ∀ {Ξ₁+Ξ₂} -> Ξ₁ +ₑ Ξ₂ is Ξ₁+Ξ₂ -> 
--          Term Γ Δ₁ Θ Ξ₁ (σ ●) -> 
--          Term Γ Δ₂ Θ Ξ₂ (τ ●) -> 
--          Term Γ (Δ₁ +ₑ Δ₂) Θ (Ξ₁+Ξ₂) ((σ ⊗ τ) ●) 

--   letpair● : 
--          ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ σ τ τ'} -> 
--          ∀ {Ξ'} -> 
--          Ξ₀ +ₑ Ξ is Ξ' -> 
--          Term Γ Δ₀ Θ Ξ₀ ((σ ⊗ τ) ●) -> 
--          Term Γ Δ  (σ ∷ τ ∷ Θ) (just one ∷ just one ∷ Ξ) (τ' ●) -> 
--          Term Γ (Δ₀ +ₑ Δ) Θ Ξ' (τ' ●)

--   inl●  : ∀ {Γ Δ Θ Ξ} {σ τ} -> 
--          Term Γ Δ Θ Ξ (σ ●) -> 
--          Term Γ Δ Θ Ξ ((σ ⊕ τ) ●)

--   inr● : ∀ {Γ Δ Θ Ξ} {σ τ} -> 
--          Term Γ Δ Θ Ξ (τ ●) -> 
--          Term Γ Δ Θ Ξ ((σ ⊕ τ) ●)

--   case● : ∀ {Γ Δ₀ Δ Δ' Θ Ξ₀ Ξ Ξ' σ τ τ'} -> 
--          ∀ {Ξ''} -> 
--          Ξ₀ +ₑ Ξ is Ξ'' -> 
--          all-nothing Ξ' -> 
--          Term Γ Δ₀ Θ Ξ₀ ((σ ⊕ τ) ●) ->
--          Term Γ Δ  (σ ∷ Θ) (just one ∷ Ξ) (τ' ●) -> 
--          Term Γ Δ  (τ ∷ Θ) (just one ∷ Ξ) (τ' ●) -> 
--          Term Γ Δ' Θ Ξ' (τ # omega ~> tbool) -> 
--          Term Γ (Δ₀ +ₑ Δ +ₑ omega ×ₑ Δ') Θ Ξ'' (τ' ●)

--   var● : ∀ {Γ Δ Θ Ξ τ} -> 
--          (x : Θ ∋ τ) -> All discardable Δ -> varOk● x Ξ ->
--          Term Γ Δ Θ Ξ (τ ●)

--   pin : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ σ τ} -> 
--         ∀ {Ξ₁+Ξ₂} -> Ξ₁ +ₑ Ξ₂ is Ξ₁+Ξ₂ -> 
--         Term Γ Δ₁ Θ Ξ₁ (σ ●) ->          
--         Term Γ Δ₂ Θ Ξ₂ (σ # omega ~> τ ●)  -> 
--         Term Γ (Δ₁ +ₑ Δ₂) Θ Ξ₁+Ξ₂ (τ ●)

--   fwd : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ σ τ} -> 
--         all-nothing Ξ₁ -> 
--         all-nothing Ξ₂ -> 
--         Term Γ Δ₁ Θ Ξ₁ (σ ● ⊸ τ ●) -> 
--         Term Γ Δ₂ Θ Ξ₂ σ -> 
--         Term Γ (omega ×ₑ Δ₁ +ₑ omega ×ₑ Δ₂) Θ (Data.Vec.replicate nothing) τ 

--   bwd : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ σ τ} -> 
--         all-nothing Ξ₁ -> 
--         all-nothing Ξ₂ -> 
--         Term Γ Δ₁ Θ Ξ₁ (σ ● ⊸ τ ●) -> 
--         Term Γ Δ₂ Θ Ξ₂ τ -> 
--         Term Γ (omega ×ₑ Δ₁ +ₑ omega ×ₑ Δ₂) Θ (Data.Vec.replicate nothing) σ


-- module TermExamples where
--   open TyExamples
  
--   nil : Term [] [] [] [] natlist 
--   nil = roll (inl (unit [] [])) 

--   z : Term [] [] [] [] nat 
--   z = roll (inl (unit [] []))

--   id : ∀ {σ π} -> Term [] [] [] [] (σ # π ~> σ) 
--   id {π = π} = abs π (var vz (var-here []) [])

-- data Residual : (Θ : TyEnv) -> MultEnvL (length Θ) -> Ty 0F -> Set 

-- data Value : (Θ : TyEnv) -> (MultEnvL (length Θ)) -> Ty 0F -> Set where 
--   abs : ∀ {Θ Ξ σ τ} -> 
--         (π : Multiplicity) -> 
--         Term (σ ∷ []) (just π ∷ []) Θ Ξ τ -> 
--         Value Θ Ξ (σ # π ~> τ) 
  
--   unit : ∀ {Θ Ξ} -> all-nothing Ξ -> 
--          Value Θ Ξ tunit 

--   pair : ∀ {Θ Ξ₁ Ξ₂ σ τ} -> 
--          ∀ {Ξ} -> Ξ₁ +ₑ Ξ₂ is Ξ -> 
--          Value Θ Ξ₁ σ -> 
--          Value Θ Ξ₂ τ -> 
--          Value Θ Ξ (σ ⊗ τ) 

--   inl : ∀ {Θ Ξ σ τ} -> 
--         Value Θ Ξ σ -> 
--         Value Θ Ξ (σ ⊕ τ) 

--   inr : ∀ {Θ Ξ σ τ} -> 
--         Value Θ Ξ τ -> 
--         Value Θ Ξ (σ ⊕ τ) 

--   roll : ∀ {Θ Ξ τ} -> 
--          Value Θ Ξ (substTy τ (μ τ)) ->
--          Value Θ Ξ (μ τ) 

--   red : ∀ {Θ Ξ τ} -> 
--         Residual Θ Ξ (τ ●) -> Value Θ Ξ (τ ●) 

-- data Residual where
--   var● : ∀ {Θ Ξ τ} -> 
--          (x : Θ ∋ τ) -> varOk● x Ξ ->
--          Residual Θ Ξ (τ ●)

--   unit● : ∀ {Θ Ξ} -> 
--           all-nothing Ξ -> 
--           Residual Θ Ξ (tunit ●)

--   letunit● : 
--           ∀ {Θ Ξ₀ Ξ τ} -> 
--           ∀ {Ξ'} -> 
--           Ξ₀ +ₑ Ξ is Ξ' -> 
--           Residual Θ Ξ₀ (tunit ●) ->
--           Residual Θ Ξ (τ ●)  -> 
--           Residual Θ Ξ' (τ ●)
  
--   pair● : ∀ {Θ Ξ₁ Ξ₂ Ξ σ τ} -> 
--           Ξ₁ +ₑ Ξ₂ is Ξ -> 
--           Residual Θ Ξ₁ (σ ●) -> 
--           Residual Θ Ξ₂ (τ ●) -> 
--           Residual Θ Ξ  ((σ ⊗ τ) ●) 

--   letpair● : 
--          ∀ {Θ Ξ₀ Ξ σ τ τ'} -> 
--          ∀ {Ξ'} -> 
--          Ξ₀ +ₑ Ξ is Ξ' -> 
--          Residual Θ Ξ₀ ((σ ⊗ τ) ●) -> 
--          Residual (σ ∷ τ ∷ Θ) (just one ∷ just one ∷ Ξ) (τ' ●) -> 
--          Residual Θ Ξ' (τ' ●)

--   inl●  : ∀ {Θ Ξ} {σ τ} -> 
--          Residual Θ Ξ (σ ●) -> 
--          Residual Θ Ξ ((σ ⊕ τ) ●)

--   inr● : ∀ {Θ Ξ} {σ τ} -> 
--          Residual Θ Ξ (τ ●) -> 
--          Residual Θ Ξ ((σ ⊕ τ) ●)

--   case● : ∀ {Θ Ξ₀ Ξ Ξ' σ τ τ'} -> 
--          ∀ {Ξ''} -> 
--          Ξ₀ +ₑ Ξ is Ξ'' -> 
--          all-nothing Ξ' -> 
--          Residual Θ Ξ₀ ((σ ⊕ τ) ●) ->
--          Residual (σ ∷ Θ) (just one ∷ Ξ) (τ' ●) -> 
--          Residual (τ ∷ Θ) (just one ∷ Ξ) (τ' ●) -> 
--          Value Θ Ξ' (τ # omega ~> tbool) -> 
--          Residual Θ Ξ'' (τ' ●)

--   pin : ∀ {Θ Ξ₁ Ξ₂ σ τ} -> 
--         ∀ {Ξ₁+Ξ₂} -> Ξ₁ +ₑ Ξ₂ is Ξ₁+Ξ₂ -> 
--         Residual Θ Ξ₁ (σ ●) ->          
--         Residual Θ Ξ₂ (σ # omega ~> τ ●)  -> 
--         Residual Θ Ξ₁+Ξ₂ (τ ●)

-- value2term : ∀ {Θ Ξ τ} -> Value Θ Ξ τ -> Term [] [] Θ Ξ τ       
-- residual2term : ∀ {Θ Ξ τ} -> Residual Θ Ξ τ -> Term [] [] Θ Ξ τ 

-- value2term (abs π t) = abs π t
-- value2term (unit emp) = unit [] emp
-- value2term (pair disj v₁ v₂) = pair disj (value2term v₁) (value2term v₂)
-- value2term (inl v) = inl (value2term v)
-- value2term (inr v) = inr (value2term v)
-- value2term (roll v) = roll (value2term v)
-- value2term (red r) = residual2term r   
         
-- residual2term (var● x varOk) = var● x [] varOk
-- residual2term (unit● emp) = unit● [] emp
-- residual2term (letunit● disj r r₁) = letunit● disj (residual2term r) (residual2term r₁)
-- residual2term (pair● x r r₁) = pair● x (residual2term r) (residual2term r₁)
-- residual2term (letpair● x r r₁) = letpair● x (residual2term r) (residual2term r₁)
-- residual2term (inl● r) = inl● (residual2term r)
-- residual2term (inr● r) = inr● (residual2term r)
-- residual2term (case● disj emp r r₁ r₂ v₁) = case● disj emp (residual2term r) (residual2term r₁) (residual2term r₂) (value2term v₁)


