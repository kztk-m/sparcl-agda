{-# OPTIONS --without-K #-}

open import Data.Nat 
open import Data.List using (List ; [] ; _∷_ ; length) renaming (_++_ to _++L_ )
open import Data.Vec  using (Vec ; [] ; _∷_ ) renaming (_++_ to _++V_ ) 
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

-- Multiplicities with 0.
-- This is a deviation from the papers. Having 0 is convenient for handling uses of variables. 
data Multiplicity₀ : Set where
  zero  : Multiplicity₀
  one   : Multiplicity₀
  omega : Multiplicity₀

-- Embedding 
M→M₀ : Multiplicity -> Multiplicity₀
M→M₀ one   = one 
M→M₀ omega = omega 

-- Since it is cumbersome to handle type and value constructors, we handle them differently in 
-- this implementation. Superficially, we have (multiplicative) product and (additive) sum types, and
-- iso-recursive types. To express non-linear constructors, we prepare Many. 
data Ty : ℕ -> Set where 
  _⊕_    : ∀ {n} -> Ty n -> Ty n -> Ty n 
  tunit  : ∀ {n} -> Ty n 
  _⊗_   : ∀ {n} -> Ty n -> Ty n -> Ty n 
  Many   : ∀ {n} -> Multiplicity -> Ty n -> Ty n 
  _#_~>_ : ∀ {n} -> Ty n -> Multiplicity -> Ty n -> Ty n 
  _●     : ∀ {n} -> Ty n -> Ty n 
  μ_    : ∀ {n} -> Ty (suc n) -> Ty n 
  tvar   : ∀ {n} -> Fin n -> Ty n 
  _↔_    : ∀ {n} -> Ty n -> Ty n -> Ty n 

_⊸_ : ∀ {n} -> Ty n -> Ty n -> Ty n
t ⊸ t' = t # one ~> t' 

infixr 4 _⊗_ 
infixr 1 _⊕_ 
infixr 0 _#_~>_ 
infixr 0 _⊸_ 

tbool : Ty zero 
tbool = tunit ⊕ tunit 

module _ where 
  -- Several properties to handle recursive types. 
  open import Data.Nat.Properties
  private 
    lemma : ∀ {m n} -> m ≤ n -> ∃[ k ] (k + m ≡ n)
    lemma {n = n} z≤n = n , +-identityʳ n
    lemma (s≤s r) with lemma r 
    ... | k , refl = k , +-suc k _ 

    weakenVarK : ∀ {m n k} -> k + m ≡ n -> Fin m -> Fin (k + m) 
    weakenVarK {k = zero} refl  x = x
    weakenVarK {n = suc n} {suc k} eq x = suc (weakenVarK {n = n} {k = k} (suc-injective eq) x) 

  weakenVar : ∀ {m n} -> m ≤ n -> Fin m -> Fin n 
  weakenVar r x with lemma r 
  ... | k , r' = subst Fin r' (weakenVarK r' x)

  substTyVar : ∀ {m n k} -> m + n ≤ k -> Fin (m + suc n) -> Ty k -> Ty k
  substTyVar {zero} r zero t = t
  substTyVar {zero} r (suc x) t = tvar (weakenVar r x)  
  substTyVar {suc m} {k = suc k} r zero t = tvar zero 
  substTyVar {suc m} (s≤s r) (suc x) t = substTyVar {m} (≤-trans r (≤-step ≤-refl)) x t 

  weaken : ∀ {m n} -> m ≤ n -> Ty m -> Ty n 
  weaken r (t ⊕ t₁) = weaken r t ⊕ weaken r t₁
  weaken r tunit =  tunit 
  weaken r (t ⊗ t₁) = weaken r t ⊗ weaken r t₁
  weaken r (Many x t) = Many x (weaken r t)
  weaken r (t # x ~> t₁) = weaken r t # x ~> weaken r t₁
  weaken r (t ●) = weaken r t ●
  weaken r (μ t) = μ (weaken (s≤s r) t)
  weaken r (tvar x) = tvar (weakenVar r x)  
  weaken r (t₁ ↔ t₂) = weaken r t₁ ↔ weaken r t₂ 

  substTyGen : ∀ {m n} -> Ty (m + suc n) -> Ty (m + n) -> Ty (m + n) 
  substTyGen (s₁ ⊕ s₂) t = substTyGen s₁ t ⊕ substTyGen s₂ t 
  substTyGen tunit t = tunit 
  substTyGen (s₁ ⊗ s₂) t = substTyGen s₁ t ⊗ substTyGen s₂ t 
  substTyGen (Many x s) t = Many x (substTyGen s t)
  substTyGen (s # x ~> s₁) t = substTyGen s t # x ~> substTyGen s₁ t
  substTyGen (s ●) t = (substTyGen s t) ●
  substTyGen {m} (μ s) t = μ (substTyGen {m = suc m} s (weaken (n≤1+n _) t))
  substTyGen (tvar x) t = substTyVar ≤-refl x t
  substTyGen (s₁ ↔ s₂) t = substTyGen s₁ t ↔ substTyGen s₂ t 

  substTy : ∀ {n} -> Ty (suc n) -> Ty n -> Ty n 
  substTy = substTyGen {zero}

module TyExamples where 
  nat : ∀ {n} -> Ty n
  nat = μ (tunit ⊕ tvar zero) 

  natlist : ∀ {n} -> Ty n 
  natlist = μ (tunit ⊕ (nat ⊗ tvar zero))

{- 

Instead of handling an environment that maps variables to pairs of
types and multiplicities, we handle two sort of environments: one maps
variables to types and the other maps variables to multiplicities.

We will use de Bruijn indices for variables, and thus type
environments are represented as a list of types. The treatment of
multiplicity environment is similar but we assume that it has the same
length with the corresponding type environment; so we use Vec for
multiplicity environments.

-} 
TyEnv : Set 
TyEnv = List (Ty zero) 

MultEnv : ∀ ℕ -> Set 
MultEnv n = Vec Multiplicity₀ n 

-----------------------------------------------------------------------------
-- Operations and properties for multiplicities

mul : Multiplicity -> Multiplicity -> Multiplicity 
mul one   y = y 
mul omega y = omega 

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

-----------------------------------------------------------------------------
-- Operations and properties for multiplicity environments

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

-- The multiplicity environment that maps all variables into 0. 
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
                           ; isCommutativeMonoid = record { isMonoid = +ₘ-isMonoid ; comm = +ₘ-comm }
                             -- record { 
                             -- isSemigroup = record { isMagma = record { isEquivalence =  Relation.Binary.PropositionalEquality.isEquivalence  ; 
                             --                                           ∙-cong = cong₂ (_+ₘ_) } ; 
                             --                        assoc = +ₘ-assoc } ; 
                             -- ; identityˡ = ∅-lid 
                             -- ; comm = +ₘ-comm }
                           } 
  where 
    +ₘ-isMonoid : IsMonoid _≡_ _+ₘ_ ∅ 
    +ₘ-isMonoid = record { isSemigroup = record { isMagma = record { isEquivalence = Relation.Binary.PropositionalEquality.isEquivalence ; ∙-cong = cong₂ (_+ₘ_) } ; assoc = +ₘ-assoc } ; identity = ∅-lid , ∅-rid } 


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

omega×ₘm×ₘ-omega×ₘ : ∀ {n} (m : Multiplicity) (Δ : MultEnv n) -> omega ×ₘ m ×ₘ Δ ≡ omega ×ₘ Δ 
omega×ₘm×ₘ-omega×ₘ {zero}   m [] = refl 
omega×ₘm×ₘ-omega×ₘ {suc n} m (zero ∷ Δ) rewrite mul₀-m-zero (M→M₀ m) = cong (zero ∷_) (omega×ₘm×ₘ-omega×ₘ {n} m Δ)
omega×ₘm×ₘ-omega×ₘ {suc n} one (one ∷ Δ)   = cong (omega ∷_) (omega×ₘm×ₘ-omega×ₘ {n} one Δ)
omega×ₘm×ₘ-omega×ₘ {suc n} omega (one ∷ Δ) = cong (omega ∷_) (omega×ₘm×ₘ-omega×ₘ {n} omega Δ)
omega×ₘm×ₘ-omega×ₘ {suc n} one (omega ∷ Δ) = cong (omega ∷_) (omega×ₘm×ₘ-omega×ₘ {n} one Δ)
omega×ₘm×ₘ-omega×ₘ {suc n} omega (omega ∷ Δ) = cong (omega ∷_) (omega×ₘm×ₘ-omega×ₘ {n} omega Δ)

mul-×ₘ : ∀ {n} m₁ m₂ (Δ : MultEnv n)  -> mul m₁ m₂ ×ₘ Δ ≡ m₁ ×ₘ (m₂ ×ₘ Δ)
mul-×ₘ one m₂ Δ = sym (one×ₘ _)
mul-×ₘ omega m₂ Δ = sym (omega×ₘm×ₘ-omega×ₘ m₂ Δ)


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

×ₘ-split : ∀ {n} m (Δ : MultEnv n)  -> ∃[ Δ' ] (m ×ₘ Δ ≡ Δ +ₘ Δ' )
×ₘ-split m [] = [] , refl
×ₘ-split m (x ∷ Δ) with ×ₘ-split m Δ
×ₘ-split one (x ∷ Δ) | Δ' , eq = zero ∷ Δ' , cong₂ (_∷_) (sym (add₀-m-zero x)) eq
×ₘ-split omega (zero ∷ Δ) | Δ' , eq = zero ∷ Δ' , cong (_∷_ zero) eq
×ₘ-split omega (one ∷ Δ) | Δ' , eq = one ∷ Δ' , cong (_∷_ omega) eq
×ₘ-split omega (omega ∷ Δ) | Δ' , eq = one ∷ Δ' , cong (_∷_ omega) eq 

-----------------------------------------------------------------------------
-- Constraints on multiplicity environments

open import Data.Vec.Relation.Unary.All 

-- all-zero Δ essentially asserts that Δ is ∅ 
all-zero : ∀ {n} -> Vec Multiplicity₀ n -> Set 
all-zero = All (λ x -> x ≡ zero) 

all-zero-∅ : ∀ {n} -> all-zero {n} ∅
all-zero-∅ {zero}  = []
all-zero-∅ {suc n} = refl ∷ all-zero-∅ {n} 
 
all-zero-∅-inv : ∀ {n} -> (Δ : MultEnv n) -> all-zero {n} Δ -> Δ ≡ ∅ 
all-zero-∅-inv .[] [] = refl
all-zero-∅-inv .(zero ∷ _) (refl ∷ az) = cong (_∷_ zero) (all-zero-∅-inv _ az) 

data no-omega : (m : Multiplicity₀) -> Set where
  zero : no-omega zero 
  one  : no-omega one 

no-omega-dist : ∀ x y -> no-omega (add₀ x y) -> no-omega x × no-omega y 
no-omega-dist zero y noω   = zero , noω
no-omega-dist one zero noω = one , zero 

-- all-no-omega Δ asserts that Δ(x) cannot be omega. 
all-no-omega : ∀ {n} -> Vec Multiplicity₀ n -> Set 
all-no-omega = All no-omega 

-- Several properties of all-no-omega. 

all-no-omega-∅ : ∀ {n} -> all-no-omega (∅ {n})
all-no-omega-∅ {zero}  = []
all-no-omega-∅ {suc n} = zero ∷ all-no-omega-∅ 

all-no-omega-dist : ∀ {n} (Δ₁ Δ₂ : MultEnv n) -> all-no-omega (Δ₁ +ₘ Δ₂) -> 
                    all-no-omega Δ₁ × all-no-omega Δ₂
all-no-omega-dist [] [] ano = [] , []
all-no-omega-dist (x₁ ∷ Δ₁) (x₂ ∷ Δ₂) (noω ∷ ano) 
  with no-omega-dist x₁ x₂ noω | all-no-omega-dist Δ₁ Δ₂ ano
... | no₁ , no₂ | ano₁ , ano₂ = no₁ ∷ ano₁ , no₂ ∷ ano₂ 


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

-----------------------------------------------------------------------------

-- Variables, or de Bruijn indices
data _∋_ : ∀ TyEnv  -> Ty zero -> Set where
  vz : ∀ {Γ : TyEnv} {a : Ty zero} -> (a ∷ Γ) ∋ a 
  vs : ∀ {Γ : TyEnv} {a b : Ty zero} -> Γ ∋ a -> (b ∷ Γ) ∋ a

-- 'discardable' means that a corresponding variable need not be used. 
data discardable : Multiplicity₀ -> Set where 
  omega : discardable omega
  zero  : discardable zero

omega×ₘ-discardable : ∀ {n} (Δ : MultEnv n) ->  All discardable (omega ×ₘ Δ) 
omega×ₘ-discardable [] = [] 
omega×ₘ-discardable (zero ∷ Δ)  = zero ∷ omega×ₘ-discardable Δ
omega×ₘ-discardable (one ∷ Δ)   = omega ∷ omega×ₘ-discardable Δ
omega×ₘ-discardable (omega ∷ Δ) = omega ∷ omega×ₘ-discardable Δ 

-- 'usable' means that a corresponding variable can be used. 
data usable : Multiplicity₀ -> Set where
  omega : usable omega
  one   : usable one 

-- varOk means that the use of variable x in Γ is compatible with Δ; that is, 
-- x is usable in Δ and other variables must be discardable in Δ.
data varOk : (Γ : TyEnv) {a : Ty zero} -> Γ ∋ a -> (Δ : MultEnv (length Γ)) -> Set where
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

-- varOk● is similar to varOk but is for invertible variables. The definition is simplified as 
-- we assume Ξ cannot contain omega. 
data varOk● : (Θ : TyEnv) {a : Ty zero} -> Θ ∋ a -> (Ξ : MultEnv (length Θ)) -> Set where
  there :
    ∀ {Θ : TyEnv} {a b} {x : Θ ∋ a} {Ξ} -> 
    (ok : varOk● Θ x Ξ) ->
    varOk● (b ∷ Θ) (vs x) (zero ∷ Ξ) 
    
  here : 
    ∀ {Θ : TyEnv} {a} {Ξ} -> 
    (ad : all-zero Ξ) -> 
    varOk● (a ∷ Θ) vz (one ∷ Ξ) 

-- Now, we are ready to define the intrinsically-typed syntax of Sparcl. 
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

  many : 
    ∀ {Γ Δ Θ Ξ A} -> 
    (m : Multiplicity) -> 
    Term Γ Δ Θ Ξ A -> 
    Term Γ (m ×ₘ Δ) Θ (m ×ₘ Ξ) (Many m A) 

  unmany : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ m₀ A B} -> 
    (m : Multiplicity) -> 
    Term Γ Δ₀ Θ Ξ₀ (Many m₀ A) -> 
    Term (A ∷ Γ) (M→M₀ (mul m m₀) ∷ Δ) Θ Ξ B -> 
    Term Γ (m ×ₘ Δ₀ +ₘ Δ) Θ (m ×ₘ Ξ₀ +ₘ Ξ) B 
  
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
    Term Γ Δ₀ Θ Ξ₀ (tunit ●) ->
    Term Γ Δ  Θ Ξ  (A ●) -> 
    Term Γ (Δ₀ +ₘ Δ) Θ (Ξ₀ +ₘ Ξ) (A ●)

  pair● : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
    Term Γ Δ₁ Θ Ξ₁ (A ●) -> 
    Term Γ Δ₂ Θ Ξ₂ (B ●) -> 
    Term Γ (Δ₁ +ₘ Δ₂) Θ (Ξ₁ +ₘ Ξ₂) ((A ⊗ B) ●)

  letpair● : 
    ∀ {Γ Δ₀ Δ Θ Ξ₀ Ξ A B C} -> 
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
        Term Γ Δ₁ Θ Ξ₁ (A ●) ->          
        Term Γ Δ₂ Θ Ξ₂ (A # omega ~> B ●)  -> 
        Term Γ (Δ₁ +ₘ Δ₂) Θ (Ξ₁ +ₘ Ξ₂) ((A ⊗ B) ●)

  unlift : 
    ∀ {Γ Δ Θ Ξ A B}
    -> Term Γ Δ Θ Ξ (A ● ⊸ B ●) 
    -> Term Γ (omega ×ₘ Δ) Θ (omega ×ₘ Ξ) (A ↔ B) 

  fapp : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} 
    -> Term Γ Δ₁ Θ Ξ₁ (A ↔ B) 
    -> Term Γ Δ₂ Θ Ξ₂ A 
    -> Term Γ (Δ₁ +ₘ omega ×ₘ Δ₂) Θ (Ξ₁ +ₘ omega ×ₘ Ξ₂) B 

  bapp : 
    ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} 
    -> Term Γ Δ₁ Θ Ξ₁ (A ↔ B) 
    -> Term Γ Δ₂ Θ Ξ₂ B 
    -> Term Γ (Δ₁ +ₘ omega ×ₘ Δ₂) Θ (Ξ₁ +ₘ omega ×ₘ Ξ₂) A

-- fwd and bwd are obtained as derived constructs. 
fwd : 
  ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
  Term Γ Δ₁ Θ Ξ₁ (A ● ⊸ B ●) -> 
  Term Γ Δ₂ Θ Ξ₂ A -> 
  Term Γ (omega ×ₘ Δ₁ +ₘ omega ×ₘ Δ₂) Θ (omega ×ₘ Ξ₁ +ₘ omega ×ₘ Ξ₂) B  
fwd e1 e2 = fapp (unlift e1) e2

bwd : 
  ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ A B} -> 
  Term Γ Δ₁ Θ Ξ₁ (A ● ⊸ B ●) -> 
  Term Γ Δ₂ Θ Ξ₂ B -> 
  Term Γ (omega ×ₘ Δ₁ +ₘ omega ×ₘ Δ₂) Θ (omega ×ₘ Ξ₁ +ₘ omega ×ₘ Ξ₂) A
bwd e1 e2 = bapp (unlift e1) e2 


-- compatΘ Θ Ξ Θ' Ξ' asserts that environments ((Θ , Ξ) and (Θ' , Ξ'))
-- differ only in variables with multiplicity zero.

data compatΘ : (Θ : TyEnv)  (Ξ : MultEnv (length Θ)) 
                (Θ' : TyEnv) (Ξ' : MultEnv (length Θ')) -> Set where 
  compat-[] : 
    compatΘ [] [] [] [] 
     
  compat-ext-here : 
    ∀ {Θ Ξ Θ' Ξ' A} -> 
    compatΘ Θ Ξ Θ' Ξ' -> 
    compatΘ Θ Ξ (A ∷ Θ') (zero ∷ Ξ')

  compat-reduce-here : 
    ∀ {Θ Ξ Θ' Ξ' A} -> 
    compatΘ Θ Ξ Θ' Ξ' -> 
    compatΘ (A ∷ Θ) (zero ∷ Ξ) Θ' Ξ'


  compat-skip : 
    ∀ {Θ Ξ Θ' Ξ' A m } -> 
    compatΘ Θ Ξ Θ' Ξ' -> 
    compatΘ (A ∷ Θ) (m ∷ Ξ) (A ∷ Θ') (m ∷ Ξ')

  
-- Some useful examples of compatΘ

ext-id : ∀ {Θ Ξ} ->  compatΘ Θ Ξ Θ Ξ
ext-id {[]} {[]}         = compat-[]
ext-id {_ ∷ Θ} {_ ∷ Ξ} = compat-skip (ext-id {Θ} {Ξ})

smashΘ : ∀ {Θ} -> compatΘ Θ ∅ [] ∅ 
smashΘ {[]} = compat-[]
smashΘ {_ ∷ Θ} = compat-reduce-here smashΘ 

extendΘ : ∀ {Θ} -> compatΘ [] ∅ Θ ∅ 
extendΘ {[]} = compat-[]
extendΘ {_ ∷ Θ} = compat-ext-here extendΘ 

adjust∅Θ : ∀ {Θ Θ'} -> compatΘ Θ ∅ Θ' ∅ 
adjust∅Θ {[]} = extendΘ
adjust∅Θ {_ ∷ Θ} = compat-reduce-here adjust∅Θ 

-- Some properties on compatΘ

compatΘ-∅ : ∀ {Θ Θ' Ξ'} -> compatΘ Θ ∅ Θ' Ξ' -> Ξ' ≡ ∅ 
compatΘ-∅ compat-[] = refl 
compatΘ-∅ (compat-reduce-here ext) = compatΘ-∅ ext 
compatΘ-∅ (compat-ext-here  ext) = cong (_∷_ zero) (compatΘ-∅ ext)
compatΘ-∅ (compat-skip ext) = cong (_∷_ zero) (compatΘ-∅ ext) 

compatΘ-split : 
  ∀ {Θ Ξ₁ Ξ₂ Θ' Ξ'} -> 
  compatΘ Θ (Ξ₁ +ₘ Ξ₂) Θ' Ξ' -> 
    ∃ λ (Ξ₁' : MultEnv (length Θ')) -> ∃ λ (Ξ₂' : MultEnv (length Θ')) -> 
      compatΘ Θ Ξ₁ Θ' Ξ₁' × compatΘ Θ Ξ₂ Θ' Ξ₂' × Ξ₁' +ₘ Ξ₂' ≡ Ξ' 
compatΘ-split {[]} {[]} {[]} {.[]} {.[]} compat-[] = ∅ , ∅ , compat-[] , compat-[] , refl
compatΘ-split {[]} {[]} {[]} {.(_ ∷ _)} {.(zero ∷ _)} (compat-ext-here ext) 
  with compatΘ-split ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
   zero ∷ Ξ₁' , zero ∷ Ξ₂' , compat-ext-here ext₁ , compat-ext-here ext₂ , refl 
compatΘ-split {x ∷ Θ} {zero ∷ Ξ₁} {.zero ∷ Ξ₂} {[]} {[]} (compat-reduce-here ext) 
  with compatΘ-split ext 
... | [] ,  [] , ext₁ , ext₂ , eq  = 
  [] , [] , compat-reduce-here ext₁ , compat-reduce-here ext₂ , refl
compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {zero ∷ Ξ₂} {[]} {[]} ()
compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {one ∷ Ξ₂} {[]} {[]} ()
compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {omega ∷ Ξ₂} {[]} {[]} ()

compatΘ-split {x ∷ Θ} {zero ∷ Ξ₁} {x₂ ∷ Ξ₂} {x₃ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext)
  with compatΘ-split {x ∷ Θ} {zero ∷ Ξ₁} {x₂ ∷ Ξ₂}  ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
   zero ∷ Ξ₁' , zero ∷ Ξ₂' , compat-ext-here ext₁ , compat-ext-here ext₂ , refl 
compatΘ-split {x ∷ Θ} {zero ∷ Ξ₁} {.zero ∷ Ξ₂} {x₃ ∷ Θ'} {x₄ ∷ Ξ'} (compat-reduce-here ext) 
  with compatΘ-split ext
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , eq =
  Ξ₁' , Ξ₂' , compat-reduce-here ext₁ , compat-reduce-here ext₂ , eq
compatΘ-split {x ∷ Θ} {zero ∷ Ξ₁} {x₂ ∷ Ξ₂} {.x ∷ Θ'} {.x₂ ∷ Ξ'} (compat-skip ext) 
  with compatΘ-split ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
  zero ∷ Ξ₁' , x₂ ∷ Ξ₂' , compat-skip ext₁ , compat-skip ext₂ , refl

compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {zero ∷ Ξ₂} {x₃ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {zero ∷ Ξ₂}  ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
   zero ∷ Ξ₁' , zero ∷ Ξ₂' , compat-ext-here ext₁ , compat-ext-here ext₂ , refl 
compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {zero ∷ Ξ₂} {.x ∷ Θ'} {.one ∷ Ξ'} (compat-skip ext) 
  with compatΘ-split ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
  one ∷ Ξ₁' , zero ∷ Ξ₂' , compat-skip ext₁ , compat-skip ext₂ , refl

compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {one ∷ Ξ₂} {x₃ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext)
  with compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {one ∷ Ξ₂}  ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
   zero ∷ Ξ₁' , zero ∷ Ξ₂' , compat-ext-here ext₁ , compat-ext-here ext₂ , refl 
compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {one ∷ Ξ₂} {.x ∷ Θ'} {.omega ∷ Ξ'} (compat-skip ext) 
  with compatΘ-split ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
  one ∷ Ξ₁' , one ∷ Ξ₂' , compat-skip ext₁ , compat-skip ext₂ , refl

compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {omega ∷ Ξ₂} {x₃ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {omega ∷ Ξ₂}  ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
   zero ∷ Ξ₁' , zero ∷ Ξ₂' , compat-ext-here ext₁ , compat-ext-here ext₂ , refl 
compatΘ-split {x ∷ Θ} {one ∷ Ξ₁} {omega ∷ Ξ₂} {.x ∷ Θ'} {.omega ∷ Ξ'} (compat-skip ext) 
  with compatΘ-split ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
  one ∷ Ξ₁' , omega ∷ Ξ₂' , compat-skip ext₁ , compat-skip ext₂ , refl

compatΘ-split {x ∷ Θ} {omega ∷ Ξ₁} {x₂ ∷ Ξ₂} {x₃ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-split {x ∷ Θ} {omega ∷ Ξ₁} {x₂ ∷ Ξ₂}  ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
   zero ∷ Ξ₁' , zero ∷ Ξ₂' , compat-ext-here ext₁ , compat-ext-here ext₂ , refl 
compatΘ-split {x ∷ Θ} {omega ∷ Ξ₁} {x₂ ∷ Ξ₂} {.x ∷ Θ'} {.omega ∷ Ξ'} (compat-skip ext) 
  with compatΘ-split ext 
... | Ξ₁' ,  Ξ₂' , ext₁ , ext₂ , refl = 
  omega ∷ Ξ₁' , x₂ ∷ Ξ₂' , compat-skip ext₁ , compat-skip ext₂ , refl

compatΘ-preserves-all-no-omega : 
  ∀ {Θ Ξ Θ' Ξ'} -> 
  compatΘ Θ Ξ Θ' Ξ' -> all-no-omega Ξ -> all-no-omega Ξ' 
compatΘ-preserves-all-no-omega compat-[] ano = ano
compatΘ-preserves-all-no-omega (compat-ext-here ext) ano = zero ∷ compatΘ-preserves-all-no-omega ext ano
compatΘ-preserves-all-no-omega (compat-reduce-here ext) (px ∷ ano) = compatΘ-preserves-all-no-omega ext ano
compatΘ-preserves-all-no-omega (compat-skip ext) (px ∷ ano) = px ∷ compatΘ-preserves-all-no-omega ext ano 

compatΘ-preserves-all-zero :
  ∀ {Θ Ξ Θ' Ξ'} -> 
  compatΘ Θ Ξ Θ' Ξ' -> all-zero Ξ -> all-zero Ξ' 
compatΘ-preserves-all-zero compat-[] az = az
compatΘ-preserves-all-zero (compat-ext-here ext) az = refl ∷ compatΘ-preserves-all-zero ext az
compatΘ-preserves-all-zero (compat-reduce-here ext) (px ∷ az) = compatΘ-preserves-all-zero ext az
compatΘ-preserves-all-zero (compat-skip ext) (px ∷ az) = px ∷ compatΘ-preserves-all-zero ext az 

compatΘ-preserves-varOk● : 
  ∀ {Θ Ξ Θ' Ξ' A} {x : Θ ∋ A} -> 
  compatΘ Θ Ξ Θ' Ξ' -> varOk● Θ x Ξ -> ∃ λ (x' : Θ' ∋ A) -> varOk● Θ' x' Ξ' 
compatΘ-preserves-varOk● (compat-ext-here ext) ok with compatΘ-preserves-varOk● ext ok 
... | x' , ok'  =  vs x' , there ok'
compatΘ-preserves-varOk● (compat-reduce-here ext) (there ok) = compatΘ-preserves-varOk● ext ok
compatΘ-preserves-varOk● (compat-skip ext) (there ok) with compatΘ-preserves-varOk● ext ok 
... | x' , ok' = vs x' , there ok'
compatΘ-preserves-varOk● (compat-skip ext) (here ad) = vz , here (compatΘ-preserves-all-zero ext ad) 


compatΘ-×ₘ : 
  ∀ {Θ m Ξ Θ' Ξ'} -> 
  compatΘ Θ (m ×ₘ Ξ) Θ' Ξ' -> 
   ∃ λ (Ξ'' : MultEnv (length Θ')) -> 
     compatΘ Θ Ξ Θ' Ξ'' × m ×ₘ Ξ'' ≡ Ξ' 
compatΘ-×ₘ {[]} {m} {[]} {.[]} {.[]} compat-[] = [] , compat-[] , refl
compatΘ-×ₘ {[]} {m} {[]} {.(_ ∷ _)} {.(zero ∷ _)} (compat-ext-here ext) with compatΘ-×ₘ {[]} {m} {[]} ext
... | Ξ' , ext' , refl = zero ∷ Ξ' , compat-ext-here ext' , cong (_∷ m ×ₘ Ξ') (mul₀-m-zero _) 

compatΘ-×ₘ {_ ∷ Θ} {one} {.zero ∷ Ξ} {[]} {[]} (compat-reduce-here ext) with compatΘ-×ₘ ext 
... | [] , ext' , eq = [] , compat-reduce-here ext' , refl
compatΘ-×ₘ {_ ∷ Θ} {omega} {zero ∷ Ξ} {[]} {[]} (compat-reduce-here ext) with compatΘ-×ₘ ext 
... | [] , ext' , eq = [] , compat-reduce-here ext' , refl

compatΘ-×ₘ {_ ∷ Θ} {one} {n ∷ Ξ} {_ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-×ₘ ext 
... | Ξ'' , ext' , refl = zero ∷ Ξ'' , compat-ext-here ext' , refl
compatΘ-×ₘ {_ ∷ Θ} {one} {.zero ∷ Ξ} {_ ∷ Θ'} {n' ∷ Ξ'} (compat-reduce-here ext) 
  with compatΘ-×ₘ ext
... | Ξ'' , ext' , eq = Ξ'' , compat-reduce-here ext' , eq
compatΘ-×ₘ {_ ∷ Θ} {one} {n ∷ Ξ} {_ ∷ Θ'} {.n ∷ Ξ'} (compat-skip ext) 
  with compatΘ-×ₘ ext 
... | Ξ'' , ext' , refl = n ∷ Ξ'' , compat-skip ext' , refl

compatΘ-×ₘ {_ ∷ Θ} {omega} {zero ∷ Ξ} {_ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-×ₘ {m = omega} {zero ∷ Ξ} ext 
... | Ξ'' , ext' , refl = zero ∷ Ξ'' , compat-ext-here ext' , refl
compatΘ-×ₘ {_ ∷ Θ} {omega} {zero ∷ Ξ} {_ ∷ Θ'} {n' ∷ Ξ'} (compat-reduce-here ext) 
  with compatΘ-×ₘ ext 
... | Ξ'' , ext' , eq = Ξ'' , compat-reduce-here ext' , eq
compatΘ-×ₘ {_ ∷ Θ} {omega} {zero ∷ Ξ} {_ ∷ Θ'} {.zero ∷ Ξ'} (compat-skip ext) 
  with compatΘ-×ₘ ext 
... | Ξ'' , ext' , refl = zero ∷ Ξ'' , compat-skip ext' , refl

compatΘ-×ₘ {_ ∷ Θ} {omega} {one ∷ Ξ} {_ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-×ₘ {m = omega} {one ∷ Ξ} ext 
... | Ξ'' , ext' , refl = zero ∷ Ξ'' , compat-ext-here ext' , refl
compatΘ-×ₘ {_ ∷ Θ} {omega} {one ∷ Ξ} {_ ∷ Θ'} {.omega ∷ Ξ'} (compat-skip ext) 
  with compatΘ-×ₘ ext 
... | Ξ'' , ext' , refl = one ∷ Ξ'' , compat-skip ext' , refl

compatΘ-×ₘ {_ ∷ Θ} {omega} {omega ∷ Ξ} {_ ∷ Θ'} {.zero ∷ Ξ'} (compat-ext-here ext) 
  with compatΘ-×ₘ {m = omega} {omega ∷ Ξ} ext 
... | Ξ'' , ext' , refl = zero ∷ Ξ'' , compat-ext-here ext' , refl
compatΘ-×ₘ {_ ∷ Θ} {omega} {omega ∷ Ξ} {_ ∷ Θ'} {.omega ∷ Ξ'} (compat-skip ext) 
  with compatΘ-×ₘ ext 
... | Ξ'' , ext' , refl = omega ∷ Ξ'' , compat-skip ext' , refl


-- Well-typed terms can also be typed compatible environments. 
-- With a historical reason, this property is called 'weakenΘ-term' as 
-- `compatΘ` was initially used only for adding variables with multiplicity zero. 

weakenΘ-term : ∀ {Γ Δ Θ Ξ Θ' Ξ' A} -> 
                  compatΘ Θ Ξ Θ' Ξ' -> 
                  Term Γ Δ Θ  Ξ A -> 
                  Term Γ Δ Θ' Ξ' A 
weakenΘ-term ext (var x ok) with compatΘ-∅ ext 
... | refl = var x ok
weakenΘ-term ext (abs m t) = abs m (weakenΘ-term ext t)
weakenΘ-term ext (app t₁ t₂) with compatΘ-split ext 
... | Ξ₁' , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₂ 
... | Ξ₂'' , ext₂' , refl = app (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂' t₂) 
weakenΘ-term ext (unit ad) with compatΘ-∅ ext 
... | refl = unit ad
weakenΘ-term ext (letunit m t₁ t₂) with compatΘ-split ext 
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = letunit m (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (pair t₁ t₂) with compatΘ-split ext 
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = pair (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂) 
weakenΘ-term ext (letpair m t₁ t₂) with compatΘ-split ext  
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = letpair m (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂ t₂)

weakenΘ-term ext (many m t) with compatΘ-×ₘ ext 
... | Ξ'' , ext' , refl = many m (weakenΘ-term ext' t) 

weakenΘ-term ext (unmany m' t₁ t₂) with compatΘ-split ext  
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = unmany m' (weakenΘ-term ext₁' t₁) (weakenΘ-term ext₂ t₂) 

weakenΘ-term ext (inl t) = inl (weakenΘ-term ext t)
weakenΘ-term ext (inr t) = inr (weakenΘ-term ext t)
weakenΘ-term ext (case m t₀ t₁ t₂) with compatΘ-split ext  
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₁ 
... | Ξ₁'' , ext₁' , refl = case m (weakenΘ-term ext₁' t₀) (weakenΘ-term ext₂ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (roll t)   = roll (weakenΘ-term ext t)
weakenΘ-term ext (unroll t) = unroll (weakenΘ-term ext t)
weakenΘ-term ext (unit● ad) with compatΘ-∅ ext 
... | refl  = unit● ad
weakenΘ-term ext (letunit● t₁ t₂) 
  with compatΘ-split ext
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = letunit● (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (pair● t₁ t₂)
  with compatΘ-split ext
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = pair● (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (letpair● t₁ t₂) 
  with compatΘ-split ext
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = letpair● (weakenΘ-term ext₁ t₁) (weakenΘ-term (compat-skip (compat-skip ext₂)) t₂)
weakenΘ-term ext (inl● t) = inl● (weakenΘ-term ext t)
weakenΘ-term ext (inr● t) = inr● (weakenΘ-term ext t)
weakenΘ-term ext (case● t t₁ t₂ t₃) 
  with compatΘ-split ext 
... | _ , _ , ext₁₂ , ext₃ , refl with compatΘ-split ext₁₂ 
... | _ , _ , ext₁ , ext₂ , refl with compatΘ-×ₘ ext₃ 
... | _ , ext₃' , refl = case● (weakenΘ-term ext₁ t) (weakenΘ-term (compat-skip ext₂) t₁) (weakenΘ-term (compat-skip ext₂) t₂) (weakenΘ-term ext₃' t₃)
weakenΘ-term ext (var● x ad ok) with compatΘ-preserves-varOk● ext ok 
... | x' , ok' = var● x' ad ok'
weakenΘ-term ext (pin t₁ t₂) 
  with compatΘ-split ext
... | Ξ₁'  , Ξ₂' , ext₁ , ext₂ , refl = pin (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂ t₂)
weakenΘ-term ext (unlift t) =
  CASE compatΘ-×ₘ ext OF λ {
    (_ , ext' , refl) -> unlift (weakenΘ-term ext' t)
  }
weakenΘ-term ext (fapp t₁ t₂) =
  CASE compatΘ-split ext OF λ {
    (_ , _ , ext₁ , ext₂ , refl) -> CASE compatΘ-×ₘ ext₂ OF λ {
      (_ , ext₂' , refl) -> fapp (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂' t₂)
    }
  }
weakenΘ-term ext (bapp t₁ t₂) =
  CASE compatΘ-split ext OF λ {
    (_ , _ , ext₁ , ext₂ , refl) -> CASE compatΘ-×ₘ ext₂ OF λ {
      (_ , ext₂' , refl) -> bapp (weakenΘ-term ext₁ t₁) (weakenΘ-term ext₂' t₂)
    }
  }
  
