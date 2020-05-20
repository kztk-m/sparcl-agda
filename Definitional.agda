{-# OPTIONS --without-K #-}

-- Approx. 15-20 min are required to typecheck this file (for Agda 2.6.1) on
-- my MacBook 13-inch 2017 with 3.5 GHz Core i7 CPU and 16 GB memory. 
--
-- Since most of the time was spent for termination analysis, please
-- uncomment {-# TERMINATING #-} before evalR and eval to remove the 
-- termination checks.

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

open import Size 
open import Codata.Thunk


module Interpreter where 
  open import Codata.Delay renaming (length to dlength ; map to dmap )

  open import PInj
  open _⊢_⇔_

  -- A variant of the Delay monad in which the bind operator is
  -- frozen. While we cannot restrict levels in general, using Set is
  -- enough for enough for our purpose.

  data DELAY : (A : Set) -> (i : Size) -> Set₁ where 
    Now   : ∀ {A i} -> A -> DELAY A i 
    Later : ∀ {A i} -> Thunk (DELAY A) i -> DELAY A i 
    Bind  : ∀ {A B i} 
            -> (m : DELAY A i) -> (f : A -> DELAY B i) -> DELAY B i 

  Never : ∀ {A i} -> DELAY A i 
  Never = Later λ where .force -> Never 

  Dmap : ∀ {A B i} -> (A -> B) -> DELAY A i -> DELAY B i 
  Dmap f d = Bind d (λ x -> Now (f x)) 

  -- The function runD thaws the frozen operations.   
  runD : ∀ {A : Set} {i : Size} -> DELAY A i -> Delay A i 
  runD (Now x) = now x
  runD (Later x) = later λ where .force -> runD (force x)
  runD (Bind d f) = bind (runD d) (λ x -> runD (f x))

  -- The frozen version of _⊢_⇔_ 
  record _⊢F_⇔_ (i : Size) (A B : Set) : Set₁ where 
    field 
      Forward  : A -> DELAY B i 
      Backward : B -> DELAY A i 

  open _⊢F_⇔_ 

  forwardF  : ∀ {A B i} -> i ⊢F A ⇔ B -> A -> Delay B i 
  forwardF h a = runD (Forward h a) 

  backwardF : ∀ {A B i} -> i ⊢F A ⇔ B -> B -> Delay A i 
  backwardF h b = runD (Backward h b) 

  -- Similarly to runD, runD⇔ thawas the frozen operations in
  -- _⊢F_⇔_.
  runD⇔ : ∀ {A B i} -> i ⊢F A ⇔ B -> i ⊢ A ⇔ B
  forward  (runD⇔ f) = forwardF f 
  backward (runD⇔ f) = backwardF f 

  -- Environments handled by the forward and backward evaluations,
  -- which correponds to μ in the paper.
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

  -- An inverse of splitRValEnv. 
  mergeRValEnv : ∀ {Θ Ξ₁ Ξ₂} -> all-no-omega (Ξ₁ +ₘ Ξ₂) -> RValEnv Θ Ξ₁ -> RValEnv Θ Ξ₂ -> RValEnv Θ (Ξ₁ +ₘ Ξ₂)
  mergeRValEnv {.[]} {.[]} {.[]} _ [] [] = []
  mergeRValEnv {.(_ ∷ _)} {.(zero ∷ _)} {.(zero ∷ _)} (_ ∷ ano) (skip ρ₁) (skip ρ₂) = skip (mergeRValEnv ano ρ₁ ρ₂)
  mergeRValEnv {.(_ ∷ _)} {.(zero ∷ _)} {.(one ∷ _)} (_ ∷ ano) (skip ρ₁) (x ∷ ρ₂) = x ∷ (mergeRValEnv ano ρ₁ ρ₂)
  mergeRValEnv {.(_ ∷ _)} {.(one ∷ _)} {.(zero ∷ _)} (_ ∷ ano) (x ∷ ρ₁) (skip ρ₂) = x ∷ mergeRValEnv ano ρ₁ ρ₂
  mergeRValEnv {.(_ ∷ _)} {.(one ∷ _)} {.(one ∷ _)} (() ∷ ano) (x ∷ ρ₁) (x₁ ∷ ρ₂) 

  -- Construction of the empty value environment. 
  from-all-zero : ∀ {Θ Ξ} -> all-zero Ξ -> RValEnv Θ Ξ 
  from-all-zero {[]} {[]} [] = []
  from-all-zero {_ ∷ Θ} {.(zero ∷ _)} (refl ∷ az) = skip (from-all-zero az) 
  
  -- Value environments conforms to an empty invertible environment must be empty. 
  all-zero-canon : ∀ {Θ Ξ} -> (az : all-zero Ξ) -> (θ : RValEnv Θ Ξ) -> θ ≡ (from-all-zero az)
  all-zero-canon {[]} {[]} [] [] = refl
  all-zero-canon {_ ∷ Θ} {_ ∷ Ξ} (refl ∷ az) (skip θ) = cong skip (all-zero-canon az θ) 

  -- Looking-up function for RValEnv
  lkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> varOk● Θ x Ξ -> RValEnv Θ Ξ -> Value [] ∅ A 
  lkup (there ok) (skip ρ) = lkup ok ρ
  lkup (here ad) (x ∷ ρ) = x -- ad asserts ρ consists only of skip and []

  -- An inverse of lkup; the linearity matters here. 
  unlkup : ∀ {Θ A} {x : Θ ∋ A} {Ξ} -> varOk● Θ x Ξ -> Value [] ∅ A -> RValEnv Θ Ξ 
  unlkup (there ok) v = skip (unlkup ok v)
  unlkup (here ad) v = v ∷ from-all-zero ad 

  -- Some utility functions. 
  var●₀ : ∀ {A Θ} -> Residual (A ∷ Θ) (one ∷ ∅) (A ●) 
  var●₀ = var● vz (here all-zero-∅) 

  BindR : ∀ {i Θ Ξ A} {r : Set} -> DELAY (Value Θ Ξ (A ●)) i -> (Residual Θ Ξ (A ●) -> DELAY r i) -> DELAY r i 
  BindR x f = Bind x λ { (red r) -> f r } 
  

  -- For the do trick for the pattern matching 
  -- See https://github.com/agda/agda/issues/2298
  _>>=_ : ∀ {a b : Level} {A : Set a} {B : A -> Set b} -> ∀ (x : A) -> (∀ x -> B x) -> B x 
  x >>= f = f x 

  -- Function application. 
  apply : 
    ∀ {Θ Ξ₁ Ξ₂ A m B} i -> 
    all-no-omega (Ξ₁ +ₘ m ×ₘ Ξ₂) -> 
    Value Θ Ξ₁ (A # m ~> B) -> Value Θ Ξ₂ A -> DELAY (Value Θ (Ξ₁ +ₘ m ×ₘ Ξ₂) B) i 

  -- Forward, backward and unidirectional evalautions are given as
  -- mutually recursive functions. Notice that, the existence of these
  -- functions essentially proves the type safety (i.e., the
  -- preservation and progree prperty). Thus, in a sense, they are
  -- generalizations of Lemma 3.1 and Lemma 3.2 in the paper.

  -- Forward and backward evaluation. 
  -- {-# TERMINATING #-} 
  evalR :
    ∀ {Θ Ξ A} i -> 
    all-no-omega Ξ -> Residual Θ Ξ (A ●) -> i ⊢F (RValEnv Θ Ξ) ⇔ Value [] ∅ A 

  -- Unidirectional evaluation. Also, an important thing is that this function keeps 
  -- the invariant all-no-omega (Ξₑ +ₘ Ξ) for recursive calls, which essentially supports 
  -- the claim in Section 3.4: "This assumption is actually an invariant in our system ...".

  -- {-# TERMINATING #-} 
  eval : 
    ∀ {Θ Ξₑ Γ Δ Ξ A} i -> 
    all-no-omega (Ξₑ +ₘ Ξ) -> ValEnv Γ Δ Θ Ξₑ -> Term Γ Δ Θ Ξ A -> DELAY (Value Θ (Ξₑ +ₘ Ξ) A) i 

  apply {Θ} {Ξ₁} {Ξ₂} i ano (clo {Ξ' = Ξ'} {Ξₜ = Ξₜ} m refl θ t) v with all-no-omega-dist _ _ ano
  ... | ano-'t , ano-m2 = Later λ { .force {j} -> 
        let T = eval j (subst all-no-omega lemma ano) (tup _ _ refl (value-to-multM ano-m2 v) θ) t
        in subst (λ x -> DELAY (Value Θ x _) j) (sym lemma) T  
      }
    where
      lemma : Ξ' +ₘ Ξₜ +ₘ m ×ₘ Ξ₂ ≡ m ×ₘ Ξ₂ +ₘ Ξ' +ₘ Ξₜ 
      lemma = trans (+ₘ-comm _ _)
                    (sym (+ₘ-assoc (m ×ₘ Ξ₂) Ξ' _))


  -- evalR is defined so that evalR ∞ ano r actually defines a
  -- bijection. See Invertiblity.agda for its proof.
  
  Forward  (evalR i ano unit●) _ = Now (unit refl)
  Backward (evalR i ano unit●) _ = Now emptyRValEnv

  Forward  (evalR i ano (letunit● r₁ r₂)) ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    ρ₁ , ρ₂ <- splitRValEnv ρ 
    Bind (Forward (evalR i ano₁ r₁) ρ₁) λ { (unit eq) -> Forward (evalR i ano₂ r₂) ρ₂ } 
  Backward (evalR i ano (letunit● r₁ r₂)) v = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    Bind (Backward (evalR i ano₂ r₂) v) λ ρ₂ -> 
     Bind (Backward (evalR i ano₁ r₁) (unit refl)) λ ρ₁ -> 
      Now (mergeRValEnv ano ρ₁ ρ₂) 
   
  Forward  (evalR i ano (pair● r₁ r₂)) ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    ρ₁  , ρ₂  <- splitRValEnv ρ
    Bind (Forward (evalR i ano₁ r₁) ρ₁) λ v₁ -> 
     Bind (Forward (evalR i ano₂ r₂) ρ₂) λ v₂ -> 
      Now (pair refl v₁ v₂)
      
  Backward (evalR i ano (pair● {A = A} {B} r₁ r₂)) (pair {Ξ₁ = []} {[]} spΞ v₁ v₂) = do
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    Bind (Backward (evalR i ano₁ r₁) v₁) λ ρ₁ -> 
     Bind (Backward (evalR i ano₂ r₂) v₂) λ ρ₂ -> 
      Now (mergeRValEnv ano ρ₁ ρ₂)

  Forward (evalR i ano (letpair● r₁ r₂)) ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    ρ₁  , ρ₂  <- splitRValEnv ρ
    Bind (Forward (evalR i ano₁ r₁) ρ₁) λ { 
      (pair {Ξ₁ = []} {[]} spΞ v₁ v₂ ) -> 
        Forward (evalR i (one ∷ one ∷ ano₂) r₂) (v₁ ∷ v₂ ∷ ρ₂)
     }
  
  Backward (evalR i ano (letpair● r₁ r₂)) v = do 
    ano₁ , ano₂ <-  all-no-omega-dist _ _ ano 
    Bind (Backward (evalR i (one ∷ one ∷ ano₂) r₂) v) λ { (v₁ ∷ v₂ ∷ ρ₂) -> 
      Bind (Backward (evalR i ano₁ r₁) (pair refl v₁ v₂)) λ ρ₁ -> 
       Now (mergeRValEnv ano ρ₁ ρ₂)
     }
  
  Forward (evalR i ano (inl● r)) ρ = Bind (Forward (evalR i ano r) ρ) λ x -> Now (inl x)
  Backward (evalR i ano (inl● r)) v = 
    CASE v OF λ {
      (inl v₁) -> Backward (evalR i ano r) v₁ ; 
      (inr v₂) -> Never 
    }
  
  Forward  (evalR i ano (inr● r)) ρ = Bind (Forward (evalR i ano r) ρ) λ x -> Now (inr x)
  Backward (evalR i ano (inr● r)) v = 
    CASE v OF λ { 
      (inl v₁) -> Never ; 
      (inr v₂) -> Backward (evalR i ano r) v₂
    }
  
  Forward  (evalR i ano (case● {Γ₁ = Γ₁} {Γ₂} r refl θ₁ t₁ θ₂ t₂ f)) ρ = do 
    ano₀ , ano- <- all-no-omega-dist _ _ ano
    ρ₀  , ρ-  <- splitRValEnv ρ 
    Bind (Forward (evalR i ano₀ r) ρ₀) λ {
          (inl v₁) -> 
            Bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₁ (compat-ext-here ext-id) θ₁) t₁) λ { (red r₁) -> 
              Later λ { .force {j} -> 
                Bind (Forward (evalR j (one ∷ ano-) r₁) (v₁ ∷ ρ-)) λ v -> 
                 Bind (apply j [] f v) λ { 
                   (inl _) -> Now v ; 
                   (inr _) -> Never 
                  }                 
              }   
            }
           ; 
          (inr v₂) -> 
            Bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₂ (compat-ext-here ext-id) θ₂) t₂) λ { (red r₂) -> 
              Later λ { .force {j} -> 
                Bind (Forward (evalR j (one ∷ ano-) r₂) (v₂ ∷ ρ-)) λ v -> 
                  Bind (apply j [] f v) λ {
                    (inl _) -> Never ; 
                    (inr _) -> Now v 
                  }
               }
            }
        }
  
  Backward (evalR i ano (case● {Γ₁ = Γ₁} {Γ₂} r refl θ₁ t₁ θ₂ t₂ f)) v = do 
    ano₀ , ano- <- all-no-omega-dist _ _ ano 
    Bind (apply i [] f v) λ {
      (inl _) -> 
         Bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₁ (compat-ext-here ext-id) θ₁) t₁) λ { (red r₁) -> 
           Later λ { .force {j} -> 
               Bind (Backward (evalR j (one ∷ ano-) r₁) v) λ { (v₁ ∷ ρ-) -> 
                 Bind (Backward (evalR j ano₀ r) (inl v₁)) λ ρ₀ -> 
                     Now (mergeRValEnv ano ρ₀ ρ-)                 
               }
            } 
         }
      ;
      (inr _) -> 
          Bind (eval i (one ∷ ano-) (weakenΘ-valEnv Γ₂ (compat-ext-here ext-id) θ₂) t₂) λ { (red r₂) -> 
            Later λ where .force {j} -> 
                             Bind (Backward (evalR j (one ∷ ano-) r₂) v) λ { (v₂ ∷ ρ-) -> 
                               Bind (Backward (evalR j ano₀ r) (inr v₂)) λ ρ₀ -> 
                                 Now (mergeRValEnv ano ρ₀ ρ-)
                             }
          }     
     }

  

  Forward  (evalR i ano (var● x ok)) ρ = Now (lkup ok ρ)
  Backward (evalR i ano (var● x ok)) v  = Now (unlkup ok v)

  Forward (evalR i ano (pin r f))  ρ = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano
    ρ₁  , ρ₂  <- splitRValEnv ρ
    Bind (Forward (evalR i ano₁ r) ρ₁) λ v₁ -> 
      CASE f OF λ { (clo .omega refl θ t) → 
        Later λ { .force {j} -> 
           Bind (eval j ano₂ (tup ∅ _ (∅-lid _) (mult-omega (weakenΘ-value extendΘ v₁) refl) θ) t) λ { 
            (red r₂) -> 
              -- maybe another delaying would be needed here
              Bind (Forward (evalR j ano₂ r₂) ρ₂) λ v₂ -> 
              Now (pair refl v₁ v₂)
           }
        }
      } 
  
    
  Backward (evalR i ano (pin r (clo .omega refl θ t))) (pair {Ξ₁ = []} {[]} refl v₁ v₂) = do 
    ano₁ , ano₂ <- all-no-omega-dist _ _ ano 
    Later λ { .force {j} -> 
      BindR (eval j ano₂ (tup ∅ _ (∅-lid _) (mult-omega (weakenΘ-value extendΘ v₁) refl) θ) t) λ r₂ -> 
        Bind (Backward (evalR j ano₂ r₂) v₂) λ ρ₂ -> 
        Bind (Backward (evalR j ano₁ r) v₁) λ ρ₁ -> 
        Now (mergeRValEnv ano ρ₁ ρ₂) 
     } 

  -- The unidirectional evaluation, of which definition would be
  -- routine except for rather tedious manipulation of value
  -- environments.
    
  eval {Θ} _ ano θ (var x ok) = Now (subst (λ x -> Value Θ x _) (sym (∅-rid _)) (lookupVar θ ok))
  eval _ ano θ (abs m t) = Now (clo m refl θ t) 

  eval {Θ} {Γ = Γ} i ano θ (app {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} {m = m} t₁ t₂)
      with separateEnv {Γ} Δ₁ (m ×ₘ Δ₂) θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ with eval i (proj₁ lemma) θ₁ t₁ | proj₂ lemma | un×ₘ-valEnv Γ θ₂ 
    where 
      lemma' : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₁ +ₘ m ×ₘ Ξ₂) ≡ (Ξₑ₁ +ₘ Ξ₁) +ₘ (Ξₑ₂ +ₘ m ×ₘ Ξ₂)
      lemma' = +ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ (m ×ₘ Ξ₂) 

      lemma : all-no-omega (Ξₑ₁ +ₘ Ξ₁) × all-no-omega (Ξₑ₂ +ₘ m ×ₘ Ξ₂)
      lemma = all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ (subst all-no-omega lemma' ano)  
  ... | T₁ | ano-e2m2 | Ξₑ₂' , θ₂' , refl with (subst all-no-omega (sym (×ₘ-dist m Ξₑ₂' _)) ano-e2m2)
  ... | ano-m[e2'2] with eval i (all-no-omega-dist-×ₘ m (Ξₑ₂' +ₘ Ξ₂) ano-m[e2'2]) θ₂' t₂
  ... | T₂ = 
    Bind T₁ (λ { (clo {Ξ' = Ξ'} {Ξₜ = Ξₜ} m spΞ θf t) → Bind T₂ λ v₂ -> 
      Later λ { .force ->
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
              
        in (Bind (eval _ lemma-ano (tup (m ×ₘ (Ξₑ₂' +ₘ Ξ₂)) Ξ' refl (value-to-multM ano-m[e2'2] v₂) θf) t) λ v ->  Now (subst (λ Ξ -> Value Θ Ξ _) lemma v)  
       )}
    })
      
  eval {Γ = Γ} _ ano θ (unit ad) with discardable-has-no-resources {Γ} θ ad
  ... | refl = Now (substV (sym (∅-lid _)) (unit refl))

  eval {Θ} {Ξₑ} {Γ} i ano θ (letunit {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} m t₀ t) 
    with separateEnv {Γ} (m ×ₘ Δ₀) Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with un×ₘ-valEnv Γ θ₁ 
  ... | Ξₑ₁' , θ₁' , refl 
    with subst all-no-omega (+ₘ-transpose (m ×ₘ Ξₑ₁') Ξₑ₂ (m ×ₘ Ξ₀) _) ano 
  ... | ano'
    with all-no-omega-dist (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) _ ano'
  ... | ano-me1'm0 , ano-e2 
    with eval i (all-no-omega-dist-×ₘ m (Ξₑ₁' +ₘ Ξ₀) (subst all-no-omega (sym (×ₘ-dist m Ξₑ₁' Ξ₀)) ano-me1'm0)) θ₁' t₀ 
  ... | T₀ = Bind T₀ λ { (unit emp-e1'0) → 
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
      in Dmap (substV lemma) (eval i ano-e2 θ₂ t)
   }

  eval {Θ} {Ξₑ} {Γ} i ano θ (pair {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} t₁ t₂) 
    with separateEnv {Γ} Δ₁ Δ₂ θ
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ _) ano 
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano'
  ... | ano-e11 , ano-e22 
    with eval i ano-e11 θ₁ t₁ | eval i ano-e22 θ₂ t₂ 
  ... | T₁ | T₂ = Bind T₁ λ v₁ -> 
                  Bind T₂ λ v₂ -> Now (pair (+ₘ-transpose Ξₑ₁ Ξ₁ Ξₑ₂ _) v₁ v₂) 

  eval {Θ} {Ξₑ} {Γ} i ano θ (letpair {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} m t₀ t) 
    with separateEnv {Γ} (m ×ₘ Δ₀) Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with un×ₘ-valEnv Γ θ₁ 
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
  ... | T₀  = Bind T₀ λ { (pair {Ξ₁ = Ξ₁} {Ξ₂} spΞ v₁ v₂) → 
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
                   in Dmap (substV eq') (eval i (subst all-no-omega (sym eq') ano) θ' t) 
              }

  eval {Θ} {Ξₑ} {Γ} i ano θ (many m t) = do 
    (Ξₑ' , θ' , refl) <- un×ₘ-valEnv Γ θ
    ano-m[e'-] <- subst all-no-omega (sym (×ₘ-dist m Ξₑ' _)) ano
    ano-e'- <- all-no-omega-dist-×ₘ m _ ano-m[e'-] 
    Bind (eval i ano-e'- θ' t) λ v -> 
      Now (many m (×ₘ-dist m Ξₑ' _) v) 
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (unmany {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} {m₀ = m₀} {A} m t₀ t) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂  <- separateEnv {Γ} (m ×ₘ Δ₀) Δ θ  
    Ξₑ₁' , θ₁' , refl <-  un×ₘ-valEnv Γ θ₁ 
    ano' <- subst all-no-omega (+ₘ-transpose (m ×ₘ Ξₑ₁') Ξₑ₂ (m ×ₘ Ξ₀) Ξ) ano 
    ano-me1'm0 , ano-e2 <-  all-no-omega-dist (m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀) _ ano' 
    ano-m[e1'0] <- subst all-no-omega (sym (×ₘ-dist m Ξₑ₁' _)) ano-me1'm0 
    ano-e1'0    <- all-no-omega-dist-×ₘ m _ ano-m[e1'0] 
    Bind (eval i ano-e1'0 θ₁' t₀ ) λ where
      (many {Ξ₀ = Ξ''} .m₀ sp v₀) -> do 
        let ano-mm₀[e1'0] : all-no-omega (m ×ₘ m₀ ×ₘ Ξ'')
            ano-mm₀[e1'0] = subst all-no-omega (cong (m ×ₘ_) (sym sp)) ano-m[e1'0] 
        
            ano-mul[e1'0] : all-no-omega (mul m m₀ ×ₘ Ξ'') 
            ano-mul[e1'0] = subst all-no-omega (sym (mul-×ₘ m m₀ Ξ'')) ano-mm₀[e1'0]

            eq : m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) ≡ mul m m₀ ×ₘ Ξ'' +ₘ Ξₑ₂ +ₘ Ξ
            eq = 
              begin 
                m ×ₘ Ξₑ₁' +ₘ m ×ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ)
                ≡⟨ cong (_+ₘ _) (sym (×ₘ-dist m Ξₑ₁' _)) ⟩ 
                m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ (Ξₑ₂ +ₘ Ξ)
                ≡⟨ cong (λ e -> m ×ₘ e +ₘ _) (sym sp) ⟩ 
                m ×ₘ m₀ ×ₘ Ξ'' +ₘ (Ξₑ₂ +ₘ Ξ)
                ≡⟨ cong (_+ₘ _) (sym (mul-×ₘ m m₀ Ξ'')) ⟩ 
                mul m m₀ ×ₘ Ξ'' +ₘ (Ξₑ₂ +ₘ Ξ)
                ≡⟨ sym (+ₘ-assoc _ _ _) ⟩ 
                mul m m₀ ×ₘ Ξ'' +ₘ Ξₑ₂ +ₘ Ξ
              ∎ 

  
            ano'' : all-no-omega (mul m m₀ ×ₘ Ξ'' +ₘ Ξₑ₂ +ₘ Ξ)
            ano'' = subst all-no-omega eq ano' 
  
            θ' : ValEnv (A ∷ Γ) (M→M₀ (mul m m₀) ∷ Δ) Θ (mul m m₀ ×ₘ Ξ'' +ₘ Ξₑ₂)
            θ' = tup _ Ξₑ₂ refl (value-to-multM ano-mul[e1'0] v₀) θ₂ 
        Bind (eval i ano'' θ' t) λ v -> Now (substV (trans (sym eq) (sym (+ₘ-transpose (m ×ₘ Ξₑ₁') Ξₑ₂ (m ×ₘ Ξ₀) Ξ))) v)  


  eval i ano θ (inl t) = Dmap inl (eval i ano θ t) 
  eval i ano θ (inr t) = Dmap inr (eval i ano θ t)
  eval {Θ} {Ξₑ = Ξₑ} {Γ} i ano θ (case {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} m t₀ t₁ t₂) 
    with separateEnv {Γ} (m ×ₘ Δ₀) Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with un×ₘ-valEnv Γ θ₁ 
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
  ... | T₀ =  Bind T₀ λ { 
                (inl v) → 
                  let θ' : ValEnv (_ ∷ Γ) (M→M₀ m ∷ Δ) Θ (m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂)
                      θ' = tup (m ×ₘ (Ξₑ₁' +ₘ Ξ₀)) Ξₑ₂ refl (value-to-multM ano-m[e1'0] v) θ₂
                  in Dmap (substV lemma) (eval i (subst all-no-omega (sym lemma) ano) θ' t₁) ; 
                (inr v) →
                  let θ' : ValEnv (_ ∷ Γ) (M→M₀ m ∷ Δ) Θ (m ×ₘ (Ξₑ₁' +ₘ Ξ₀) +ₘ Ξₑ₂)
                      θ' = tup (m ×ₘ (Ξₑ₁' +ₘ Ξ₀)) Ξₑ₂ refl (value-to-multM ano-m[e1'0] v) θ₂
                  in Dmap (substV lemma) (eval i (subst all-no-omega (sym lemma) ano) θ' t₂) 
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

  eval i ano θ (roll t) = Dmap roll (eval i ano θ t)
  eval i ano θ (unroll t) = 
   Bind (eval i ano θ t) λ { (roll v) → Later λ where .force -> Now v  }


  eval {Γ = Γ} i ano θ (unit● ad) with discardable-has-no-resources {Γ} θ ad
  ... | refl = Now (red (substR (sym (∅-lid _)) unit●))

  eval {Θ} {Ξₑ} {Γ} i ano θ (letunit● {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} t₀ t) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ <- separateEnv {Γ} Δ₀ Δ θ
    let lemma : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₀ +ₘ Ξ) ≡ Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ)
        lemma = +ₘ-transpose _ _ _ _ 
    let ano' = subst all-no-omega lemma ano 
    ano-e10 , ano-e2- <- all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano' 
    BindR (eval i ano-e10 θ₁ t₀) λ E₀ -> 
     BindR (eval i ano-e2- θ₂ t) λ E -> 
       Now (red (substR (sym lemma) (letunit● E₀ E)))

  eval {Θ} {Ξₑ} {Γ} i ano θ (pair● {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} t₁ t₂) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ <- separateEnv {Γ} Δ₁ Δ₂ θ
    let lemma : Ξₑ₁ +ₘ Ξₑ₂ +ₘ (Ξ₁ +ₘ Ξ₂) ≡ Ξₑ₁ +ₘ Ξ₁ +ₘ (Ξₑ₂ +ₘ Ξ₂)
        lemma = +ₘ-transpose _ _ _ _ 
    let ano' = subst all-no-omega lemma ano
    ano-e11 , ano-e22 <- all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano' 
    BindR (eval i ano-e11 θ₁ t₁) λ E₁ -> 
      BindR (eval i ano-e22 θ₂ t₂) λ E₂ -> 
        Now (red (substR (sym lemma) (pair● E₁ E₂)))  
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (letpair● {Δ₀ = Δ₀} {Δ} {Ξ₀ = Ξ₀} {Ξ} t₀ t) 
    with separateEnv {Γ} Δ₀ Δ θ 
  ... | tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂ 
    with subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₀ _) ano 
  ... | ano' 
    with all-no-omega-dist (Ξₑ₁ +ₘ Ξ₀) _ ano' 
  ... | ano-e10 , ano-e2- 
    with eval i ano-e10 θ₁ t₀ | eval i (one ∷ one ∷ ano-e2-) (weakenΘ-valEnv Γ (compat-ext-here (compat-ext-here ext-id)) θ₂) t 
  ... | T₁ | T = 
    Bind T₁ λ { (red E₁) -> 
     Bind T  λ { (red E ) -> 
       Now (red (substR (+ₘ-transpose Ξₑ₁ Ξ₀ _ _) (letpair● E₁ E)))
     }}

  eval i ano θ (inl● t) = 
    BindR (eval i ano θ t) λ E -> Now (red (inl● E))
    
  
  eval i ano θ (inr● t) = 
    BindR (eval i ano θ t) λ E -> Now (red (inr● E))    
  
  eval {Θ} {Ξₑ} {Γ} i ano θ (case● {Δ₀ = Δ₀} {Δ} {Δ'} {Ξ₀ = Ξ₀} {Ξ} {Ξ'} t t₁ t₂ t₃) 
    with separateEnv {Γ} (Δ₀ +ₘ Δ) _ θ 
  ... | tup Ξₑ₁₂ Ξₑ₃ refl θ' θ₃
    with discardable-has-no-resources {Γ} θ₃ (omega×ₘ-discardable Δ') 
  ... | refl 
    with un×ₘ-valEnv Γ θ₃
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
        Bind T λ { (red r) ->
        Bind T₃ λ { f -> 
          Now (red (substR (trans lemma' (sym lemma))
            let f' = weakenΘ-value smashΘ (subst (λ x -> Value Θ x _) (∅-lid ∅) f)
            in (case● r refl θ₂ t₁ θ₂ t₂ f')))
        }
        }
      where
        lemma' : Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) 
                 ≡ Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ omega ×ₘ ∅
        lemma' = 
          sym (trans (cong (λ x -> Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) +ₘ x)
                           (×ₘ∅ omega))
                     (∅-rid (Ξₑ₁ +ₘ Ξ₀ +ₘ (Ξₑ₂ +ₘ Ξ) )))

 
  eval {Θ} {Ξₑ} {Γ} i ano θ (var● x ad ok) 
    with discardable-has-no-resources {Γ} θ ad
  ... | refl = Now (red (substR (sym (∅-lid _)) (var● x ok)))

  eval {Θ} {Ξₑ} {Γ} i ano θ (pin {Δ₁ = Δ₁} {Δ₂} {Ξ₁ = Ξ₁} {Ξ₂} t₁ t₂) = do 
    tup Ξₑ₁ Ξₑ₂ refl θ₁ θ₂  <- separateEnv {Γ} Δ₁ Δ₂ θ 
    let ano' = subst all-no-omega (+ₘ-transpose Ξₑ₁ Ξₑ₂ Ξ₁ _) ano
    ano-e11 , ano-e22 <- all-no-omega-dist (Ξₑ₁ +ₘ Ξ₁) _ ano' 
    BindR (eval i ano-e11 θ₁ t₁) λ r -> 
      Bind (eval i ano-e22 θ₂ t₂) λ v -> 
        Now (red (substR (+ₘ-transpose _ _ _ _) (pin r v)))
     
    
  
  eval {Γ = Γ} i ano θ (unlift e) = do
    Ξ' , θ' , refl <- un×ₘ-valEnv Γ θ
    ano₁ , ano₂  <- all-no-omega-dist _ _ ano 
    refl <- all-no-omega-omega×ₘ _ ano₁  
    refl <- all-no-omega-omega×ₘ _ ano₂ 
    Bind (eval i (subst all-no-omega (sym (∅-lid ∅)) all-no-omega-∅ ) θ' e) λ v -> 
      BindR (apply i (one ∷ subst all-no-omega (sym lemma₁) all-no-omega-∅) (weakenΘ-value (compat-ext-here ext-id) v) (red var●₀)) λ r -> 
        Now (substV (sym lemma₂) (inj refl (weakenΘ-residual (compat-skip smashΘ) (substR (cong (one ∷_) lemma₁) r) )))
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
    Ξₑ₂' , θ₂' , refl <- un×ₘ-valEnv Γ θ₂
    ano₁' , _ <- all-no-omega-dist _ _ (subst all-no-omega lemma' ano)
    Bind (eval i ano₁' θ₁ e₁) λ { 
      (inj spΞ r) → do 
        refl , refl <- ∅+ₘ∅-inv _ _ (sym spΞ)
        refl <- all-no-omega-omega×ₘ _ (subst all-no-omega (∅-lid _) anoₑ)         
        Bind (eval i (subst all-no-omega (sym (∅-lid ∅)) all-no-omega-∅) θ₂' e₂) λ v -> Later λ { .force {j} -> 
           Bind (Forward (evalR j (one ∷ all-no-omega-∅) r) (weakenΘ-value smashΘ (substV (∅-lid ∅) v) ∷ [])) λ v' -> 
            Now (substV (sym lemma) (weakenΘ-value extendΘ v'))
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
    Ξₑ₂' , θ₂' , refl <- un×ₘ-valEnv Γ θ₂
    ano₁' , _ <- all-no-omega-dist _ _ (subst all-no-omega lemma' ano)
    Bind (eval i ano₁' θ₁ e₁) λ { 
      (inj spΞ r) → do 
        refl , refl <- ∅+ₘ∅-inv _ _ (sym spΞ)
        refl <- all-no-omega-omega×ₘ _ (subst all-no-omega (∅-lid _) anoₑ)         
        Bind (eval i (subst all-no-omega (sym (∅-lid ∅)) all-no-omega-∅) θ₂' e₂) λ v -> Later λ { .force {j} -> 
          Bind (Backward (evalR j (one ∷ all-no-omega-∅) r) (weakenΘ-value smashΘ (substV (∅-lid ∅) v))) λ { (v' ∷ []) -> 
             Now (substV (sym lemma) (weakenΘ-value extendΘ v'))
           }
         } 
     } 
    where
      lemma' : ∀ {n} {Ξₑ₁ Ξ₁ X Y : MultEnv n} -> Ξₑ₁ +ₘ X +ₘ (Ξ₁ +ₘ Y) ≡ Ξₑ₁ +ₘ Ξ₁ +ₘ (X +ₘ Y)
      lemma' {n} {A} {B} {C} {D} = +ₘ-transpose A C B D 

      lemma : ∀ {n} -> ∅ +ₘ omega ×ₘ ∅ +ₘ (∅ +ₘ omega ×ₘ ∅) ≡ ∅ {n} 
      lemma {n} rewrite ×ₘ∅ {n} omega | ∅-lid {n} ∅ = ∅-lid ∅
      
  


open Interpreter public 
