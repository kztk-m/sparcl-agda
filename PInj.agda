{-# OPTIONS --without-K #-}

module PInj where

open import Codata.Delay renaming (length to dlength ; map to dmap )
open import Codata.Thunk

open import Relation.Binary.PropositionalEquality

open import Size
open import Level
open import Data.Product

-- A pair of partial functions that are supposed to form a partial bijection. 
record _⊢_⇔_ (i : Size) {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set ℓ where
  constructor pre-pinj-i 
  field 
    forward  : A -> Delay B i
    backward : B -> Delay A i 

open _⊢_⇔_ 

