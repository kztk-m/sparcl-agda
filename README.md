This is an Agda implementation related to our ICFP 2020 paper:
  
    Kazutaka Matsuda and Meng Wang. "Sparcl: A Language for Partially-Invertible Computation"

The purpose of this implementation is
to prove the type safety of Sparcl by giving a definitional
interpreter that manipulates intrinsically-typed terms. 
As other Agda implementations, the implementation is just to be type-checked and
supposed not to be executed.

Correspondence to the Paper
---------------------------

This is the Agda implementation mentioned in Section 3.6.4. 
As written in the paper, this
version has notable differences from the paper both in syntax (this
version uses products, sums and iso-recursive types instead of
constructors) and semantics (this version uses environments instead of
substitutions). 
This implementation provides an intrinsically-typed definitional
interpreter as proofs of the subject reduction (Lemma 3.2 in the paper) and
progress property (unstated), which can be found in 
the file `Definitional.agda` (`eval` and `evalR`).

Besides, we also have proved Lemma 3.3 based on the definitional
interpreter (`Invertibility.agda`).

How to Type Check
-----------------

**Caution:** The type-checking takes time (around 20 minutes on my
Macbook Pro with 3.5 GHz Intel Core i7). 
Most of the time is spent for
termination checking of the definitional interpreter. 
So, if you trust
us , please uncomment the two occurrences of `{-# TERMINATING #-}` in
`Definitional.agda`, which suggests Agda to skip terminating checking for corresponding functions; after that, type-checking runs in a few minutes. 

Just type `make` to invoke `agda` for type-checking. It will print many lines of messages such as `Checking ...`, but one will see no type error messages.

Requirements
------------

 * Agda 2.6.1
 * Agda's standard library version 1.3 
 
The scripts are not compatible with the standard library version 1.2
or below, due to the change on `IsCommutativeMonoid` as of version 1.3.
 
Agda Scripts
------------

 * `PInj.agda`: an implementation of partially-invertible computation
   (without any proofs).
 * `Syntax.agda`: a syntax of the core system of Sparcl. This version
   uses sums, products and isorecursive types instead of constructors.
 * `Value.agda`: the definitions of values and properties on value
   manipulations.
 * `Definitional.agda`: a definitional interpreter for Sparcl, using
   (a frozen version) of the delay monad.
 * `Invertibility.agda`: a proof that the forward and backward
   evaluations form a (not-necessarily-total) bijection.
