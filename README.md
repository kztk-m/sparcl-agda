This is an Agda implementation related to our ICFP 2020 paper:
  
    Kazutaka Matsuda and Meng Wang. "Sparcl: A Language for Partially-Invertible Computation"

The purpose of this implementation is
to prove the type safety of Sparcl by giving a definitional
interpreter that manipulates intrinsically-typed terms. 
As typical of Agda implementations, this implementation is just to be type-checked and not meant to be executed.

Correspondence to the Paper
---------------------------

This is the Agda implementation mentioned in Section 3.6.4. As mentioned in the paper, there is a couple of differences from the formalism in the paper. In particular, the implementation uses products, sums and iso-recursive types instead of constructors, and uses environments instead of
substitutions. 

This implementation provides an intrinsically-typed definitional
interpreter as proofs of the subject reduction (Lemma 3.2 in the paper) and
progress property (unstated), which can be found in 
the file `Definitional.agda` (`eval` and `evalR`).

Besides, Lemma 3.3 is proved based on the definitional
interpreter (`Invertibility.agda`).

How to Type Check
-----------------

**Caution:** The type-checking takes time (around 20 minutes on
Macbook Pro with 3.5 GHz Intel Core i7). 
Most of the time is spent on
termination checking of the definitional interpreter. 
To remove this expensive and yet less interesting part, one may uncomment the two occurrences of `{-# TERMINATING #-}` in
`Definitional.agda`, which instructs Agda to skip terminating checking for the corresponding functions.  With this, type-checking finishes in a few minutes. 

To type check, type `make` to invoke `agda` for type-checking. It will print many lines of messages such as `Checking ...`, but one shall see no type error messages.

Requirements
------------

 * Agda 2.6.1
 * Agda's standard library version 1.3 
 
The scripts are not compatible with standard library version 1.2 or ealier, due to the change on `IsCommutativeMonoid` as of version 1.3.
 
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
