module Cubical.Relation.Binary.More where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Induction.WellFounded

open import Cubical.Relation.Binary.Properties
-- Pulling back a relation along a function.
-- This can for example be used when restricting an equivalence relation to a subset:
--   _~'_ = on fst _~_

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

module _
  (f : A → B)
  (R : Rel B B ℓ)
  where

  private
    accessible : {x : A} → Acc R (f x) → Acc (pulledbackRel f R) x
    accessible (acc rs) = acc (λ y fy<fx → accessible (rs (f y) fy<fx))

  isWFPulledbackRel : WellFounded R → WellFounded (pulledbackRel f R)
  isWFPulledbackRel wf x = accessible (wf (f x))

