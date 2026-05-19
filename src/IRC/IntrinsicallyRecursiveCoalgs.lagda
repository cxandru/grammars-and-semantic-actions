\begin{code}
open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.Function
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Sum.Base as ⊎
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Unit
open import Cubical.Data.Empty.Base
open import IRC.Util
module IRC.IntrinsicallyRecursiveCoalgs {A : Type} (_≺_ : Rel A A lzero) where

private variable
 ⇃ ↿ l l' ℓ ℓ' : Level

-- first A: parameter, outer, larger
-- snd A: index, inner, smaller
-- partially applied (parameterized!): Get a family w (inner) index free, outer bound
T< : A → (A → Type l) → (A → Type l)
\end{code}
%<*properTDefn>
\begin{code}[inline]
T< i X j = (j ≺ i) × X j
\end{code}
%</properTDefn>
\begin{code}
module ForTypes where
  < : A → Type -- downset
  < i = Σ[ j ∈ A ] (j ≺ i)
  -- restriction
  _|<_ : (A → Type ⇃) → (i : A) → ((< i) → Type ⇃)
  (X |< i) (j , _pf) = X j
\end{code}
%<*partialElt>
\begin{code}
  J< J'< : (i : A) → ((< i) → Type ⇃) → (A → Type ⇃)
  J'<  i X j =  ∀ (pf : j ≺ i) → X (j , pf)
  J<   i X j =  Σ[ pf ∈ j ≺ i ] X (j , pf)
\end{code}
%</partialElt>
%<*Jdef>
\begin{code}
< : A → Type -- downset
< i = Σ[ j ∈ A ] (j ≺ i)
-- restriction
_|<_ : (A → Type ⇃) → (i : A) → ((< i) → Type ⇃)
(X |< i) (j , _pf) = X j

-- inclusion: copartial element formulation
J< : (i : A) → ((< i) → Type ⇃) → (A → Type ⇃)
J<   i X j =  Σ[ pf ∈ j ≺ i ] X (j , pf)

-- truncation: restriction, then inclusion: _|<;J< ≈ T
T : (i : A) → (A → Type ⇃) → (A → Type ⇃)
T   i X j =  (j ≺ i) × X j -- "annotate with pfs j < i"
\end{code}
%</Jdef>
\begin{code}
J'< : (i : A) → ((< i) → Type ⇃) → (A → Type ⇃)
J'<  i X j =  ∀ (pf : j ≺ i) → X (j , pf)

T' : (i : A) → (A → Type ⇃) → (A → Type ⇃)
T'  i X j =  ∀ (pf : j ≺ i) → X j
\end{code}
%<*Flt>
\begin{code}
[_]< : ((A → Type ⇃) → (A → Type ↿)) → (i : A) → ((< i) → Type ⇃) → Type ↿
[ F ]< i X = F (λ j → Σ[ pf ∈ j ≺ i ] X (j , pf)) i
\end{code}
%</Flt>
\begin{code}
--wellfoundification
_↓ : ((A → Type ⇃) → (A → Type ↿)) → ((A → Type ⇃) → (A → Type ↿))
(F ↓) X i = [ F ]< i (X |< i) -- F (J< i (X |< i)) i -- F (λ j → (j ≺ i) × X j) i -- = F (T i X) i
\end{code}
\begin{code}

open import Cubical.Foundations.Isomorphism

-- without the naturality requirement, for that see `unique`
is-Wellfounded : {⇃ ↿ : Level} → ((A → Type ⇃) → (A → Type ↿)) → (Type (ℓ-suc (⇃ ⊔ ↿)))
is-Wellfounded {⇃ = ⇃} {↿ = ↿} G =
  ∀ (i : A) →
   Σ[ G<i ∈ (((< i) → Type ⇃) → (Type ↿)) ]
    ∀ (X : (A → Type ⇃)) → Iso (G X i) (G<i (X |< i))

counit' : {r : A → Type} → (i : A) → (j : A) → (J< i (r |< i)) j → r j
counit' i j rj = rj .snd

-- not definable

-- unit' : {r : A → Type} → (i : A) → (j : A) → r j → (J< i (r |< i)) j
-- unit' i j rj = {!!} , rj (need j ≺? i)

-- alternative "partial element" definition

unit : {r : A → Type} → (i : A) → (j : A) → r j → (J'< i (r |< i)) j
unit i j rj = λ _pf → rj

-- not definable

-- counit : {r : A → Type} → (i : A) → (j : A) → (J'< i (r |< i)) j → r j
-- counit i j rj = {!!} (need j ≺? i)

-- note: For the Σ formulation the unit is definable and the counit not, for Π
-- it is vice versa.

[_]'< : ((A → Type ⇃) → (A → Type ↿)) → (i : A) → ((< i) → Type ⇃) → Type ↿
[ F ]'< i X = F (J'< i X) i  -- F (λ j → ∀ (pf : j ≺ i) → X (j , pf)) i

watch₁ :
  ∀ (i : A) →
  {X Y : A → Type l} → (X ⇒ Y) →
  T< i X ⇒ T< i Y
watch₁ _ h j x = fst x , (h j ∘ snd) x
-- (λ j → λ{(x , y) → x , h j y}

T<⇃' : (i : A) → (_≺?i : (j : A) → Dec (i ≺ j)) → (X : A → Type ⇃) → ((j : A) → Type ⇃)
T<⇃' i _≺?i X j = case (j ≺?i) of λ{(yes _) → X j; (no _) → ⊥*}

module withDec< (_≺?_ : (i j : A) → Dec (i ≺ j)) where
  T<⇃ : A → (A → Type ⇃) → (A → Type ⇃)
  T<⇃ i X j = case (j ≺? i) of λ{(yes _) → X j; (no _) → ⊥*}

  _↓⇃ : ((A → Type ↿) → (A → Type ⇃)) → ((A → Type ↿) → (A → Type ⇃))
  (F₀ ↓⇃) r i = (F₀ (T<⇃ i r)) i

  module c2a (wf : WellFounded _≺_)
       (F₀ : (r : A → Type l) → (A → Type l))
       (F₁ : {r r′ : A → Type l} →
          (r ⇒ r′) → F₀ r ⇒ F₀ r′)
          -- (i : A) → F₀ r i → (F₀ ((_≺ i) ⊠ r) i)
       (Fwf : {r : A → Type l} → F₀ r ⇒ (F₀ ↓⇃) r)

       -- coalgebra
       {r : A → Type l} (c : r ⇒ F₀ r)
       -- target algebra
       {X : A → Type l} (a : (F₀ X) ⇒ X) where
    open WFI wf

    private
      IS : (∀ x → (∀ y → y ≺ x → (r y → X y)) → (r x → X x))
      IS i IH = a i ∘ F₁ (fiz) i ∘ Fwf i ∘ c i where
        fiz : T<⇃ i r ⇒ X
        fiz j x₁ with j ≺? i
        ... | yes p = IH j p x₁

    c2a-morph : r ⇒ X
    c2a-morph g = induction {P = λ g → r g → X g} IS g

-- simple guard: Bind the free variable under an existential
-- corresponds to $G: Set^A → Set^A, G(X)_i ≔ ⨆_{j < i} X_j$"
[_]_⊔  : (r : A → Type l) → (A → Type l)
[_]_⊔ r i = Σ A (T< i r)
-- ([ _≺_ ] r ⊔) i

-- indexed guard
-- Writing it as such is the only way to express `Fwf` pointfree
_↓₀ : ((A → Type ⇃) → (A → Type ↿)) → ((A → Type ⇃) → (A → Type ↿))
(F₀ ↓₀) X i = (F₀ (λ j → (j ≺ i) × X j)) i

guard₀₁ :
  {F : (A → Type l) → (A → Type l)} →
  (F₁ : {X Y : A → Type l} → (X ⇒ Y) → F X ⇒ F Y) →
  {X Y : A → Type l} → (X ⇒ Y) →
  (F ↓₀) X ⇒ (F ↓₀) Y
guard₀₁ F₁ h i = F₁ (watch₁ i h) i

-- guard is a higher-order Functor – guard₁ : ([ [Set^A,Set^A], [Set^A,Set^A] ]₁)
guard₁ : (F G : (A → Type l) → (A → Type l)) →
  (∀ (X : A → Type l) → F X ⇒ G X) →
  ∀ (X : A → Type l) → (F ↓₀) X ⇒ (G ↓₀) X
guard₁ F G μ X i = μ (T< i X) i

PWLift : (F : Type l → Type l) → ((A → Type l) → (A → Type l))
PWLift F = pwl F ∘ [_]_⊔


-- with "partial element" formulation (J'<). This also works, but differently.
module c2a' (wf : WellFounded _≺_)
     (F₀ : (r : A → Type) → (A → Type)) --temporarily suspended universe polymorphism, need to lift `_≺_` to `l` to restore
     (F₁ : {r r′ : A → Type} →
        (r ⇒ r′) → F₀ r ⇒ F₀ r′)
     (Fwf : {r : A → Type} → (i : A) → ([ F₀ ]'< i (r |< i)) → F₀ r i) where
  open WFI wf

  private
    iuncurry : {r X : A → Type} → (i : A) (IH : (y : A) → y ≺ i → r y → X y) →
      ((_≺ i) ⊠ r) ⇒ X
    iuncurry _ IH j = uncurry (IH j)


module c2a (wf : WellFounded _≺_)
     (F₀ : (r : A → Type l) → (A → Type l))
     (F₁ : {r r′ : A → Type l} →
        (r ⇒ r′) → F₀ r ⇒ F₀ r′)
        -- (i : A) → F₀ r i → (F₀ ((_≺ i) ⊠ r) i)
     (Fwf : {r : A → Type l} → F₀ r ⇒ (F₀ ↓₀) r) where
  open WFI wf

  module apo-Definition
     -- target algebra (before "coalg" here bc coalg deps on carrier X)
     {X : A → Type l} (a : (F₀ X) ⇒ X)
     -- early-terminating coalgebra
     {r : A → Type l} (c : r ⇒ F₀ (X ⊞ r)) where
    private
      IS : (∀ x → (∀ y → y ≺ x → (r y → X y)) → (r x → X x))
      IS i IH = a i ∘ F₁ (λ{j (j≺i , X+r) → ⊎.elim (idfun _) (IH j j≺i) X+r}) i ∘ Fwf i ∘ c i
    apo : r ⇒ X
    apo g = induction {P = λ g → r g → X g} IS g

  open apo-Definition public

  private
    iuncurry : {r X : A → Type l} → (i : A) (IH : (y : A) → y ≺ i → r y → X y) →
      ((_≺ i) ⊠ r) ⇒ X
    iuncurry _ IH j = uncurry (IH j)

  module c2a-morph-Definition
     -- coalgebra
     {r : A → Type l} (c : r ⇒ F₀ r)
     -- target algebra
     {X : A → Type l} (a : (F₀ X) ⇒ X) where

    private
      IS : (∀ x → (∀ y → y ≺ x → (r y → X y)) → (r x → X x))
      IS i IH =
\end{code}
%<*elegant>
\begin{code}
        a i ∘ F₁ (iuncurry i IH) i ∘ Fwf i ∘ c i
\end{code}
%</elegant>
\begin{code}
    c2a-morph : r ⇒ X
    c2a-morph g = induction {P = λ g → r g → X g} IS g

    module c2a
       (F-hom : {X Y Z : A → Type l} →
         (f : (Y ⇒ Z)) → (g : (X ⇒ Y)) →
         (i : A) → F₁ (f ∘ᵢ g) i ≡ (F₁ f ∘ᵢ F₁ g) i
       )

       -- We cannot express this as `F₁ sndᵢ ∘ᵢ Fwf` bc rhs of `Fwf` contains `i`
       -- (ε := F₁ sndᵢ) : (F₀ ((_≺ i) ⊠ r) i) → F₀ r i
       (ε-split-epi : (i : A) → {r : A → Type l} → (x : F₀ r i) → F₁ sndᵢ i (Fwf i x) ≡ x)
       where

      private
        preq : (i : A) → iuncurry i (λ j _ → c2a-morph j) ≡ c2a-morph ∘ᵢ sndᵢ
        preq i = funExt λ j → funExt λ{(x1 , x2) → refl}

      is-c2a-morph : (i : A) → c2a-morph i ≡ a i ∘ F₁ c2a-morph i ∘ c i
      is-c2a-morph i = c2a-morph i ≡⟨ induction-compute IS i ⟩
        a i ∘ (F₁ (iuncurry i (λ j _ → c2a-morph j)) i ∘ Fwf i) ∘ c i ≡⟨ (cong (λ o → a i ∘ o ∘ c i) (
          F₁ (iuncurry i (λ j _ → c2a-morph j)) i ∘ Fwf i ≡⟨ cong (_∘ Fwf i) (
            F₁ (iuncurry i (λ j _ → c2a-morph j)) i ≡⟨ cong (λ o → F₁ o i) (
                iuncurry i (λ j _ → c2a-morph j) ≡⟨ preq i ⟩
                c2a-morph ∘ᵢ sndᵢ ∎) ⟩
            F₁ (c2a-morph ∘ᵢ sndᵢ) i ≡⟨ F-hom c2a-morph sndᵢ i ⟩
            (F₁ c2a-morph ∘ᵢ F₁ sndᵢ) i ∎) ⟩
          (λ x → (F₁ c2a-morph i ((F₁ sndᵢ) i (Fwf i x))))
                   ≡⟨ (funExt λ x → cong (λ o → F₁ c2a-morph i o) (ε-split-epi i x)) ⟩
           F₁ c2a-morph i ∎))⟩
        a i ∘ F₁ c2a-morph i ∘ c i ∎

       -- uniqueness pf requires this one of the naturality squares
       -- guard₀₁ F₁ h = F₁ (watch₁ i h)
      module unique (sq : {r r' : A → Type l} → (h : r ⇒ r') → (i : A) →
           F₁ h i ≡ F₁ sndᵢ i ∘ (guard₀₁ F₁ h) i ∘ Fwf i) where
        private
          unique-step : (u : r ⇒ X) → (isC2AMorph-u : a ∘ᵢ F₁ u ∘ᵢ c ≡ u) →
              (i : A) → ((j : A) → j ≺ i → c2a-morph j ≡ u j) → c2a-morph i ≡ u i
          unique-step u isC2AMorph-u i IH =
            c2a-morph i ≡⟨ is-c2a-morph i ⟩ a i ∘ F₁ c2a-morph i ∘ c i ≡⟨ cong (λ o → a i ∘ o ∘ c i) (
              F₁ c2a-morph i ≡⟨ sq c2a-morph i ⟩
              F₁ sndᵢ i ∘ F₁ (watch₁ i c2a-morph) i ∘ Fwf i ≡⟨ cong (λ o → F₁ sndᵢ i ∘ F₁ o i ∘ Fwf i)
               (watch₁ i c2a-morph ≡⟨ aux ⟩ watch₁ i u ∎)⟩
               F₁ sndᵢ i ∘ F₁ (watch₁ i u) i ∘ Fwf i ≡⟨ sym (sq u i) ⟩
                 F₁ u i ∎ )⟩ (a ∘ᵢ F₁ u ∘ᵢ c) i ≡⟨ funExt⁻ isC2AMorph-u i ⟩ u i ∎
               where
                 aux : watch₁ i c2a-morph ≡ watch₁ i u
                 aux = funExt λ j → funExt λ{(x , y) → λ i → ( x , IH j x i y) }

        unique : (u : r ⇒ X) → (isC2AMorph-u : a ∘ᵢ F₁ u ∘ᵢ c ≡ u) → (i : A) → c2a-morph i ≡ u i
        unique u isC2AMorph-u i = induction (unique-step u isC2AMorph-u) i

  open c2a-morph-Definition public
