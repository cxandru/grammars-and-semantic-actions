open import Agda.Primitive
open import Cubical.Foundations.Function
open import Cubical.HITs.FiniteMultiset
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sum.Base
module IRC.Util where

private variable
 l l' ℓ ℓ' ℓ′ ℓ′′ : Level
 A : Type ℓ

-- index-preserving arrow
infixr 2 _↠_
_↠_ : {ℓ : Level} → {A : Type ℓ} → (r : A → Type l) → (r′ : A → Type l') → Type (l ⊔ l' ⊔ ℓ)
_↠_ {A = A} r r′ = ∀ {i : A} → r i → r′ i

-- index-preserving arrow, but explicit
infixr 2 _⇒_
_⇒_ : {ℓ : Level} → {A : Type ℓ} → (r : A → Type l) → (r′ : A → Type l') → Type (l ⊔ l' ⊔ ℓ)
_⇒_ {A = A} r r′ = ∀ (i : A) → r i → r′ i

infixr 9 _∘ᵢ_
_∘ᵢ_ : {X : A → Type l} → {Y : A → Type l'} → {Z : A → Type ℓ'}
       (f : (Y ⇒ Z)) → (g : (X ⇒ Y)) → (X ⇒ Z)
_∘ᵢ_ f g _ p = f _ (g _ p)

idᵢ : {X : A → Type l} → X ⇒ X
idᵢ _ x = x

-- singleton
data Singleton {ℓ : _} {A : Set ℓ} : A -> Set ℓ where
  singleton : (a : A) -> Singleton a

-- pointwise (indexed) sum + product
infixr 25 _⊞_ _⊠_

_⊞_ _⊠_ : (L : A → Type ℓ′) → (R : A → Type ℓ′′) → (i : A) → Type (ℓ′ ⊔ ℓ′′)
(l ⊞ r) i = l i ⊎ r i
(l ⊠ r) i = l i × r i
-- induced product
_□_ : ∀ {ℓ ℓ′ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (L : A → Type ℓ′) → (R : B → Type ℓ'') → (A × B) → Type (ℓ′ ⊔ ℓ'')
_□_ l r (i , j) = l i × r j

fstᵢ : {L : A → Type ℓ′} → {R : A → Type ℓ′′} → L ⊠ R ⇒ L
fstᵢ _ = fst

sndᵢ : {L : A → Type ℓ′} → {R : A → Type ℓ′′} → L ⊠ R ⇒ R
sndᵢ _ = snd

inlᵢ : {L : A → Type ℓ′} → {R : A → Type ℓ′′} → L ⇒ L ⊞ R
inlᵢ _ = inl

inrᵢ : {L : A → Type ℓ′} → {R : A → Type ℓ′′} → R ⇒ L ⊞ R
inrᵢ _ = inr

-- need to use ⸴ instead of , bc the latter is syntax for × and else we get parsing ambiguity
-- i don't know why this doesn't seem to be a problem with agda-stdlib
[_⸴_] : {X : A → Type ℓ'} {Y : A → Type l} {Z : A → Type l'} →
  (X ⇒ Z) → (Y ⇒ Z) → ((X ⊞ Y) ⇒ Z)
[ f ⸴ g ] i (inl x) = f i x
[ f ⸴ g ] i (inr x) = g i x

_⊞₁_ : {X : A → Type ℓ'} → {Y : A → Type l} → {C : A → Type l'} → {D : A → Type ℓ'} → (f : X ⇒ Y) → (g : C ⇒ D) → (X ⊞ C) ⇒ (Y ⊞ D)
_⊞₁_ f g = [ inlᵢ ∘ᵢ f ⸴ inrᵢ ∘ᵢ g ]

-- _⊠₁_ f g i =

⟨_⸴_⟩ : {X : A → Type ℓ'} {Y : A → Type l} {Z : A → Type l'} →
  (X ⇒ Y) → (X ⇒ Z) → (X ⇒ (Y ⊠ Z))
⟨ f ⸴ g ⟩ i x = ( f i x , g i x )


-- pointwise lifting of a functor to families
-- aka the Morphism component of Δ / K ? (diagonal / constant functor)
pwl : {ℓ : Level} {A : Type ℓ} → (F : Type l → Type l) → ((A → Type l) → (A → Type l))
pwl F X i = F (X i)
