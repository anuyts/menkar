module MCont where

open import Data.Nat
open import Data.Fin
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Empty
open import Function

open ≡-Reasoning

postulate
  funext : ∀{X : Set} {Y : X → Set} {f g : (x : X) → Y x} → ((x : X) → f x ≡ g x) → f ≡ g

syntax funext (λ x → e) = λ= x , e

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀{X} → X → M X
    _>>=_ : ∀{X Y} → M X → (X → M Y) → M Y
    lunitM : ∀{X Y : Set} {f : X → M Y} → f ≡ (λ x → return x >>= f)
    runitM : ∀{X Y : Set} {f : X → M Y} → f ≡ (λ x → f x >>= return)
    assocM : ∀{X Y Z W : Set} {f : X → M Y} {g : Y → M Z} {h : Z → M W}
      → (λ x → f x >>= (λ y → g y >>= h)) ≡ λ x → (f x >>= g) >>= h
open Monad {{...}} public

record Applic (A : Set → Set) : Set₁ where
  field
    pure : ∀{X} → X → A X
    _⊚_ : ∀{X Y} → A (X → Y) → A X → A Y
    identA : ∀{X}{ax : A X} → pure id ⊚ ax ≡ ax
    compA : ∀{X Y Z}{af : A (X → Y)}{ag : A (Y → Z)}{ax : A X} →
      ((pure (λ (g : Y → Z) (f : X → Y) → g ∘ f) ⊚ ag) ⊚ af) ⊚ ax ≡ ag ⊚ (af ⊚ ax)
    homA : ∀{X Y}{f : X → Y}{x : X} → pure f ⊚ pure x ≡ pure (f x)
    intchA : ∀{X Y}{af : A (X → Y)}{x : X} → af ⊚ pure x ≡ pure (λ g → g x) ⊚ af
open Applic {{...}} public

record Sense (M : Set → Set) {{monadM : Monad M}} {{applicM : Applic M}} : Set₁ where
  pureAM : ∀{X} → return {M} {X} ≡ pure
  ⊚AM : ∀{X Y} {mf : M (X → Y)} {mx : M X} → mf ⊚ mx ≡ (mf >>= λ f → mx >>= λ x → return (f x))

MCont : (R : Set) → (M : Set → Set) → Set → Set
MCont R M X = (M X → M R) → M R

monadMCont : ∀{R M} → {{monadM : Monad M}} → Monad (MCont R M)
--monadMCont {R} {M} {{monadM}} = {!!}
Monad.return (monadMCont {R} {M} ⦃ monadM ⦄) x mx* = mx* (return x)
Monad._>>=_ (monadMCont {R} {M} ⦃ monadM ⦄) mx** x↦my** my* = mx** λ mx → mx >>= λ x → x↦my** x my*
Monad.lunitM (monadMCont {R} {M} ⦃ monadM ⦄) {X}{Y}{f} = λ= x , λ= my* , cong-app lunitM x
Monad.runitM (monadMCont {R} {M} ⦃ monadM ⦄) {X}{Y}{f} = λ= x , λ= my* , cong (f x) (λ= my , (begin
  my* my
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  (my >>= λ y → my* (return y)) ∎
  ))
Monad.assocM (monadMCont {R} {M} ⦃ monadM ⦄) = {!!}
