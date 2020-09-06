
module NoFunExt where

open import Lib
open import CwF
open import Pi
open import Identity

FunExtTy : ∀ {i j k} → Set _
FunExtTy {i}{j}{k} =
         ∀ {Γ A B}(f g : Tm Γ (Π {i}{j}{k} A B))
         → Tm (Γ ▶ A) (Id (app {i}{j}{k}{Γ}{A}{B} f) (app g))
         → Tm Γ (Id f g)

A : Ty ∙ lzero
A = ty (λ _ → ⊤) (λ _ → Bool)

B : Ty (∙ ▶ A) lzero
B = ty (λ _ → ⊤) (λ _ → ⊤)

f : Tm ∙ (Π A B)
f = tm (λ _ _ → _ , (λ _ → inj₂ true)) (λ ())

g : Tm ∙ (Π A B)
g = tm (λ _ _ → _ , (λ _ → inj₂ false)) (λ ())

e : Tm (∙ ▶ A) (Id (app f) (app g))
e = Refl (app f)

¬FunExt : FunExtTy → ⊥ {lzero}
¬FunExt funext with ap (λ f → ₂ (f tt) tt) (P (funext f g (Refl (app f))) tt)
... | ()
