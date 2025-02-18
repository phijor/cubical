{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.DirProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Sigma using (_×_ ; ≡-×)
open import Cubical.Algebra.Group.Base using (Group ; GroupStr ; makeIsGroup)

DirProd : ∀ {ℓ ℓ'} → (G : Group ℓ) → (H : Group ℓ') → Group (ℓ-max ℓ ℓ')
DirProd G H = G×H where
  module G = GroupStr (str G)
  module H = GroupStr (str H)

  G×H : Group _
  G×H .fst = ⟨ G ⟩ × ⟨ H ⟩
  G×H .snd .GroupStr.1g = G.1g , H.1g
  G×H .snd .GroupStr._·_ (g , h) (g′ , h′) = g G.· g′ , h H.· h′
  G×H .snd .GroupStr.inv (g , h) = G.inv g , H.inv h
  G×H .snd .GroupStr.isGroup = makeIsGroup
    (isSet× G.is-set H.is-set)
    (λ _ _ _ → ≡-× (G.·Assoc _ _ _) (H.·Assoc _ _ _))
    (λ _ → ≡-× (G.·IdR _) (H.·IdR _))
    (λ _ → ≡-× (G.·IdL _) (H.·IdL _))
    (λ _ → ≡-× (G.·InvR _) (H.·InvR _))
    (λ _ → ≡-× (G.·InvL _) (H.·InvL _))
  {-# INLINE G×H #-}
