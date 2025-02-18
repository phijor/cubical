{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.DirProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Sigma using (_×_ ; ≡-×)

open import Cubical.Algebra.Group.Base using (Group ; GroupStr ; makeIsGroup)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; IsGroupHom)

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

module DirProd {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ') where
  open IsGroupHom

  fstHom : GroupHom (DirProd G H) G
  fstHom .fst = fst
  fstHom .snd .pres· _ _ = refl
  fstHom .snd .pres1 = refl
  fstHom .snd .presinv _ = refl

  sndHom : GroupHom (DirProd G H) H
  sndHom .fst = snd
  sndHom .snd .pres· _ _ = refl
  sndHom .snd .pres1 = refl
  sndHom .snd .presinv _ = refl

  pairingHom : {K : Group ℓ} (φ : GroupHom K G) (ψ : GroupHom K H) → GroupHom K (DirProd G H)
  pairingHom (φ , is-hom-φ) (ψ , is-hom-ψ) = [φ,ψ] where
    module φ = IsGroupHom is-hom-φ
    module ψ = IsGroupHom is-hom-ψ

    [φ,ψ] : GroupHom _ (DirProd G H)
    [φ,ψ] .fst k .fst = φ k
    [φ,ψ] .fst k .snd = ψ k
    [φ,ψ] .snd .pres· k₁ k₂ = ≡-× (φ.pres· k₁ k₂) (ψ.pres· k₁ k₂)
    [φ,ψ] .snd .pres1 = ≡-× (φ.pres1) (ψ.pres1)
    [φ,ψ] .snd .presinv k = ≡-× (φ.presinv k) (ψ.presinv k)
    {-# INLINE [φ,ψ] #-}

open DirProd public using (fstHom ; sndHom ; pairingHom)
