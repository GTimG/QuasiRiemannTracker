/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from Bebel's ChosenSource physical-affine extraction, retaining the
original OpenAI/Collet/Levy/Gao source and mask interfaces. The source itself is
proved by the authentic PositiveSource theorem through PhysicalInlet.q_source. -/
import Candidate.C092.transport.DirectPhysicalInput
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open Cycle25ProbeFinalAssembly
namespace QRH.Cycle092.DirectEnergy

/-- Extract the literal radial initial energy at the actual Q face for arbitrary
compatible source data. The fixed ideal, masks and conjugated profile are genuine. -/
theorem physical_affine_of_unit {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (mesh ε : ℝ)
    (hsource : UnitFaceSource physicalFace mesh ε) :
    ∃ bPhi : ℝ, 2 ≤ bPhi ∧
      Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi ∧
      ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
        ∀ᶠ U : ℝ in atTop, AffineAt F bPhi mesh ε U degree controls C := by
  obtain ⟨b,hb⟩ := radialMajorant_compact.isCompact.bddAbove
  let bPhi : ℝ := max 2 b
  have hbPhi : 2 ≤ bPhi := le_max_left _ _
  have hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi := by
    intro x hx
    exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  let Q := Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal F
  obtain ⟨degree,controls,C,hC,hbound⟩ := hsource (Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x))
    (HeckeInverseAmplification.conjugate_profile_smooth _ (F.W.smooth ⊤))
    (by intro x hx; exact F.complex_support (by simpa using hx))
    bPhi hbPhi η η Q
    (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_le_modulus F)
    (internalQ_ne_zero Q (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top Q (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_le_72 F))
  exact ⟨bPhi,hbPhi,hsPhi,degree,controls,C,hC,hbound⟩

/-- One early mesh is fixed before every generated D/F dictionary. The actual
positive source proves its weighted physical energy, with controls fixed before
all row choices, scale parameters and independent heights. -/
theorem q_physical_affine_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (F : WeightedSourceData D),
      ∃ bPhi : ℝ, 2 ≤ bPhi ∧
        Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi ∧
        ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
          ∀ᶠ U : ℝ in atTop, AffineAt F bPhi mesh ε U degree controls C := by
  obtain ⟨mesh,hm,hsrc⟩ := QRH.Cycle092.PhysicalInlet.q_source hβ ε hε
  exact ⟨mesh,hm,fun _ F => physical_affine_of_unit F mesh ε hsrc⟩
end QRH.Cycle092.DirectEnergy
#print axioms QRH.Cycle092.DirectEnergy.q_physical_affine_source
