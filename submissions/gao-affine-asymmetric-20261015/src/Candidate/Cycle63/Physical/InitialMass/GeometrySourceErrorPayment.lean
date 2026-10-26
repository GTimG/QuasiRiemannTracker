/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorCompletePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorFamily
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAssembly

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentLogDyadic

/-- Specialize the normalized-family payment to the exact weighted source.
Its fixed modulus gates are derived internally; only the normalized estimate
remains explicit. -/
theorem actual_weighted_source_error_paid_of_normalized {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(Ψ : 𝓢(ℝ,ℂ)) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    let Qfix:=internalQ (weighted_sourceFixedIdeal F) η
    (∀T : Finset (Fin D.N),∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) →
    ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z := by
  intro W hW hs η Qfix hnormalized
  exact actual_affine_error_uniform_paid_of_normalized (α:=Fin D.N) F.modulus ⊤ le_top
    0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad W hW hs Ψ η η εaffine mesh
    hε hmesh Qfix (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 hnormalized

/-- The original retained error estimate for the exact weighted source,
with the normalized-family estimate and fixed modulus gates supplied. -/
theorem actual_weighted_source_error_paid {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hβ : 51/100≤HeckeZeroSupremum.beta)(Ψ : 𝓢(ℝ,ℂ)) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z := by
  intro W hW hs η
  apply actual_weighted_source_error_paid_of_normalized F εaffine mesh hε hmesh Ψ
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  exact actual_affine_error_normalized_family (α:=Fin D.N) F.modulus ⊤ le_top
    F.S F.exclusions.bad W hSmooth hs hβ Ψ η η (weighted_sourceFixedIdeal F)
    (weighted_sourceFixedIdeal_le_modulus F) (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 εaffine mesh hε hmesh0 hmesh hmeshμ hmeshcap

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_weighted_source_error_paid_of_normalized
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_weighted_source_error_paid
