import Candidate.Target836.Source836.GeometryAffineMainUniform
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow
import Candidate.Target836.Error836.GeometryAffineErrorCompletePayment
import Candidate.Target836.Error836.GeometryAffineErrorFamily
import Candidate.Target836.Target836SourceLiteral
import Candidate.Target836.Source836.GeometryAffinePaidComponents
import Candidate.Target836.Target836InitialSupplier

/- Original module: Candidate.Target836.SourceProvider.WeightedSourceMainPayment. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace Target874836.SourceProvider.Physical
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff ComplexConjugate
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentLogDyadic

/-- The exact reflected weighted source has a paid retained main estimate
with every low/high analytic premise discharged. The error family remains
a separate obligation for the full geometry budget. -/
theorem actual_weighted_source_main_paid {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0< εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤ bΦ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤ 7/8) :
    let W:=fun x=> conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    ∃τ : ℝ,0< τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          OAI.SevenEighths.Target836SourceAssembly.GeometryAffineMainPaidSpec F.modulus ⊤ le_top F.S W hW hs η η mesh
            (geometryLossUnit 1 εaffine) T S degree C Z := by
  intro W hW hs η
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  obtain ⟨τ,hτ,hτcap,hpaid⟩:=OAI.SevenEighths.Target836SourceAssembly.actual_affine_main_uniform_paid (α:=Fin D.N)
    F.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad
    W hSmooth hs hβlo hβhi η 1 (fixedSourceNaturalRow F.S F.exclusions.prime F.exclusions.bad)
    1 (by norm_num) εaffine mesh bΦ hε hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ
  refine ⟨τ,hτ,hτcap,?_⟩
  have hp:=hpaid (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2
  rw [←actual_weighted_source_natural_excluded F] at hp
  exact hp

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.actual_weighted_source_main_paid
end

/- Original module: Candidate.Target836.SourceProvider.WeightedSourceErrorPayment. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace Target874836.SourceProvider.Physical
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
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
    (F : WeightedSourceData D)(εaffine mesh : ℝ)(hε : 0< εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(Ψ : 𝓢(ℝ,ℂ)) :
    let W:=fun x=> conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    let Qfix:=internalQ (weighted_sourceFixedIdeal F) η
    (∀T : Finset (Fin D.N),∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤ Cn ∧ ∀ᶠZ : ℝ in atTop,
        OAI.SevenEighths.Target836ErrorPayment.GeometryAffineErrorNormalizedSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) →
    ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        OAI.SevenEighths.Target836ErrorPayment.GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z := by
  intro W hW hs η Qfix hnormalized
  exact OAI.SevenEighths.Target836ErrorPayment.actual_affine_error_uniform_paid_of_normalized (α:=Fin D.N) F.modulus ⊤ le_top
    0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad W hW hs Ψ η η εaffine mesh
    hε hmesh Qfix (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 hnormalized

/-- The original retained error estimate for the exact weighted source,
with the normalized-family estimate and fixed modulus gates supplied. -/
theorem actual_weighted_source_error_paid {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh : ℝ)(hε : 0< εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hβ : 51/100≤ HeckeZeroSupremum.beta)(Ψ : 𝓢(ℝ,ℂ)) :
    let W:=fun x=> conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        OAI.SevenEighths.Target836ErrorPayment.GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z := by
  intro W hW hs η
  apply actual_weighted_source_error_paid_of_normalized F εaffine mesh hε hmesh Ψ
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  exact OAI.SevenEighths.Target836ErrorPayment.actual_affine_error_normalized_family (α:=Fin D.N) F.modulus ⊤ le_top
    F.S F.exclusions.bad W hSmooth hs hβ Ψ η η (weighted_sourceFixedIdeal F)
    (weighted_sourceFixedIdeal_le_modulus F) (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 εaffine mesh hε hmesh0 hmesh hmeshμ hmeshcap

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.actual_weighted_source_error_paid_of_normalized
#print axioms Target874836.SourceProvider.Physical.actual_weighted_source_error_paid
end

/- Original module: Candidate.Target836.SourceProvider.WeightedSourceBudget. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace Target874836.SourceProvider.Physical
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

/-- The fixed weighted-source geometry budget has only its exact paid error
family left to supply. All retained main and source identities are internal. -/
theorem actual_weighted_source_geometry_budget_of_error {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0< εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤ bΦ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤ 7/8) :
    let W:=fun x=> conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    (∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          OAI.SevenEighths.Target836ErrorPayment.GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z) →
    ∃τ : ℝ,0< τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
      OAI.SevenEighths.Target836SourceAssembly.SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  intro W hW hs η herror
  obtain ⟨τ,hτ,hτcap,hmain⟩:=actual_weighted_source_main_paid F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ hβlo hβhi
  refine ⟨τ,hτ,hτcap,?_⟩
  exact OAI.SevenEighths.Target836SourceAssembly.literal_affine_geometry_budget_of_main_error F.modulus ⊤ le_top F.S F.exclusions.bad
    W hW hs η η (weighted_sourceFixedIdeal F) bΦ mesh εaffine τ hε hmesh hmain herror

/-- The exact weighted source satisfies the geometry budget from the original
main and error estimates, without an additional analytic hypothesis. -/
theorem actual_weighted_source_geometry_budget {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0< εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤ bΦ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤ 7/8) :
    ∃τ : ℝ,0< τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
      OAI.SevenEighths.Target836SourceAssembly.SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  apply actual_weighted_source_geometry_budget_of_error F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ hβlo hβhi
  intro Ψ _hsΨ _hΨ
  exact actual_weighted_source_error_paid F εaffine mesh hε hmesh hmesh0 hmeshμ hmeshcap hβlo Ψ

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.actual_weighted_source_geometry_budget_of_error
#print axioms Target874836.SourceProvider.Physical.actual_weighted_source_geometry_budget
end

/- Original module: Candidate.Target836.Target836Unconditional. -/
section
/- The .874836 endpoint assembled from actual source and count providers.
Adapted from Hailey Collet, OpenAI, DaysSky and Zhongpai Gao; Apache-2.0. -/

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open OAI.SevenEighths

theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry
    Target874836.SourceProvider.Physical.actual_weighted_source_geometry_budget

theorem beta_le_rational : HeckeZeroSupremum.beta ≤ (218709/250000:ℝ) :=
  beta_le_rational_of_chosen_affine
    Target836InitialSupplier.actual_detector_affine_input chosen_affine_input

end
end Target836.FinalAssembly
#print axioms Target836.FinalAssembly.chosen_affine_input
#print axioms Target836.FinalAssembly.beta_le_rational
end
