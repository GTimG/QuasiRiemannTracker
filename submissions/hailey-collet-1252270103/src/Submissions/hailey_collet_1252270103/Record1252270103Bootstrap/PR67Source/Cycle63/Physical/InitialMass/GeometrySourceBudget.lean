import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySourceMainPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePaidComponents
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometrySourceErrorPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

/-- The fixed weighted-source geometry budget has only its exact paid error
family left to supply. All retained main and source identities are internal. -/
theorem actual_weighted_source_geometry_budget_of_error {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hmeshlow : mesh≤Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8))
    (hslot : 5/2*mesh ≤ secondStepMesh εaffine)
    (hbΦ : 2≤bΦ)(hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    (∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤C ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧
          GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z) →
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
      SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  intro W hW hs η herror
  obtain ⟨τ,hτ,hτcap,hmain⟩:=actual_weighted_source_main_paid F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hmeshlow hslot hbΦ hβlo hβhi
  refine ⟨τ,hτ,hτcap,?_⟩
  exact literal_affine_geometry_budget_of_main_error F.modulus ⊤ le_top F.S F.exclusions.bad
    W hW hs η η (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) bΦ mesh εaffine τ hε hmesh hmain herror

/-- The exact weighted source satisfies the geometry budget from the original
main and error estimates, without an additional analytic hypothesis. -/
theorem actual_weighted_source_geometry_budget {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hmeshlow : mesh≤Cycle25.Energy.commonMesh (101/100) 28 1 (geometryLossUnit 1 εaffine/8))
    (hslot : 5/2*mesh ≤ secondStepMesh εaffine)
    (hbΦ : 2≤bΦ)(hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
      SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  apply actual_weighted_source_geometry_budget_of_error F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hmeshlow hslot hbΦ hβlo hβhi
  intro Ψ _hsΨ _hΨ
  exact actual_weighted_source_error_paid F εaffine mesh hε hmesh hmesh0 hmeshμ hmeshcap hβlo Ψ

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
