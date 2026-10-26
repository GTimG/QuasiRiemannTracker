/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainTwoLevel
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAssembly

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle63InitialMass
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
theorem actual_weighted_source_main_paid {D : WeightedQRH.MomentData}
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
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤C ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧
          GeometryAffineMainPaidSpec F.modulus ⊤ le_top F.S W hW hs η η mesh
            (geometryLossUnit 1 εaffine) T S degree C Z := by
  intro W hW hs η
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  obtain ⟨τ,hτ,hτcap,hpaid⟩:=actual_affine_main_uniform_paid_two_level (α:=Fin D.N)
    F.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad
    W hSmooth hs hβlo hβhi η 1 (fixedSourceNaturalRow F.S F.exclusions.prime F.exclusions.bad)
    1 (by norm_num) εaffine mesh bΦ hε hmesh hmesh0 hmeshμ hmeshcap hmeshlow hslot hmarkedmesh hbΦ
  refine ⟨τ,hτ,hτcap,?_⟩
  have hp:=hpaid (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_le_modulus F)
    (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_top F) η)
    (OAI.SevenEighths.CenteredMomentDetectorEnergyInitialState.weighted_source_fixed_gates F η).2.2.2
  rw [←actual_weighted_source_natural_excluded F] at hp
  exact hp

end
end OAI.SevenEighths.Cycle63InitialMass
