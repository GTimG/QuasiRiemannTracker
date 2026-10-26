import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineMainCompletePayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineHighUniform
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource
open CenteredMomentEnergyState CenteredMomentEnergyBands

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The common cutoff and the actual paid main terms are constructed from
the fixed natural source. The separate selected-fiber proof is the only
remaining high analytic premise. -/
theorem actual_affine_main_uniform_paid_of_fibers
    {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6)
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (Mcap : ℝ)(hMcap1 : 101/100≤Mcap)(hMcap2 : Mcap≤2)
    (hrow5 : ∀g : GeometryAffineLowSchedule,g.μ=geometryLossUnit 1 εaffine →
      g.δ=geometryAffineHighDictionaryRate (geometryLossUnit 1 εaffine) (Fintype.card α) →
      LowSelectedPaidAt M H hH g Mcap mesh Adm labelExp Presented)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤bΦ)
    (hAdm : ∀ᶠZ : ℝ in atTop,Adm 1 (frequencyLoss Z 32 (geometryLossUnit 1 εaffine/64)+
      geometryLossUnit 1 εaffine/8) (geometryLossUnit 1 εaffine/64))
    (τT : ℝ)
    (hpres : ∀T : Finset α,GeometryLowChildrenPresented (α:=T) (Presented 28) τT η₀ u₀ F₀ R₀ 8)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (geometryLossUnit 1 εaffine/8) 3 1 (geometryLossUnit 1 εaffine/64)) :
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤Cm ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineMainPaidSpec M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤Cycle63.Optimization.geometryLossCap := geometry_loss_below_marked_cap εaffine
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=
    actual_affine_high_uniform_literal_schedule_of_fibers (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀
      W hWs hW hβlo (by unfold Cycle63.Optimization.plainCapacityCost; linarith) μ bΦ hμ hμcap hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,?_⟩
  intro Q hQM hQ hQt hQ72
  have hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) := by
    simpa only [geometryAffineHighDictionaryRate,hgμ] using hgδ
  have hmeshμ' : mesh≤g.μ/8 := by simpa only [hgμ] using hmeshμ
  have hmeshcap' : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := by
    simpa only [hgμ] using hmeshcap
  have hAdm' : ∀ᶠZ : ℝ in atTop,Adm 1 (frequencyLoss Z 32 (g.μ/64)+g.μ/8) (g.μ/64) := by
    simpa only [hgμ] using hAdm
  have hpaid:=actual_affine_main_uniform_paid_of_high (α:=α) M H hH hgate A hc hs Sbad hbad
    W hW hWs hβlo hβhi (excluded F₀.character R₀) εaffine mesh hε hmesh hmesh0 g hgμ
    (Fintype.card α) le_rfl 130 (3*((Fintype.card α:ℝ)+2)) (by norm_num) (by positivity)
    hδ hmeshμ' Mcap hMcap1 hMcap2 (hrow5 g hgμ hgδ) hmeshcap' hmarkedmesh η₀ u₀ F₀ R₀ hu₀ hAdm' τT
    (parentPresentation_of_eq rfl) hpres Q hQM hQ hQt hQ72 (by
      intro T
      obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,SH,hSH,dh,KH,hKH,hcost⟩:=hhigh T
      refine ⟨P,he.symm,hPτ.trans hgτ.symm,SH,dh,KH,hKH.le,?_⟩
      filter_upwards [hcost Q hQM hQ72] with Z hz
      simpa only [hgμ,hgδ] using hz.2)
  simpa only [hgμ] using hpaid

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
