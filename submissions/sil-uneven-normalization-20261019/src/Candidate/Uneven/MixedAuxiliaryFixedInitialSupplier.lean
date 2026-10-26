import Candidate.Target830.Parameters
import Candidate.Target830.High.AffinePhysicalSelection
import Candidate.Uneven.AuxiliaryAffineMainLowPayment
import Candidate.Uneven.FineUniformSchedule
import Candidate.Uneven.MixedAuxiliaryHighAffinePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineUniformSchedule
import Candidate.Uneven.AuxiliaryHighParameters
import Candidate.Target830.High.BalancedMass
import Candidate.Uneven.AuxiliaryHighMainCompletePayment
import Candidate.Uneven.AuxiliaryAssemblyInitialSupplier

/- Original module: Candidate.Uneven.MixedAuxiliaryHighUniformSchedule. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.AuxiliaryPhysical
open Marked830Plain
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
open scoped Classical ContDiff
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve ConcretePrimeRowBridge Cycle63Moment
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Select every actual-subset density dictionary before fixing one common
height cutoff. Only the scalar loss rate uses the ambient cardinality.
The exact fiber receipt remains explicit until its separate proof is joined. -/
theorem actual_affine_high_uniform_schedule_of_fibers_mixed_anchor
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤3/4)
    (μ Cs bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/10000000000000000000000000000)(hCs : 1≤ Cs)(hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighSelectedFiberReceipt_mixed_anchor (α:=T) ηcoarse η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighDictionaryRate_mixed_anchor μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighScheduleGates_mixed_anchor W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0< K ∧
        ∀(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤ Z ∧
            OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighSelectedCostSpec_mixed_anchor (α:=T) M H hH  W hbeta P μ δ
              (OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighTarget_mixed_anchor μ δ) (fun _ _ _ _ _=> True)
              (excluded F₀.character R₀) Cs Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  have high (T : Finset α) := OAI.SevenEighths.AuxiliaryHigh.actual_affine_high_selected_all_height_of_fibers_mixed_anchor 
    (α:=T) M H hH ηcoarse η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs (Fintype.card α)
    hμ (hμcap.trans (by norm_num)) hCs (Fintype.card_le_of_injective (fun i : T=> i.val) Subtype.val_injective)
    (fiberReceipt T)
  choose bound hbound J hhigh using high
  have hL : 0≤3*((Fintype.card α:ℝ)+2) := by positivity
  have hb : 0≤ bΦ := by linarith
  obtain ⟨τ,hτ,hτcap,hτzero,hτw,g,hgμ,hgδ,hgτ,hschedule⟩:=SaturatedPlain.geometry_affine_marked_uniform_schedule
    W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2)) bΦ (Fintype.card α) bound J
    hμ hμcap (by norm_num) hL hb (fun T k=>(hbound T k).le)
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  let P:=geometryAffineFinalHighSchedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
    bΦ τ (Fintype.card α) (bound T) hμ (by norm_num) hL hb hτ (fun k=>(hbound T k).le)
  have hs:=hschedule T
  have gates : OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighScheduleGates_mixed_anchor W μ δ P :=
    OAI.SevenEighths.AuxiliaryHigh.geometry_affine_high_schedule_gates_mixed_anchor W hWs hW μ bΦ τ (Fintype.card α) (bound T)
      hμ hbΦ hτ (fun k=>(hbound T k).le)
  refine ⟨P,rfl,rfl,hs.2.1,hs.2.2.1,hs.2.2.2.1,gates,?_⟩
  have hmarked : FineMarkedSchedule P (Fintype.card T) W (33/50) (33/50) :=
    (SaturatedPlain.geometry_final_marked_schedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
      bΦ τ (Fintype.card α) (bound T) hμ hμcap (by norm_num) hL hb hτ
      (fun k=>(hbound T k).le) hτzero hτw).of_card_le
      (Fintype.card_le_of_injective (fun i : T=> i.val) Subtype.val_injective)
  exact hhigh T P hs.1 gates hmarked hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1

/-- Actual source caps are fixed before the shared schedule; each literal
affine high estimate then has its constants before any moving source. -/
theorem actual_affine_high_uniform_literal_schedule_of_fibers_mixed_anchor
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤3/4)
    (μ bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/10000000000000000000000000000)(hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighSelectedFiberReceipt_mixed_anchor (α:=T) ηcoarse η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighDictionaryRate_mixed_anchor μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighScheduleGates_mixed_anchor W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0< K ∧
        ∀(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤ Z ∧
            OAI.SevenEighths.AuxiliaryHigh.GeometryAffineMainHighSpec_mixed_anchor (α:=T) M H hH  W hW.continuous hWs hbeta P μ δ
              (OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighTarget_mixed_anchor μ δ) (excluded F₀.character R₀)
              Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  obtain ⟨Cs,hCs,hcaps⟩:=AuxiliaryPhysical.eventual_actual_affine_exceptional_source_gates (α:=α) M H hH
    W hW.continuous hWs
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=actual_affine_high_uniform_schedule_of_fibers_mixed_anchor
    (α:=α) M H hH ηcoarse η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs bΦ hμ hμcap hCs hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,hpaid⟩:=hhigh T
  refine ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,?_⟩
  intro Q hQM hQ72
  filter_upwards [hpaid Q hQM hQ72,hcaps,eventual_geometry_small_frequency μ hμ]
    with Z hp hc hf
  refine ⟨hp.1,?_⟩
  apply OAI.SevenEighths.AuxiliaryHigh.affine_main_high_spec_of_receipts_mixed_anchor (α:=T) M H hH  W hW.continuous hWs hbeta
    P μ δ (OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighTarget_mixed_anchor μ δ) (excluded F₀.character R₀) Cs Sp degree K
    η₀ Q hQM hQ72 Z hμ (hμcap.trans (by norm_num)) hf.2 _ hp.2
  unfold AuxiliaryPhysical.GeometryAffineMainLowSourceSpec
  intro θ η w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots inp
  exact TargetHigh830.geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
    (hc.2 T η θ w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂
      (hslots.trans (by norm_num)))

end
end OAI.SevenEighths.AuxiliaryHigh
end

/- Original module: Candidate.Uneven.MixedAuxiliaryHighMainUniform. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.AuxiliaryHigh
private theorem mixed_high_spec_eq :
    @OAI.SevenEighths.AuxiliaryHigh.GeometryAffineMainHighSpec_mixed_anchor =
      @OAI.SevenEighths.AuxiliaryHigh.GeometryAffineMainHighSpec := by rfl

private theorem mixed_high_target_eq :
    geometryAffineHighTarget_mixed_anchor = geometryAffineHighTarget := by rfl

open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.AuxiliaryPhysical
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff
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
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The common cutoff and the actual paid main terms are constructed from
the fixed natural source. The separate selected-fiber proof is the only
remaining high analytic premise. -/
theorem actual_affine_main_uniform_paid_of_fibers_mixed_anchor
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)(hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh< Sil.Uneven.AuxiliarySource.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ SaturatedPlain.fineRawMesh*SaturatedPlain.fineRawCore)
    (hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighSelectedFiberReceipt_mixed_anchor (α:=T) ηcoarse η₀ u₀ F₀ R₀ (9/4) (9/4)
        (geometryLossUnit 1 εaffine/8) 3 1 (geometryLossUnit 1 εaffine/64)) :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤ M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec  M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/10000000000000000000000000000 := by
    have hh:=min_le_left (εaffine/128)
      (min ((7/30000000:ℝ)*1/128) (min ((1:ℝ)/128) (1/128)))
    change μ≤εaffine/128 at hh
    linarith
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=
    actual_affine_high_uniform_literal_schedule_of_fibers_mixed_anchor  (α:=α) M H hH ηcoarse η₀ u₀ F₀ R₀ hu₀
      W hWs hW hβlo (by linarith) μ bΦ hμ hμcap hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,?_⟩
  intro Q hQM hQ hQt hQ72
  have hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) := by
    simpa only [OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighDictionaryRate_mixed_anchor,hgμ] using hgδ
  have hmeshμ' : mesh≤ g.μ/8 := by simpa only [hgμ] using hmeshμ
  have hmeshcap' : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := by
    simpa only [hgμ] using hmeshcap
  have hpaid:=actual_affine_main_uniform_paid_of_high (α:=α) M H hH A hc hs Sbad hbad
    W hW hWs hβlo hβhi (excluded F₀.character R₀) εaffine mesh hε hmesh hmesh0 g hgμ
    (Fintype.card α) le_rfl 130 (3*((Fintype.card α:ℝ)+2)) (by norm_num) (by positivity)
    hδ hmeshμ' hmeshcap' hmarkedmesh ηcoarse u₀ F₀ R₀ hu₀ η₀ Q hQM hQ hQt hQ72 (by
      intro T
      obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,SH,hSH,dh,KH,hKH,hcost⟩:=hhigh T
      refine ⟨P,he.symm,hPτ.trans hgτ.symm,SH,dh,KH,hKH.le,?_⟩
      filter_upwards [hcost Q hQM hQ72] with Z hz
      simpa only [mixed_high_spec_eq,mixed_high_target_eq,hgμ,hgδ] using hz.2)
  simpa only [hgμ] using hpaid

/-- The fixed-source main payment has no remaining analytic branch premise. -/
theorem actual_affine_main_uniform_paid_mixed_anchor
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)(hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh< Sil.Uneven.AuxiliarySource.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ SaturatedPlain.fineRawMesh*SaturatedPlain.fineRawCore)
    (hbΦ : 2≤ bΦ)
    :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤ M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec  M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  exact actual_affine_main_uniform_paid_of_fibers_mixed_anchor (α:=α) M H hH A hc hs Sbad hbad W hW hWs
    hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ εaffine mesh bΦ hε hεcap hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ
    (fun T=> OAI.SevenEighths.AuxiliaryHigh.geometry_affine_high_selected_fiber_receipt_mixed_anchor (α:=T) ηcoarse η₀ u₀ F₀ R₀ hu₀
      (geometryLossUnit 1 εaffine) (geometry_loss_unit_pos 1 εaffine (by norm_num) hε))

end
end OAI.SevenEighths.AuxiliaryHigh
end

/- Original module: Candidate.Uneven.MixedAuxiliaryFixedInitialSupplier. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.AuxiliaryAssembly
open CanonicalQuadraticSieve
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic ConcretePrimeRowBridge
open Cycle63InitialMass Cycle63MarkedPlain AuxiliaryReconstruction AuxiliaryPhysical
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The auxiliary source before specialization to the detector dictionary.
It applies to every fixed natural seed and its actual relative-slot anchor. -/
theorem fixed_natural_initial_affine_capped_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (ε mesh bΦ : ℝ) (hε : 0<ε) (hεcap : ε ≤ 1/10000000000000000000000000000)
    (hmesh0 : 0< mesh) (hmesh : mesh ≤ chosenMesh ε) (hbΦ : 2 ≤ bΦ) :
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε U (excluded F₀.character R₀) η₀ Q degree Sd C := by
  let η := excluded F₀.character R₀
  obtain ⟨hm0,hmcomp,hmcommon,hmmu,hmamp,hmmarked⟩:=chosen_mesh_admission ε hε
  have hmeshlt : mesh< Sil.Uneven.AuxiliarySource.amplifierMinimum/2:=hmesh.trans_lt hmamp
  have hmeshμ : mesh ≤ geometryLossUnit 1 (ε/4)/8:=hmesh.trans hmmu
  have hmeshcap : mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8):=
    hmesh.trans hmcommon
  have hmarkedmesh : mesh ≤ SaturatedPlain.fineRawMesh*SaturatedPlain.fineRawCore:=hmesh.trans hmmarked
  have hε4 : 0<ε/4 := by positivity
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=AuxiliaryHigh.actual_affine_main_uniform_paid_mixed_anchor (α:=α)
    M H hH 0 logAnnulus_compact logAnnulus_smooth Sbad hbad W hW hWs hβlo hβhi
    ηcoarse η₀ u₀ F₀ R₀ hu₀ (ε/4) mesh bΦ hε4 (by linarith) hmeshlt hmesh0.le
    hmeshμ hmeshcap hmarkedmesh hbΦ
  have hp:=hpaid Q hQM hQ0 hQt hQ72
  have herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0 ≤ (Ψ x).re) →
      ∀T : Finset α,∃Se : Finset (ℕ×ℕ),∃De : ℕ,∃Ce : ℝ,0 ≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          AuxiliaryErrorReconstruction.GeometryAffineErrorPaidSpec M H hH Sbad W hW.continuous hWs
            Ψ η η₀ mesh (ε/4) T Se De Ce Z := by
    intro Ψ _ _
    apply AuxiliaryErrorReconstruction.actual_affine_error_uniform_paid_of_normalized (α:=α)
      M H hH 0 logAnnulus_compact logAnnulus_smooth Sbad hbad W hW.continuous hWs Ψ η η₀
      (ε/4) mesh hε4 hmeshlt (internalQ Q η₀) hQ0 hQt hQ72
    exact AuxiliaryErrorReconstruction.actual_affine_error_normalized_family (α:=α) M H hH
      Sbad hbad W hW hWs hβlo AuxiliaryLow.incumbent_kappa_bound Ψ η η₀ Q hQM hQ0 hQt hQ72
      (ε/4) mesh hε4 hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := literal_affine_geometry_budget_of_main_error M H hH Sbad hbad W hW.continuous hWs
    η η₀ Q bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  exact literal_geometry_initial_affine (α:=α) M H hH W hW hWs η η₀ Q bΦ mesh ε τ
    (geometryLossUnit 1 (ε/4)/64) (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hmcomp) hβlo (by linarith) hQM hQ0 hQt hQ72
    logAnnulus_compact logAnnulus_smooth hbudget

theorem fixed_natural_initial_affine_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (ε mesh bΦ : ℝ) (hε : 0<ε) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ sourceMesh ε) (hbΦ : 2 ≤ bΦ) :
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε U (excluded F₀.character R₀) η₀ Q degree Sd C := by
  have hs:=capped_error_bounds hε
  obtain ⟨degree,Sd,C,hC,hev⟩:=fixed_natural_initial_affine_capped_mixed_anchor (α:=α) M H hH Sbad hbad W hW hWs
    hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72 (cappedError ε) mesh bΦ
    hs.1 hs.2.2 hmesh0 hmesh hbΦ
  refine ⟨degree,Sd,C,hC,?_⟩
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hu hU
  exact initial_affine_error_mono (α:=α) M H hH W 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (cappedError ε) ε U (excluded F₀.character R₀) η₀ Q degree Sd C hC.le hU hs.2.1 hu

end
end OAI.SevenEighths.AuxiliaryAssembly
end
