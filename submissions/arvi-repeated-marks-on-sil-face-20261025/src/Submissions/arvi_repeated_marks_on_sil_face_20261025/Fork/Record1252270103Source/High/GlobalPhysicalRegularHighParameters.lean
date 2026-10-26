/- Repeated marks: fork of Record1252270103Source.High.GlobalPhysicalRegularHighParameters (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularHighParameters
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Admission.SelectedRegularHighSourceSome
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed pre-slot loss and post-cardinality buffer instantiate the actual
HIGH source with one consistent set of numerical geometry budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Admission
local notation "O"=>HeckeFamily.O
variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
variable (hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (reserve θ mesh amp:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (hm:0≤mesh)(hmesh:100*mesh≤θ)(hamp:0<amp)
variable (R₀:Ideal O)(hR₀:R₀≠0)
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)

/-- This is a proof-valued specialization of the actual Some-source theorem.
The inferred result retains its exact quantified FamilyStatement. -/
def regular_some_source_rm (high:Source)
    (hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ) :=
  SelectedRegularHighSourceSome.actual_selected_regular_high_source_uniform_tau_rm M H hH (α:=α)
    ηanchor η₀ n low high (100*mesh) hB0 hB1 hlam hcap0 hcap1 setup W
    bRad θ θ θ θ (1/100) 100 rmin 1 θ (highBuffer 1 1 εslot (θ/16))
    (highKappa εslot (θ/16)) (θ/16) εslot (εslot/4)
    (bufferCount (highBuffer 1 1 εslot (θ/16))) le_rfl θ 33 1 wmin hf.positive
    (by norm_num) (by norm_num) hc.wmin_pos hparent hWs hW hbRad hrad
    hf.positive hf.positive hf.positive hf.positive (by norm_num) (by norm_num) hc.rmin_pos (by norm_num)
    hf.positive (hf.small.trans (by norm_num)) hc.buffer_pos hc.buffer_small hc.kappa_pos hc.kappa_le_one
    (div_nonneg hf.positive.le (by norm_num)) hc.density_budget hc.slot_pos (div_nonneg hc.slot_pos.le (by norm_num)) hc.slot_budget hc.slot_gap hβ
    (1/50) 2 (100*mesh) (by norm_num) (by norm_num) (by norm_num)
    (by linarith only [hf.positive]) (by linarith only [hf.small]) hc.live_lower
    (mul_nonneg (by norm_num) hm) le_rfl (hmesh.trans (hf.small.trans (by norm_num)))
    6 θ (by norm_num) (by norm_num) hf.positive 1 (θ/100) (by norm_num) (div_nonneg hf.positive.le (by norm_num))
    1 (1/4) (9/4) θ 2 (by norm_num) hf.positive (by norm_num) N θ hf.positive
    2 2 θ (amp/2) (lowerFactor N 1 (1/4)) 32 θ (by norm_num) (by norm_num) hf.positive
    (div_pos hamp (by norm_num)) (lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)) (by norm_num)
    R₀ hR₀ θ 2 1 1 1 hf.positive (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [SelectedSecondKeyCaps.coarseExponent]) le_rfl le_rfl hβhi

end
end QRH.Record1252270103Source.High.GlobalPhysical
