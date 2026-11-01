/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.SourceParameters (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Public
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Data
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalFront
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators
open Filter
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open OAI OAI.SevenEighths Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect HeckeFamily

lemma source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤ a) (hatop : a≤7/8) :
    0≤(2*a-1)/2 ∧ (2*a-1)/2≤1 ∧
    1-a-6*D.e≤1/2-(2*a-1)/2 ∧
    -(1/100:ℝ)≤1/2-(2*a-1)/2 ∧
    1+4*D.e≤(a+16*D.e)+(1/2-(2*a-1)/2) := by
  have he:=D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

lemma source_complex_profile_norm (D : BaselineData) (F : BaselineSourceData D) (r : ℝ) :
    ‖F.W r‖≤1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded r).1]
  exact (F.bounded r).2

lemma source_cutoff_le_base (b : ℝ) (hb : 0≤ b) :
    ∀ᶠU:ℝ in atTop,1< U ∧ ∀d:ℝ,(1/2:ℝ)≤ d → b*U^(y/d)≤ U := by
  have he : ∀ᶠU:ℝ in atTop,b≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0< d:=by linarith
  have hy : y/d≤19/20 := by
    apply (div_le_iff₀ hdp).mpr
    have hy : y≤19/40:=by linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ly_coarse.1,Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN.ly_coarse.2]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
