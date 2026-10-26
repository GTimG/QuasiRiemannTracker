/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.Public
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.Data
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.PhysicalFront
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators
open Filter
namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect.Source
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RH20261023Return.GenericArithmetic
open QRH.RH20261023Return.GenericArithmetic
open OAI OAI.SevenEighths QRH.RH20261023Return.GenericPhysical.PhysicalDirect HeckeFamily

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
    have hy : y≤19/40:=by linarith [Geometry.Bounds.ly_coarse.1,Geometry.Bounds.ly_coarse.2]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect.Source

#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.Source.source_packet_lines
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.Source.source_complex_profile_norm
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.Source.source_cutoff_le_base
