/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target836.Num836.Source.ActualBin
import Candidate.Target836.Num836.Fourth.Public
import Candidate.Cycle25.Numerator.PhysicalFront

noncomputable section
open scoped Classical BigOperators
open Filter
namespace Target836.Numerator.Source
open Target836.Arithmetic
open OAI OAI.SevenEighths Target836DetectorCount HeckeFamily

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
    have hy : y≤19/40:=by norm_num [y]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end Target836.Numerator.Source

#print axioms Target836.Numerator.Source.source_packet_lines
#print axioms Target836.Numerator.Source.source_complex_profile_norm
#print axioms Target836.Numerator.Source.source_cutoff_le_base
