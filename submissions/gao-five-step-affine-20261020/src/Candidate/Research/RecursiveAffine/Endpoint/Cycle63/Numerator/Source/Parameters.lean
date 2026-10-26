/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Numerator.Source.ActualBin
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Numerator.Fourth.Public
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.NumeratorPhysicalFront

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Numerator_Source_Parameters : Cycle63.AffineLedger := Cycle153.Root.rootLedger


noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle153Endpoint.Numerator.Source
open Cycle153Endpoint.Arithmetic
open OAI OAI.SevenEighths Cycle153EndpointDetectorCount HeckeFamily

lemma source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤a) (hatop : a≤7/8) :
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

lemma source_cutoff_le_base (b : ℝ) (_hb : 0≤b) :
    ∀ᶠU:ℝ in atTop,1<U ∧ ∀d:ℝ,(1/2:ℝ)≤d → b*U^(y/d)≤U := by
  have he : ∀ᶠU:ℝ in atTop,b≤U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0<d:=by linarith
  have hy : y/d≤19/20 := by
    apply (div_le_iff₀ hdp).mpr
    have hy : y≤19/40:=y_le
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end Cycle153Endpoint.Numerator.Source
