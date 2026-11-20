/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.RealBridge
import Candidate.C092.Intake.QRH.SourceEnvelope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Real length monotonicity for the high-response source tests

The certificate checks each high-response cost at the upper rational length
endpoint. This file transfers those costs to every real length in the same
source interval. It uses the actual piecewise source gain and proves the
monotonicity through its seam; it assumes no global convexity of that gain.
Analytic source admission and the separate low-response reduction remain open.
-/

set_option autoImplicit false
namespace QRH.SourceCertificate

noncomputable section

open QRH.Cycle090

/-- The rational gain in the finite checker equals the manuscript's real gain. -/
theorem gain_cast (y : ℚ) : (gain y : ℝ) = sourceGain (y : ℝ) := by
  have hseam : (seam : ℝ) = sourceSeam := by norm_num [seam, sourceSeam]
  have hu (z : ℚ) : (upperGain z : ℝ) = QRH.Cycle090.upperGain (z : ℝ) := by
    simp [upperGain, QRH.Cycle090.upperGain, Y, sourceY]
  by_cases hy : y < seam
  · have hyreal : (y : ℝ) < sourceSeam := by
      rw [←hseam]
      exact_mod_cast hy
    simp only [gain, ite_eq_left hy, sourceGain, ite_eq_right (not_le.mpr hyreal)]
    push_cast
    rw [hu, hseam]
    rfl
  · have hyreal : sourceSeam ≤ (y : ℝ) := by
      rw [←hseam]
      exact_mod_cast (le_of_not_gt hy)
    simp only [gain, ite_eq_right hy, sourceGain, ite_eq_left hyreal]
    exact hu y

/-- On the cubic branch, adding half the length makes the gain strictly increasing. -/
theorem upperHalfGain_strictMono : StrictMonoOn
    (fun y : ℝ => y/2 + QRH.Cycle090.upperGain y) (Set.Icc sourceSeam sourceY) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · unfold QRH.Cycle090.upperGain; fun_prop
  · intro y hy
    have hmem : y ∈ Set.Icc sourceSeam sourceY := interior_subset hy
    have hd := ((hasDerivAt_id y).div_const 2).add (upperGain_hasDerivAt y)
    change HasDerivAt (fun z : ℝ => z/2+QRH.Cycle090.upperGain z)
      (1/2+upperGainSlope y) y at hd
    rw [hd.deriv]
    linarith [(upperGain_slope_bounds hmem.1 hmem.2).1]

/-- On the quadratic branch, adding half the length makes the gain strictly increasing. -/
theorem lowerHalfGain_strictMono : StrictMonoOn
    (fun y : ℝ => y/2 + lowerGain y) (Set.Icc sourceY0 sourceSeam) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · unfold lowerGain; fun_prop
  · intro y hy
    have hmem : y ∈ Set.Icc sourceY0 sourceSeam := interior_subset hy
    have hd := ((hasDerivAt_id y).div_const 2).add (lowerGain_hasDerivAt y)
    change HasDerivAt (fun z : ℝ => z/2+lowerGain z) (1/2+lowerGainSlope y) y at hd
    rw [hd.deriv]
    linarith [(lowerGain_slope_bounds hmem.1 hmem.2).1]

/-- The joined real gain has the monotonicity needed for all high-response costs. -/
theorem halfGain_mono {y b : ℝ} (hy : sourceY0 ≤ y) (hyb : y ≤ b) (hb : b ≤ sourceY) :
    y/2+sourceGain y ≤ b/2+sourceGain b := by
  by_cases hys : sourceSeam ≤ y
  · have hbs := hys.trans hyb
    simpa only [sourceGain, ite_eq_left hys, ite_eq_left hbs] using
      upperHalfGain_strictMono.monotoneOn ⟨hys,hyb.trans hb⟩ ⟨hbs,hb⟩ hyb
  · by_cases hbs : sourceSeam ≤ b
    · have hl := lowerHalfGain_strictMono.monotoneOn
        ⟨hy,(le_of_not_ge hys)⟩ ⟨source_domain.2.1.le,le_rfl⟩ (le_of_not_ge hys)
      have hu := upperHalfGain_strictMono.monotoneOn
        ⟨le_rfl,source_domain.2.2.le⟩ ⟨hbs,hb⟩ hbs
      rw [source_seam_join] at hl
      simpa only [sourceGain, ite_eq_right hys, ite_eq_left hbs] using hl.trans hu
    · simpa only [sourceGain, ite_eq_right hys, ite_eq_right hbs] using
        lowerHalfGain_strictMono.monotoneOn
          ⟨hy,(le_of_not_ge hys)⟩ ⟨hy.trans hyb,(le_of_not_ge hbs)⟩ hyb

/-- The checker capacity extended to a genuine real source length. -/
def capacityAt (y : ℝ) : ℝ := 1/2-(H : ℝ)/4-y/2+sourceGain y-(u : ℝ)
/-- Short-inverse cost at a real length and response, with the certified quota. -/
def shortCostAt (y e : ℝ) (c : Cutoff) : ℝ :=
  e*(y+capacityAt y-(H : ℝ)*((c.inverse : ℝ)+(quota c.inverse c.rootUpper : ℝ))/2)
/-- Long-inverse cost at a real length and response. -/
def longCostAt (y e : ℝ) (c : Cutoff) : ℝ :=
  e*(y+capacityAt y)-(H : ℝ)*((5/6)-((5/6)-e)*((c.inverse : ℝ)+(c.ordinary : ℝ)))/2
/-- Ordinary-substitution cost at a real length, including its positive part. -/
def ordinaryCostAt (y e : ℝ) (c : Cutoff) : ℝ :=
  let delta := (H : ℝ)*(c.ordinary : ℝ)-y
  e*(-delta+max 0 (2*(u : ℝ)+delta/2+sourceGain y-
    (H : ℝ)*(ordinaryGain c.ordinary : ℝ)))
/-- All three certified conservative costs are paid at a real length and response. -/
def PaidAt (y e : ℝ) (c : Cutoff) : Prop :=
  shortCostAt y e c < (u-rho : ℚ) ∧ longCostAt y e c < (u-rho : ℚ) ∧
    ordinaryCostAt y e c < (u-rho : ℚ)

/-- At rational lengths, the real-length capacity is the literal checked capacity. -/
theorem capacityAt_rat (b : ℚ) : capacityAt (b : ℝ) = (capacity b : ℝ) := by
  simp [capacityAt, capacity, gain_cast]

/-- Payment at a rational length is unchanged by the real-length extension. -/
theorem paidAt_rat (b : ℚ) (e : ℝ) (c : Cutoff) :
    PaidAt (b : ℝ) e c ↔ EndpointPaidReal b e c := by
  simp [PaidAt, EndpointPaidReal, shortCostAt, shortCostReal, longCostAt, longCostReal,
    ordinaryCostAt, ordinaryCostReal, capacityAt_rat, gain_cast]

/-- The common length-and-capacity base increases throughout the source interval. -/
theorem length_capacity_mono {y b : ℝ} (hy : sourceY0 ≤ y) (hyb : y ≤ b) (hb : b ≤ sourceY) :
    y+capacityAt y ≤ b+capacityAt b := by
  have hg := halfGain_mono hy hyb hb
  unfold capacityAt
  linarith

/-- The ordinary positive-part expression is the maximum of two increasing expressions. -/
theorem ordinaryCostAt_eq_max (y e : ℝ) (c : Cutoff) :
    ordinaryCostAt y e c = e*max
      (y-(H : ℝ)*(c.ordinary : ℝ))
      (y/2+sourceGain y+2*(u : ℝ)-(H : ℝ)*(c.ordinary : ℝ)/2-
        (H : ℝ)*(ordinaryGain c.ordinary : ℝ)) := by
  unfold ordinaryCostAt
  dsimp only
  rw [add_max]
  congr 2 <;> ring

/-- Upper-endpoint payment transfers to every smaller real source length. -/
theorem paidAt_mono_length {y b e : ℝ} (c : Cutoff)
    (hy : sourceY0 ≤ y) (hyb : y ≤ b) (hb : b ≤ sourceY) (he : 0 ≤ e)
    (hpaid : PaidAt b e c) : PaidAt y e c := by
  have hbase := length_capacity_mono hy hyb hb
  have hhalf := halfGain_mono hy hyb hb
  refine ⟨?_,?_,?_⟩
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (sub_le_sub_right hbase _) he) hpaid.1
  · have hmul := mul_le_mul_of_nonneg_left hbase he
    exact lt_of_le_of_lt (sub_le_sub_right hmul _) hpaid.2.1
  · have hmax : max (y-(H : ℝ)*(c.ordinary : ℝ))
        (y/2+sourceGain y+2*(u : ℝ)-(H : ℝ)*(c.ordinary : ℝ)/2-
          (H : ℝ)*(ordinaryGain c.ordinary : ℝ)) ≤
      max (b-(H : ℝ)*(c.ordinary : ℝ))
        (b/2+sourceGain b+2*(u : ℝ)-(H : ℝ)*(c.ordinary : ℝ)/2-
          (H : ℝ)*(ordinaryGain c.ordinary : ℝ)) :=
      max_le_max (by linarith) (by linarith)
    have hupper := hpaid.2.2
    rw [ordinaryCostAt_eq_max] at hupper ⊢
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmax he) hupper

/-- The same recorded inverse/ordinary cutoff supports every smaller real length. -/
theorem cutoff_support_mono {y : ℝ} {b : ℚ} {c : Cutoff}
    (hyb : y ≤ (b : ℝ)) (hguard : CutoffGuard b c) :
    2*y/(H : ℝ) ≤ (c.inverse : ℝ) ∧ y/(H : ℝ) ≤ (c.ordinary : ℝ) ∧
      y < (H : ℝ)*((c.inverse : ℝ)+(c.ordinary : ℝ))/2 := by
  have hH : (0 : ℝ) < (H : ℝ) := by norm_num [H,u]
  have h₁ : 2*(b : ℝ)/(H : ℝ) ≤ (c.inverse : ℝ) := by exact_mod_cast hguard.1
  have h₂ : (b : ℝ)/(H : ℝ) ≤ (c.ordinary : ℝ) := by exact_mod_cast hguard.2.1
  have h₃ : (b : ℝ) < (H : ℝ)*((c.inverse : ℝ)+(c.ordinary : ℝ))/2 := by
    exact_mod_cast hguard.2.2.1
  exact ⟨(div_le_div_of_nonneg_right (by linarith) hH.le).trans h₁,
    (div_le_div_of_nonneg_right hyb hH.le).trans h₂, hyb.trans_lt h₃⟩

/-- Each accepted cell pays every real high response at every real source length
in that cell, using one of the actual eight simultaneous cutoffs. -/
theorem cellCheck_real_length_response (c : Cell) (h : cellCheck c = true) {y e : ℝ}
    (hyl : (c.lower : ℝ) ≤ y) (hyu : y ≤ (c.upper : ℝ))
    (hel : (c.threshold : ℝ) ≤ e) (heu : e ≤ (responseUpper : ℝ)) :
    ∃ p ∈ c.cutoffs.zipIdx, CutoffGuard c.upper p.1 ∧ PaidAt y e p.1 ∧
      2*y/(H : ℝ) ≤ (p.1.inverse : ℝ) ∧ y/(H : ℝ) ≤ (p.1.ordinary : ℝ) ∧
        y < (H : ℝ)*((p.1.inverse : ℝ)+(p.1.ordinary : ℝ))/2 := by
  have hraw := h
  simp only [cellCheck, Bool.and_eq_true] at hraw
  obtain ⟨hlo, _, hupper, _, _, hthreshold, _, _⟩ := of_decide_eq_true hraw.1.1
  have hy : sourceY0 ≤ y := by
    have hh : (369/1000 : ℝ) ≤ (c.lower : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hlo
    exact hh.trans hyl
  have hb : (c.upper : ℝ) ≤ sourceY := by
    simpa [Y,sourceY] using (Rat.cast_le (K := ℝ)).mpr hupper
  have he : 0 ≤ e := by
    have hh : (19/50 : ℝ) < (c.threshold : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hthreshold
    linarith
  obtain ⟨p,hp,hg,hpaid⟩ := cellCheck_high_response c h hel heu
  exact ⟨p,hp,hg,paidAt_mono_length p.1 hy hyu hb he ((paidAt_rat _ _ _).mpr hpaid),
    cutoff_support_mono hyu hg⟩

end

end QRH.SourceCertificate
