/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.LengthBridge

/-!
# Real low-response continuum reduction

For the literal P1 source, the low-response replacement bracket decreases
below the displaced seam, increases from the displaced seam to the source
seam, and decreases above the source seam. A cell does not cross the source
seam. Consequently its two checked endpoints bound every real interior point.
This is a scalar theorem about the actual source polynomial, not an assertion
of analytic source admission.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.SourceCertificate

noncomputable section

open QRH.Cycle090

/-- The true low-response replacement bracket at a real source length. -/
def lowBracketAt (y : ℝ) : ℝ := 2*(u : ℝ)+sourceGain y-(H : ℝ)*sourceGain (y/(H : ℝ))
/-- A scaled difference of two smooth source branches. -/
def scaledDifference (f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  2*(u : ℝ)+f y-(H : ℝ)*g (y/(H : ℝ))

/-- The regular-core ratio is positive and strictly below one. -/
theorem H_real_bounds : (0 : ℝ) < (H : ℝ) ∧ (H : ℝ) < 1 := by norm_num [H,u]

/-- Both source branches have the same value at the seam, allowing closed intervals. -/
theorem sourceGain_eq_lower {y : ℝ} (hy : y ≤ sourceSeam) : sourceGain y = lowerGain y := by
  by_cases h : sourceSeam ≤ y
  · have heq : y = sourceSeam := le_antisymm hy h
    subst y
    simp [sourceGain, source_seam_join]
  · simp [sourceGain, h]

/-- The literal rational low test evaluates to the same real bracket. -/
theorem lowBracket_cast (y : ℚ) : (lowBracket y : ℝ) = lowBracketAt (y : ℝ) := by
  simp [lowBracket, lowBracketAt, gain_cast]

/-- Differentiation cancels the regular-core scaling exactly. -/
theorem scaledDifference_hasDerivAt {f g : ℝ → ℝ} {df dg y : ℝ}
    (hf : HasDerivAt f df y) (hg : HasDerivAt g dg (y/(H : ℝ))) :
    HasDerivAt (scaledDifference f g) (df-dg) y := by
  have hH : (H : ℝ) ≠ 0 := H_real_bounds.1.ne'
  have hd := (hf.sub ((hg.comp y ((hasDerivAt_id y).div_const (H : ℝ))).const_mul
    (H : ℝ))).const_add (2*(u : ℝ))
  convert hd using 1
  · funext z
    simp only [scaledDifference, Pi.sub_apply, Function.comp_apply, id_eq]
    ring
  · field_simp

/-- With both arguments on the lower branch, the bracket strictly decreases. -/
theorem lowLower_strictAnti : StrictAntiOn (scaledDifference lowerGain lowerGain)
    (Set.Icc sourceY0 ((H : ℝ)*sourceSeam)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · unfold scaledDifference lowerGain; fun_prop
  · intro y hy
    have hm : y ∈ Set.Icc sourceY0 ((H : ℝ)*sourceSeam) := interior_subset hy
    rw [(scaledDifference_hasDerivAt (lowerGain_hasDerivAt y)
      (lowerGain_hasDerivAt (y/(H : ℝ)))).deriv]
    norm_num [lowerGainSlope, H,u, sourceY0] at hm ⊢
    linarith [hm.1]

/-- Between the displaced seam and the source seam, the bracket strictly increases. -/
theorem lowMixed_strictMono : StrictMonoOn
    (scaledDifference lowerGain QRH.Cycle090.upperGain)
    (Set.Icc ((H : ℝ)*sourceSeam) sourceSeam) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · unfold scaledDifference lowerGain QRH.Cycle090.upperGain; fun_prop
  · intro y hy
    have hm : y ∈ Set.Icc ((H : ℝ)*sourceSeam) sourceSeam := interior_subset hy
    rw [(scaledDifference_hasDerivAt (lowerGain_hasDerivAt y)
      (upperGain_hasDerivAt (y/(H : ℝ)))).deriv]
    norm_num [lowerGainSlope, upperGainSlope, H,u, sourceSeam, sourceY] at hm ⊢
    nlinarith [sq_nonneg (y-747/2000)]

/-- With both arguments on the upper branch, the bracket strictly decreases,
including the small continuation beyond the native source endpoint. -/
theorem lowUpper_strictAnti : StrictAntiOn
    (scaledDifference QRH.Cycle090.upperGain QRH.Cycle090.upperGain)
    (Set.Icc sourceSeam sourceY) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · unfold scaledDifference QRH.Cycle090.upperGain; fun_prop
  · intro y hy
    have hm : y ∈ Set.Icc sourceSeam sourceY := interior_subset hy
    rw [(scaledDifference_hasDerivAt (upperGain_hasDerivAt y)
      (upperGain_hasDerivAt (y/(H : ℝ)))).deriv]
    have hypos : 0 ≤ y := by norm_num [sourceSeam] at hm; linarith [hm.1]
    have hprod := mul_nonneg hypos (sub_nonneg.mpr hm.2)
    norm_num [upperGainSlope, H,u, sourceSeam, sourceY] at hm hprod ⊢
    nlinarith

/-- The real bracket equals its lower-branch expression below the displaced seam. -/
theorem lowBracketAt_lower {y : ℝ} (hy : y ≤ (H : ℝ)*sourceSeam) :
    lowBracketAt y = scaledDifference lowerGain lowerGain y := by
  have hs : (H : ℝ)*sourceSeam ≤ sourceSeam := by
    exact mul_le_of_le_one_left (by norm_num [sourceSeam]) H_real_bounds.2.le
  have hyH : y/(H : ℝ) ≤ sourceSeam := (div_le_iff₀ H_real_bounds.1).mpr (by linarith)
  simp [lowBracketAt, scaledDifference, sourceGain_eq_lower (hy.trans hs), sourceGain_eq_lower hyH]

/-- The real bracket equals its mixed-branch expression between the two seams. -/
theorem lowBracketAt_mixed {y : ℝ} (hy₀ : (H : ℝ)*sourceSeam ≤ y) (hy₁ : y ≤ sourceSeam) :
    lowBracketAt y = scaledDifference lowerGain QRH.Cycle090.upperGain y := by
  have hyH : sourceSeam ≤ y/(H : ℝ) := (le_div_iff₀ H_real_bounds.1).mpr (by linarith)
  unfold lowBracketAt scaledDifference
  rw [sourceGain_eq_lower hy₁]
  simp only [sourceGain, ite_eq_left hyH]

/-- The real bracket equals its upper-branch expression above the source seam. -/
theorem lowBracketAt_upper {y : ℝ} (hy : sourceSeam ≤ y) :
    lowBracketAt y = scaledDifference QRH.Cycle090.upperGain QRH.Cycle090.upperGain y := by
  have hyH : sourceSeam ≤ y/(H : ℝ) := by
    apply (le_div_iff₀ H_real_bounds.1).mpr
    simpa only [mul_comm] using
      (mul_le_of_le_one_left (by norm_num [sourceSeam]) H_real_bounds.2.le).trans hy
  simp [lowBracketAt, scaledDifference, sourceGain, ite_eq_left hy, ite_eq_left hyH]

/-- Every real point in a cell not crossing the source seam is bounded by one
of that cell's two endpoint low brackets. -/
theorem lowBracketAt_endpoint_bound {a b y : ℝ}
    (ha : sourceY0 ≤ a) (hb : b ≤ sourceY) (hay : a ≤ y) (hyb : y ≤ b)
    (hseam : ¬(a < sourceSeam ∧ sourceSeam < b)) :
    lowBracketAt y ≤ lowBracketAt a ∨ lowBracketAt y ≤ lowBracketAt b := by
  by_cases has : sourceSeam ≤ a
  · left
    rw [lowBracketAt_upper (has.trans hay), lowBracketAt_upper has]
    exact lowUpper_strictAnti.antitoneOn ⟨has,(hay.trans hyb).trans hb⟩
      ⟨has.trans hay,hyb.trans hb⟩ hay
  · have hbs : b ≤ sourceSeam := by
      by_contra h
      exact hseam ⟨lt_of_not_ge has,lt_of_not_ge h⟩
    by_cases hyd : y ≤ (H : ℝ)*sourceSeam
    · left
      rw [lowBracketAt_lower hyd, lowBracketAt_lower (hay.trans hyd)]
      exact lowLower_strictAnti.antitoneOn ⟨ha,hay.trans hyd⟩ ⟨ha.trans hay,hyd⟩ hay
    · right
      have hdy := le_of_not_ge hyd
      rw [lowBracketAt_mixed hdy (hyb.trans hbs), lowBracketAt_mixed (hdy.trans hyb) hbs]
      exact lowMixed_strictMono.monotoneOn ⟨hdy,hyb.trans hbs⟩ ⟨hdy.trans hyb,hbs⟩ hyb

/-- An accepted cell pays every real low response at every real length in it. -/
theorem cellCheck_low_real (c : Cell) (h : cellCheck c = true) {y e : ℝ}
    (hyl : (c.lower : ℝ) ≤ y) (hyu : y ≤ (c.upper : ℝ))
    (he : 0 ≤ e) (hek : e ≤ (c.threshold : ℝ)) :
    e*lowBracketAt y < (u-rho : ℚ) := by
  have hraw := h
  simp only [cellCheck, Bool.and_eq_true] at hraw
  obtain ⟨hlo, _, hupper, _, hseam, _, _, _⟩ := of_decide_eq_true hraw.1.1
  have ha : sourceY0 ≤ (c.lower : ℝ) := by
    simpa [sourceY0] using (Rat.cast_le (K := ℝ)).mpr hlo
  have hb : (c.upper : ℝ) ≤ sourceY := by
    simpa [sourceY,Y] using (Rat.cast_le (K := ℝ)).mpr hupper
  have hs : ¬((c.lower : ℝ) < sourceSeam ∧ sourceSeam < (c.upper : ℝ)) := by
    have hsc : sourceSeam = (seam : ℝ) := by norm_num [sourceSeam,seam]
    rw [hsc]
    intro hcross
    exact hseam ⟨(Rat.cast_lt (K := ℝ)).mp hcross.1, (Rat.cast_lt (K := ℝ)).mp hcross.2⟩
  have hk : (0 : ℝ) ≤ (c.threshold : ℝ) := he.trans hek
  have hl := (cellCheck_sound c h).1
  have hu := (cellCheck_sound c h).2.1
  have hleft : (c.threshold : ℝ)*lowBracketAt (c.lower : ℝ) < (u-rho : ℚ) := by
    rw [←lowBracket_cast]
    exact_mod_cast hl
  have hright : (c.threshold : ℝ)*lowBracketAt (c.upper : ℝ) < (u-rho : ℚ) := by
    rw [←lowBracket_cast]
    exact_mod_cast hu
  have hpaid : (c.threshold : ℝ)*lowBracketAt y < (u-rho : ℚ) := by
    rcases lowBracketAt_endpoint_bound ha hb hyl hyu hs with hy | hy
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy hk) hleft
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hy hk) hright
  by_cases hB : 0 ≤ lowBracketAt y
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hek hB) hpaid
  · have hnonpos : e*lowBracketAt y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he (le_of_not_ge hB)
    have hreserve : (0 : ℝ) < (u-rho : ℚ) := by norm_num [u,rho]
    exact hnonpos.trans_lt hreserve

/-- The manuscript's actual positive-part low cost is paid throughout the cell. -/
theorem cellCheck_low_positive_part (c : Cell) (h : cellCheck c = true) {y e : ℝ}
    (hyl : (c.lower : ℝ) ≤ y) (hyu : y ≤ (c.upper : ℝ))
    (he : 0 ≤ e) (hek : e ≤ (c.threshold : ℝ)) :
    e*max 0 (lowBracketAt y) < (u-rho : ℚ) := by
  by_cases hB : 0 ≤ lowBracketAt y
  · simpa only [max_eq_right hB] using cellCheck_low_real c h hyl hyu he hek
  · rw [max_eq_left (le_of_not_ge hB), mul_zero]
    norm_num [u,rho]

end

end QRH.SourceCertificate
