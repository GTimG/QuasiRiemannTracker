/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SilPrice
import Candidate.Local.Qrh.JointDetector.JointPriceCount

/-!
# Refined joint-detector price

Scalar refinement with retained slope `k(nu)-17/200`, cutoff `500001/1000000`,
and reserve `1/250`. This constructs Sil's actual global `Price` object.
It asserts neither a selected norm, an analytic count nor a packed supplier.
Only the actual sextic feature and its conjugate can supply those analytic
inputs; no assertion about arbitrary powers of natural row features is made.
-/

namespace Qrh.JointDetector.FineRefinedPrice
noncomputable section


/-- The inherited zero-density gap. -/
def k (ν : ℝ) : ℝ := 10 * ν / (15 - 6 * ν)

/-- The retained slot slope supplied by the three detector polynomials. -/
def retainedSlope (ν : ℝ) : ℝ := k ν - 17 / 200

/-- The second envelope slope of the globally extended HIGH price. -/
def extendedMSlope (ν : ℝ) : ℝ := k ν + (ν - k ν + 17 / 200) / 10

theorem k_den_pos {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < 15 - 6 * ν := by
  linarith [hν.2]

theorem k_range {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (65/111 : ℝ) ≤ k ν ∧ k ν ≤ 5/7 := by
  have hd := k_den_pos hν
  constructor
  · rw [k, le_div_iff₀ hd]
    linarith [hν.1]
  · rw [k, div_le_iff₀ hd]
    linarith [hν.2]

theorem k_le_nu {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    k ν ≤ ν := by
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hp : 0 ≤ 5 - 6 * ν := by linarith [hν.2]
  rw [k, div_le_iff₀ (k_den_pos hν)]
  nlinarith [mul_nonneg hn hp]

theorem retainedSlope_bounds {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (11113/22200 : ℝ) ≤ retainedSlope ν ∧ retainedSlope ν ≤ ν := by
  have hk := k_range hν
  have hkn := k_le_nu hν
  dsimp [retainedSlope]
  constructor <;> linarith

theorem retainedSlope_pos {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < retainedSlope ν := by
  linarith [(retainedSlope_bounds hν).1]

theorem extensionCoeff_pos {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < ν - k ν + 17/200 := by
  linarith [k_le_nu hν]

theorem extendedMSlope_bounds {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 ≤ extendedMSlope ν ∧ extendedMSlope ν ≤ 10169/14000 := by
  have hk := k_range hν
  have he := extensionCoeff_pos hν
  dsimp [extendedMSlope]
  constructor <;> linarith [hν.2]

/-- The global HIGH summand, defined even at negative widths and envelopes. -/
def g (ν P s M : ℝ) : ℝ :=
  ν * P - k ν * M + retainedSlope ν * s +
    (ν - k ν + 17/200) * max (s - M/10) 0

/-- This affine maximum is valid for every real `P`, `s` and `M`. -/
theorem g_eq_max {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M : ℝ) :
    g ν P s M = max
      (ν * P - k ν * M + retainedSlope ν * s)
      (ν * P - extendedMSlope ν * M + ν * s) := by
  have hc := (extensionCoeff_pos hν).le
  by_cases hs : s - M/10 ≤ 0
  · rw [g, max_eq_right hs, mul_zero, add_zero, max_eq_left]
    dsimp [retainedSlope, extendedMSlope]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hs]
  · have hs' : 0 ≤ s - M/10 := (le_of_not_ge hs)
    rw [g, max_eq_left hs', max_eq_right]
    · dsimp [retainedSlope, extendedMSlope]
      ring
    · dsimp [retainedSlope, extendedMSlope]
      nlinarith [mul_nonneg hc hs']

private theorem max_le_max_add {a b a' b' e : ℝ}
    (ha : a' ≤ a + e) (hb : b' ≤ b + e) :
    max a' b' ≤ max a b + e := by
  apply max_le
  · linarith [le_max_left a b]
  · linarith [le_max_right a b]

private theorem linear_increment_le {a L : ℝ} (ha : |a| ≤ L) (δ : ℝ) :
    a * δ ≤ L * |δ| := by
  calc
    a * δ ≤ |a * δ| := le_abs_self _
    _ = |a| * |δ| := abs_mul _ _
    _ ≤ L * |δ| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)

theorem g_mono {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    g ν P' s' M ≤ g ν P s M := by
  rw [g_eq_max hν, g_eq_max hν]
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hκ := (retainedSlope_pos hν).le
  apply max_le_max
  · linarith [mul_le_mul_of_nonneg_left hP hn,
      mul_le_mul_of_nonneg_left hs hκ]
  · linarith [mul_le_mul_of_nonneg_left hP hn,
      mul_le_mul_of_nonneg_left hs hn]

/-- Arbitrary real ordinary-width increments, including negative increments. -/
theorem g_lipP_all {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν (P + δ) s M ≤ g ν P s M + (3/4 : ℝ) * |δ| := by
  have hn : 0 ≤ ν := by linarith [hν.1]
  have ha : |ν| ≤ (3/4 : ℝ) := by simpa only [abs_of_nonneg hn] using hν.2
  have hδ := linear_increment_le ha δ
  have he : g ν (P + δ) s M = g ν P s M + ν * δ := by
    dsimp [g]
    ring
  rw [he]
  linarith

/-- Arbitrary real slot-width increments, including negative increments. -/
theorem g_lipS_all {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν P (s + δ) M ≤ g ν P s M + (3/4 : ℝ) * |δ| := by
  rw [g_eq_max hν, g_eq_max hν]
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hκ := retainedSlope_bounds hν
  have ha : |ν| ≤ (3/4 : ℝ) := by simpa only [abs_of_nonneg hn] using hν.2
  have hb : |retainedSlope ν| ≤ (3/4 : ℝ) := by
    rw [abs_of_nonneg (retainedSlope_pos hν).le]
    exact hκ.2.trans hν.2
  apply max_le_max_add
  · linarith [linear_increment_le hb δ]
  · linarith [linear_increment_le ha δ]

/-- The ordinary-width field of the generic `Price` interface. -/
theorem g_lipP {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    g ν (P + δ) s M ≤ g ν P s M + (3/4 : ℝ) * δ := by
  simpa only [abs_of_nonneg hδ] using g_lipP_all hν P s M δ

/-- The slot-width field of the generic `Price` interface. -/
theorem g_lipS {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    g ν P (s + δ) M ≤ g ν P s M + (3/4 : ℝ) * δ := by
  simpa only [abs_of_nonneg hδ] using g_lipS_all hν P s M δ

/-- The envelope field has the exact global bound `10169/14000`, for either sign. -/
theorem g_lipM {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν P s (M + δ) ≤ g ν P s M + (10169/14000 : ℝ) * |δ| := by
  rw [g_eq_max hν, g_eq_max hν]
  have hk := k_range hν
  have hm := extendedMSlope_bounds hν
  have ha : |-k ν| ≤ (10169/14000 : ℝ) := by
    rw [abs_neg, abs_of_nonneg (by linarith [hk.1])]
    linarith [hk.2]
  have hb : |-extendedMSlope ν| ≤ (10169/14000 : ℝ) := by
    rw [abs_neg, abs_of_nonneg hm.1]
    exact hm.2
  apply max_le_max_add
  · linarith [linear_increment_le ha δ]
  · linarith [linear_increment_le hb δ]

/-- A bound uniform in the density parameter; no width has a sign restriction. -/
theorem g_upper_bound {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M : ℝ) :
    g ν P s M ≤ (3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (10169/14000 : ℝ) * |M| := by
  have hP := g_lipP_all hν 0 s M P
  have hs := g_lipS_all hν 0 0 M s
  have hM := g_lipM hν 0 0 0 M
  have hz : g ν 0 0 0 = 0 := by simp [g]
  simp only [zero_add] at hP hs hM
  linarith

/-- The HIGH price on a closed density interval. Clipping supplies its hypotheses. -/
def highSup (q P s M : ℝ) : ℝ :=
  ⨆ ν : Set.Icc q (3/4 : ℝ), g ν P s M

theorem highSup_bdd {q : ℝ} (hq : (13/20 : ℝ) ≤ q) (P s M : ℝ) :
    BddAbove (Set.range fun ν : Set.Icc q (3/4 : ℝ) => g ν P s M) := by
  refine ⟨(3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (10169/14000 : ℝ) * |M|, ?_⟩
  rintro _ ⟨ν, rfl⟩
  exact g_upper_bound ⟨hq.trans ν.2.1, ν.2.2⟩ P s M

theorem le_highSup {q ν : ℝ} (hq : (13/20 : ℝ) ≤ q)
    (hν : q ≤ ν) (hν' : ν ≤ 3/4) (P s M : ℝ) :
    g ν P s M ≤ highSup q P s M := by
  exact le_ciSup (f := fun ν : Set.Icc q (3/4 : ℝ) => g ν P s M)
    (highSup_bdd hq P s M) ⟨ν, hν, hν'⟩

theorem highSup_le {q P s M a : ℝ} (hq : q ≤ (3/4 : ℝ))
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → g ν P s M ≤ a) :
    highSup q P s M ≤ a := by
  have : Nonempty (Set.Icc q (3/4 : ℝ)) := ⟨⟨3/4, hq, le_rfl⟩⟩
  exact ciSup_le fun ν => h ν ν.2.1 ν.2.2

theorem highSup_mono {q : ℝ} (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4))
    {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    highSup q P' s' M ≤ highSup q P s M := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_mono ⟨hq.1.trans hν, hν'⟩ hP hs).trans
    (le_highSup hq.1 hν hν' P s M)

theorem highSup_lipP {q : ℝ} (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highSup q (P + δ) s M ≤ highSup q P s M + (3/4 : ℝ) * δ := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipP ⟨hq.1.trans hν, hν'⟩ P s M δ hδ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

theorem highSup_lipS {q : ℝ} (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highSup q P (s + δ) M ≤ highSup q P s M + (3/4 : ℝ) * δ := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipS ⟨hq.1.trans hν, hν'⟩ P s M δ hδ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

theorem highSup_lipM {q : ℝ} (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) :
    highSup q P s (M + δ) ≤ highSup q P s M + (10169/14000 : ℝ) * |δ| := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipM ⟨hq.1.trans hν, hν'⟩ P s M δ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

theorem witnessDen_pos {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    0 < witnessDen ν δ := by
  dsimp [witnessDen]
  linarith [hν.2, hδ.2]

theorem mStar_pos {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    0 < mStar ν δ := by
  exact div_pos (by linarith [hν.2, hδ.2]) (witnessDen_pos hν hδ)

theorem lStar_le_one {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    lStar ν δ ≤ 1 := by
  have hd := witnessDen_pos hν hδ
  unfold lStar mStar
  rw [← mul_div_assoc, div_le_iff₀ hd]
  dsimp [witnessDen]
  linarith [hν.2]

theorem one_le_hStar {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    1 ≤ hStar ν δ := by
  have hd := witnessDen_pos hν hδ
  unfold hStar mStar
  rw [← mul_div_assoc, le_div_iff₀ hd]
  dsimp [witnessDen]
  linarith [hδ.2]

theorem jointCountExponent_upper_identity (ν δ : ℝ) :
    jointCountExponent ν δ = (1 - ν) * hStar ν δ := by
  unfold jointCountExponent hStar mStar
  ring

theorem jointCountExponent_lower_identity {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    jointCountExponent ν δ = (1 - δ) - (ν - δ) * lStar ν δ := by
  have hd := (witnessDen_pos hν hδ).ne'
  unfold jointCountExponent lStar mStar
  field_simp
  unfold witnessDen
  ring

theorem jointCountExponent_bounds {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    1 - ν ≤ jointCountExponent ν δ ∧ jointCountExponent ν δ ≤ 1 - δ := by
  have hb : 0 ≤ 1 - ν := by linarith [hν.2]
  have ha : 0 ≤ ν - δ := sub_nonneg.mpr hδ.2
  constructor
  · rw [jointCountExponent_upper_identity]
    nlinarith [mul_le_mul_of_nonneg_left (one_le_hStar hν hδ) hb]
  · rw [jointCountExponent_lower_identity hν hδ]
    have hL : 0 ≤ lStar ν δ := by
      dsimp [lStar]
      positivity [mStar_pos hν hδ]
    linarith [mul_nonneg ha hL]

theorem quarter_le_jointCountExponent {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    (1/4 : ℝ) ≤ jointCountExponent ν δ := by
  linarith [hν.2, (jointCountExponent_bounds hν hδ).1]

/-- Every word whose length lies between the two thresholds has exponent at most `e`. -/
theorem wordEnvelope_le_of_mem {ν δ w : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hw : w ∈ Set.Icc (lStar ν δ) (hStar ν δ)) :
    wordEnvelope ν δ w ≤ jointCountExponent ν δ := by
  have hb : 0 ≤ 1 - ν := by linarith [hν.2]
  have ha : 0 ≤ ν - δ := sub_nonneg.mpr hδ.2
  unfold wordEnvelope
  apply max_le
  · rw [jointCountExponent_upper_identity]
    exact mul_le_mul_of_nonneg_left hw.2 hb
  · rw [jointCountExponent_lower_identity hν hδ]
    have := mul_le_mul_of_nonneg_left hw.1 ha
    linarith

/-- At least one of the three actual word lengths meets the good interval.

The nonnegativity assumptions record the intended witness domain; the upper
length and product-length constraints already suffice for this conclusion.
-/
theorem witness_lengths_cover {ν δ r m : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (_hr0 : 0 ≤ r) (_hm0 : 0 ≤ m)
    (hr : r ≤ 1) (hm : m ≤ 1/2) (hrm : 1 ≤ r + m) :
    r ∈ Set.Icc (lStar ν δ) (hStar ν δ) ∨
      2 * m ∈ Set.Icc (lStar ν δ) (hStar ν δ) ∨
      r + m ∈ Set.Icc (lStar ν δ) (hStar ν δ) := by
  have hL := lStar_le_one hν hδ
  have hH := one_le_hStar hν hδ
  by_cases hrL : lStar ν δ ≤ r
  · exact Or.inl ⟨hrL, hr.trans hH⟩
  · by_cases hmL : lStar ν δ ≤ 2 * m
    · exact Or.inr (Or.inl ⟨hmL, by linarith⟩)
    · apply Or.inr ∘ Or.inr
      refine ⟨hL.trans hrm, ?_⟩
      have hrL' : r < 2 * mStar ν δ := by
        simpa only [lStar] using lt_of_not_ge hrL
      have hmL' : 2 * m < 2 * mStar ν δ := by
        simpa only [lStar] using lt_of_not_ge hmL
      dsimp [hStar]
      linarith

/-- The three-polynomial scalar count bound, before analytic error buffers. -/
theorem three_word_min_le {ν δ r m : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hr0 : 0 ≤ r) (hm0 : 0 ≤ m)
    (hr : r ≤ 1) (hm : m ≤ 1/2) (hrm : 1 ≤ r + m) :
    min (wordEnvelope ν δ r)
      (min (wordEnvelope ν δ (2 * m)) (wordEnvelope ν δ (r + m))) ≤
        jointCountExponent ν δ := by
  rcases witness_lengths_cover hν hδ hr0 hm0 hr hm hrm with h | h | h
  · exact (min_le_left _ _).trans (wordEnvelope_le_of_mem hν hδ h)
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (wordEnvelope_le_of_mem hν hδ h)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans
      (wordEnvelope_le_of_mem hν hδ h)



theorem retainedSlope_mem {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    retainedSlope ν ∈ Set.Icc (500001/1000000 : ℝ) ν := by
  have h := retainedSlope_bounds hν
  exact ⟨by linarith, h.2⟩

theorem k_mul_den {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    k ν * (15 - 6 * ν) = 10 * ν := by
  unfold k
  exact div_mul_cancel₀ _ (k_den_pos hν).ne'

/-- The numerator of the count denominator at the retained slot slope. -/
def retainedDenNumerator (ν : ℝ) : ℝ :=
  (3 - ν + 17/100) * (15 - 6 * ν) - 20 * ν

theorem retainedDenNumerator_eq {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    retainedDenNumerator ν = (15 - 6 * ν) * (3 - ν - 2 * retainedSlope ν) := by
  have hk := k_mul_den hν
  unfold retainedDenNumerator retainedSlope
  nlinarith

theorem retained_count_den_pos {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < 3 - ν - 2 * retainedSlope ν := by
  rw [← witnessDen_eq]
  exact witnessDen_pos hν (retainedSlope_mem hν)

theorem retainedDenNumerator_pos {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 < retainedDenNumerator ν := by
  rw [retainedDenNumerator_eq hν]
  exact mul_pos (k_den_pos hν) (retained_count_den_pos hν)

/-- The exact denominator-cleared reserve polynomial. -/
def countReserveNumerator (ν : ℝ) : ℝ :=
  ((15 - 6 * ν) - 10 * ν) * retainedDenNumerator ν -
    3 * ((15 - 6 * ν) - (10 * ν - (15 - 6 * ν)*17/200)) * (1 - ν) * (15 - 6 * ν) -
    (15 - 6 * ν) * retainedDenNumerator ν / 250

/-- Bernstein coordinates on `[13/20,3/4]`, with all four coefficients positive. -/
theorem countReserveNumerator_bernstein (ν : ℝ) :
    countReserveNumerator ν =
      (35969507/10000000 : ℝ) * (15/2 - 10 * ν)^3 +
      3 * (70102667/30000000 : ℝ) * (10 * ν - 13/2) * (15/2 - 10 * ν)^2 +
      3 * (2234223/2000000 : ℝ) * (10 * ν - 13/2)^2 * (15/2 - 10 * ν) +
      (55737/400000 : ℝ) * (10 * ν - 13/2)^3 := by
  unfold countReserveNumerator retainedDenNumerator
  ring

theorem countReserveNumerator_nonneg {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 ≤ countReserveNumerator ν := by
  have ht : 0 ≤ 10 * ν - 13/2 := by linarith [hν.1]
  have hu : 0 ≤ 15/2 - 10 * ν := by linarith [hν.2]
  rw [countReserveNumerator_bernstein]
  positivity

theorem countReserveNumerator_identity {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    countReserveNumerator ν =
      ((1 - k ν) - jointCountExponent ν (retainedSlope ν) - 1/250) *
        ((15 - 6 * ν) * retainedDenNumerator ν) := by
  have hd := (k_den_pos hν).ne'
  have he := (retained_count_den_pos hν).ne'
  have hκ : retainedSlope ν * (15 - 6 * ν) = 10 * ν - (15 - 6 * ν)*17/200 := by
    have hk := k_mul_den hν
    unfold retainedSlope
    nlinarith
  calc
    countReserveNumerator ν =
        ((15 - 6 * ν) - 10 * ν) * retainedDenNumerator ν -
          3 * ((15 - 6 * ν) - retainedSlope ν * (15 - 6 * ν)) *
            (1 - ν) * (15 - 6 * ν) -
          (15 - 6 * ν) * retainedDenNumerator ν / 250 := by
      rw [hκ]
      rfl
    _ = _ := by
      rw [retainedDenNumerator_eq hν, jointCountExponent_eq]
      unfold k
      field_simp [hd, he]

/-- The three-witness count gains the fixed reserve `1/250` at `k-17/200`. -/
theorem joint_count_at_retainedSlope {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    jointCountExponent ν (retainedSlope ν) ≤ (1 - k ν) - 1/250 := by
  have hnum := countReserveNumerator_nonneg hν
  have hden := mul_pos (k_den_pos hν) (retainedDenNumerator_pos hν)
  rw [countReserveNumerator_identity hν] at hnum
  have hres : 0 ≤ (1 - k ν) - jointCountExponent ν (retainedSlope ν) - 1/250 := by
    by_contra hc
    have hn : (1 - k ν) - jointCountExponent ν (retainedSlope ν) - 1/250 < 0 :=
      lt_of_not_ge hc
    have := mul_neg_of_neg_of_pos hn hden
    linarith
  linarith

/-- The exact finite-difference identity underlying the amplitude derivative. -/
theorem jointCount_difference {ν δ₁ δ₂ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ₁ : δ₁ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hδ₂ : δ₂ ∈ Set.Icc (500001/1000000 : ℝ) ν) :
    jointCountExponent ν δ₁ - jointCountExponent ν δ₂ =
      3 * (1 - ν)^2 * (δ₂ - δ₁) /
        ((3 - ν - 2 * δ₁) * (3 - ν - 2 * δ₂)) := by
  have h₁ : 3 - ν - 2 * δ₁ ≠ 0 := by
    rw [← witnessDen_eq]
    exact (witnessDen_pos hν hδ₁).ne'
  have h₂ : 3 - ν - 2 * δ₂ ≠ 0 := by
    rw [← witnessDen_eq]
    exact (witnessDen_pos hν hδ₂).ne'
  have hm₁ : jointCountExponent ν δ₁ * (3 - ν - 2 * δ₁) =
      3 * (1 - δ₁) * (1 - ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ h₁
  have hm₂ : jointCountExponent ν δ₂ * (3 - ν - 2 * δ₂) =
      3 * (1 - δ₂) * (1 - ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ h₂
  apply (eq_div_iff (mul_ne_zero h₁ h₂)).mpr
  calc
    (jointCountExponent ν δ₁ - jointCountExponent ν δ₂) *
        ((3 - ν - 2 * δ₁) * (3 - ν - 2 * δ₂)) =
      (jointCountExponent ν δ₁ * (3 - ν - 2 * δ₁)) * (3 - ν - 2 * δ₂) -
        (jointCountExponent ν δ₂ * (3 - ν - 2 * δ₂)) * (3 - ν - 2 * δ₁) := by ring
    _ = _ := by rw [hm₁, hm₂]; ring

/-- A uniform finite-difference version of `partial_delta e <= -3/25`. -/
theorem jointCount_decrease {ν δ₁ δ₂ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ₁ : δ₁ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hδ₂ : δ₂ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hδ : δ₁ ≤ δ₂) :
    jointCountExponent ν δ₂ ≤ jointCountExponent ν δ₁ - (3/25 : ℝ) * (δ₂ - δ₁) := by
  have h₁ : 0 < 3 - ν - 2 * δ₁ := by
    rw [← witnessDen_eq]
    exact witnessDen_pos hν hδ₁
  have h₂ : 0 < 3 - ν - 2 * δ₂ := by
    rw [← witnessDen_eq]
    exact witnessDen_pos hν hδ₂
  have hb : 0 ≤ 5 * (1 - ν) := by linarith [hν.2]
  have hu₁ : 3 - ν - 2 * δ₁ ≤ 5 * (1 - ν) := by linarith [hν.2, hδ₁.1]
  have hu₂ : 3 - ν - 2 * δ₂ ≤ 5 * (1 - ν) := by linarith [hν.2, hδ₂.1]
  have hprod := mul_le_mul hu₁ hu₂ h₂.le hb
  have hgap : 0 ≤ (3/25 : ℝ) * (δ₂ - δ₁) := by positivity
  have hpaid := mul_le_mul_of_nonneg_right hprod hgap
  have hi : (3/25 : ℝ) * (δ₂ - δ₁) ≤
      3 * (1 - ν)^2 * (δ₂ - δ₁) /
        ((3 - ν - 2 * δ₁) * (3 - ν - 2 * δ₂)) := by
    apply (le_div_iff₀ (mul_pos h₁ h₂)).mpr
    nlinarith
  rw [← jointCount_difference hν hδ₁ hδ₂] at hi
  linarith

/-- Above the retained slope the joint count improves with a uniform linear rate. -/
theorem joint_count_above_retainedSlope {ν δ : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (retainedSlope ν) ν) :
    jointCountExponent ν δ ≤ (1 - k ν) - 1/250 -
      (3/25 : ℝ) * (δ - retainedSlope ν) := by
  have hκ := retainedSlope_mem hν
  have hδ' : δ ∈ Set.Icc (500001/1000000 : ℝ) ν := ⟨hκ.1.trans hδ.1, hδ.2⟩
  have hdec := jointCount_decrease hν hκ hδ' hδ.1
  linarith [joint_count_at_retainedSlope hν]

/-- The HIGH-amplitude branch pays the retained price with its fixed reserve. -/
theorem joint_energy_small_cap_high {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (retainedSlope ν) ν)
    (hM : 0 ≤ M) (hs : s ≤ M/10) :
    jointCountExponent ν δ * M + ν * P + δ * s ≤
      (1 - k ν) * M + ν * P + retainedSlope ν * s - M/250 := by
  have hc := mul_le_mul_of_nonneg_right (joint_count_above_retainedSlope hν hδ) hM
  have hgap : 0 ≤ δ - retainedSlope ν := sub_nonneg.mpr hδ.1
  have hcap : 0 ≤ (3/25 : ℝ) * M - s := by linarith
  have hpaid := mul_nonneg hgap hcap
  nlinarith

/-- At small retained width, the better of the zero and joint counts pays `g`. -/
theorem joint_energy_small_cap {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) (hs : s ≤ M/10) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + g ν P s M := by
  have heq : M + g ν P s M =
      (1 - k ν) * M + ν * P + retainedSlope ν * s := by
    rw [g, max_eq_right (by linarith : s - M/10 ≤ 0), mul_zero]
    ring
  rw [heq]
  by_cases hκ : δ ≤ retainedSlope ν
  · have hmin := mul_le_mul_of_nonneg_right
      (min_le_left (1 - k ν) (jointCountExponent ν δ)) hM
    have hslot := mul_le_mul_of_nonneg_right hκ hs0
    linarith
  · have hδκ : δ ∈ Set.Icc (retainedSlope ν) ν := ⟨le_of_not_ge hκ, hδ.2⟩
    have hhigh := joint_energy_small_cap_high hν hδκ hM hs (P := P)
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_right (1 - k ν) (jointCountExponent ν δ)) hM
    linarith

/-- The scalar extension to all nonnegative slot widths leaves the slots intact. -/
theorem joint_energy_le_g {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + g ν P s M := by
  by_cases hs : s ≤ M/10
  · exact joint_energy_small_cap hν hδ hM hs0 hs
  · have hbase := joint_energy_small_cap hν hδ hM
      (by linarith : 0 ≤ M/10) (le_rfl : M/10 ≤ M/10) (P := P)
    have hshift := mul_le_mul_of_nonneg_right hδ.2
      (by linarith : 0 ≤ s - M/10)
    have hcap : g ν P (M/10) M =
        ν * P - k ν * M + retainedSlope ν * (M/10) := by simp [g]
    rw [hcap] at hbase
    rw [g, max_eq_left (by linarith : 0 ≤ s - M/10)]
    dsimp [retainedSlope] at hbase ⊢
    nlinarith

/-- Low-amplitude labels need only the inherited zero count. -/
theorem zero_energy_le_g_of_delta_le {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ≤ retainedSlope ν) (hs : 0 ≤ s) :
    (1 - k ν) * M + ν * P + δ * s ≤ M + g ν P s M := by
  have hslot := mul_le_mul_of_nonneg_right hδ hs
  have hext := mul_nonneg (extensionCoeff_pos hν).le
    (le_max_right (s - M/10) 0)
  unfold g
  nlinarith

/-- A uniform density supremum is a valid scalar HIGH majorant. -/
theorem joint_energy_le_highSup {q ν δ P s M : ℝ}
    (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hν : ν ∈ Set.Icc q (3/4))
    (hδ : δ ∈ Set.Icc (500001/1000000 : ℝ) ν)
    (hM : 0 ≤ M) (hs : 0 ≤ s) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + highSup q P s M := by
  have hν' : ν ∈ Set.Icc (13/20 : ℝ) (3/4) := ⟨hq.1.trans hν.1, hν.2⟩
  exact (joint_energy_le_g hν' hδ hM hs).trans
    (add_le_add le_rfl (le_highSup hq.1 hν.1 hν.2 P s M))



open QRH.SilDensitySplit.CubeFree

/-- The actual upstream price, with an arbitrary uniformly clipped density cut. -/
def jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    QRH.SilDensitySplit.CubeFree.Price where
  f w P s M := max
    (QRH.SilDensitySplit.Density.lowPart B₀ L₀ c₀ (q w) P s M)
    (highSup (q w) P s M)
  nonneg w P s M := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    exact le_max_of_le_left (mul_nonneg hq0 (deletionNeed_nonneg B₀ L₀ c₀ P s M))
  mono w P P' s s' M hP hs := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    exact max_le_max
      (mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) hq0)
      (highSup_mono (hq w) hP hs)
  lip := needLip B₀ L₀ c₀
  lip_nonneg := zero_le_one.trans (one_le_needLip B₀ L₀ c₀)
  lipP w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipP hL hδ)
    · have hhigh := highSup_lipP (hq w) P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipS w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipS hL hδ)
    · have hhigh := highSup_lipS (hq w) P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipM w P s M δ := by
    have hq0 : 0 ≤ q w := by linarith [(hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) (abs_nonneg δ))
        (deletionNeed_lipM hL)
    · have hhigh := highSup_lipM (hq w) P s M δ
      have hscale : (10169/14000 : ℝ) * |δ| ≤ needLip B₀ L₀ c₀ * |δ| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg δ)
      exact hhigh.trans (add_le_add le_rfl hscale)

theorem jointPrice_f (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    (w P s M : ℝ) :
    (jointPrice B₀ L₀ c₀ hL q hq).f w P s M =
      max (q w * deletionNeed B₀ L₀ c₀ P s M) (highSup (q w) P s M) := rfl

theorem jointPrice_lip (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (jointPrice B₀ L₀ c₀ hL q hq).lip = needLip B₀ L₀ c₀ := rfl

/-- Specialization to the literal accepted density cut, rather than a substitute. -/
def jointDensityPrice (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) :
    QRH.SilDensitySplit.CubeFree.Price :=
  jointPrice B₀ L₀ c₀ hL
    (QRH.SilDensitySplit.Density.densQ B₀ L₀ L A D s₀)
    (fun w => ⟨QRH.SilDensitySplit.Density.densQ_ge B₀ L₀ L A D s₀ w,
      QRH.SilDensitySplit.Density.densQ_le B₀ L₀ L A D s₀ w⟩)

theorem jointDensityPrice_f (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀)
    (w P s M : ℝ) :
    (jointDensityPrice B₀ L₀ c₀ L A D s₀ hL).f w P s M =
      max
        (QRH.SilDensitySplit.Density.densQ B₀ L₀ L A D s₀ w *
          deletionNeed B₀ L₀ c₀ P s M)
        (highSup (QRH.SilDensitySplit.Density.densQ B₀ L₀ L A D s₀ w) P s M) := rfl

theorem jointDensityPrice_lip (B₀ L₀ c₀ L A D s₀ : ℝ) (hL : 0 < L₀) :
    (jointDensityPrice B₀ L₀ c₀ L A D s₀ hL).lip = needLip B₀ L₀ c₀ := rfl

theorem highSup_le_jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    (w P s M : ℝ) :
    highSup (q w) P s M ≤ (jointPrice B₀ L₀ c₀ hL q hq).f w P s M :=
  le_max_right _ _

theorem g_le_jointPrice (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    {w ν P s M : ℝ} (hν : ν ∈ Set.Icc (q w) (3/4)) :
    g ν P s M ≤ (jointPrice B₀ L₀ c₀ hL q hq).f w P s M :=
  (le_highSup (hq w).1 hν.1 hν.2 P s M).trans
    (highSup_le_jointPrice B₀ L₀ c₀ hL q hq w P s M)


/-- The zero-density function is exactly the inherited function. -/
theorem k_eq_old (ν : ℝ) : k ν = Qrh.JointDetector.k ν := rfl

/-- The refined fixed cutoff remains strictly below every retained slope. -/
def amplitudeCutoff : ℝ := 500001/1000000

theorem retainedSlope_at_lower : retainedSlope (13/20 : ℝ) = 11113/22200 := by
  norm_num [retainedSlope, k]

theorem retainedSlope_cutoff_gap {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    (19/222000 : ℝ) ≤ retainedSlope ν - amplitudeCutoff := by
  have h := (retainedSlope_bounds hν).1
  dsimp [amplitudeCutoff]
  linarith

theorem retainedSlope_gt_cutoff {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    amplitudeCutoff < retainedSlope ν := by
  linarith [retainedSlope_cutoff_gap hν]

/-- The low-amplitude floor uses only the inherited zero count. -/
theorem zero_energy_le_g_of_delta_le_cutoff {ν δ P s M : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (hδ : δ ≤ amplitudeCutoff) (hs : 0 ≤ s) :
    (1 - k ν) * M + ν * P + δ * s ≤ M + g ν P s M :=
  zero_energy_le_g_of_delta_le hν (hδ.trans (retainedSlope_gt_cutoff hν).le) hs

theorem amplitudeCutoff_half_gap : amplitudeCutoff - 1/2 = (1/1000000 : ℝ) := by
  norm_num [amplitudeCutoff]

theorem global_M_lipschitz_lt_three_quarters : (10169/14000 : ℝ) < 3/4 := by
  norm_num

/-- Exact price saving, for all real widths and row envelopes. -/
theorem g_sub_old (ν P s M : ℝ) :
    g ν P s M - Qrh.JointDetector.g ν P s M = -(1/600 : ℝ) * min s (M/10) := by
  by_cases hs : s ≤ M/10
  · rw [g, Qrh.JointDetector.g,
      max_eq_right (by linarith : s - M/10 ≤ 0), min_eq_left hs]
    unfold retainedSlope k Qrh.JointDetector.retainedSlope Qrh.JointDetector.k
    ring
  · have hs' : M/10 ≤ s := le_of_not_ge hs
    rw [g, Qrh.JointDetector.g,
      max_eq_left (by linarith : 0 ≤ s - M/10), min_eq_right hs']
    unfold retainedSlope k Qrh.JointDetector.retainedSlope Qrh.JointDetector.k
    ring

/-- The saving is independent of the density parameter, so the supremum
retains its exact size, even when the maximizing density changes. -/
theorem highSup_eq_old {q : ℝ}
    (hq : q ∈ Set.Icc (13/20 : ℝ) (3/4)) (P s M : ℝ) :
    highSup q P s M = Qrh.JointDetector.highSup q P s M -
      (1/600 : ℝ) * min s (M/10) := by
  apply le_antisymm
  · apply highSup_le hq.2
    intro ν hν hν'
    have h := Qrh.JointDetector.le_highSup hq.1 hν hν' P s M
    have he := g_sub_old ν P s M
    linarith
  · have h : Qrh.JointDetector.highSup q P s M ≤
        highSup q P s M + (1/600 : ℝ) * min s (M/10) := by
      apply Qrh.JointDetector.highSup_le hq.2
      intro ν hν hν'
      have h := le_highSup hq.1 hν hν' P s M
      have he := g_sub_old ν P s M
      linarith
    linarith

/-- Literal actual-Price comparison: the unchanged LOW price may hide part
of the HIGH saving, so it remains inside the maximum. -/
theorem jointPrice_eq_old_high (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    (w P s M : ℝ) :
    (jointPrice B₀ L₀ c₀ hL q hq).f w P s M =
      max (q w * QRH.SilDensitySplit.CubeFree.deletionNeed B₀ L₀ c₀ P s M)
        (Qrh.JointDetector.highSup (q w) P s M -
          (1/600 : ℝ) * min s (M/10)) := by
  rw [jointPrice_f, highSup_eq_old (hq w)]

theorem jointPrice_le_old (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc (13/20 : ℝ) (3/4))
    (w P s M : ℝ) (hs : 0 ≤ s) (hM : 0 ≤ M) :
    (jointPrice B₀ L₀ c₀ hL q hq).f w P s M ≤
      (Qrh.JointDetector.jointPrice B₀ L₀ c₀ hL q hq).f w P s M := by
  rw [jointPrice_eq_old_high, Qrh.JointDetector.jointPrice_f]
  apply max_le_max le_rfl
  have : 0 ≤ min s (M/10) := le_min hs (by positivity)
  linarith

end
end Qrh.JointDetector.FineRefinedPrice

#print axioms Qrh.JointDetector.FineRefinedPrice.joint_energy_le_highSup
#print axioms Qrh.JointDetector.FineRefinedPrice.jointDensityPrice
#print axioms Qrh.JointDetector.FineRefinedPrice.g_sub_old
#print axioms Qrh.JointDetector.FineRefinedPrice.jointPrice_le_old
