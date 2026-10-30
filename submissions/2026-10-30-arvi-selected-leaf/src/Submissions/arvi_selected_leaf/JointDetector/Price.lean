/- Copyright (c) 2026 Joseph Bebel. -/
import Mathlib

/-!
# Global scalar primitives for the joint-detector HIGH price

These statements concern real affine functions. They do not assert the analytic
priced packed supplier or an all-Dirichlet endpoint.
-/

namespace Qrh.JointDetector

noncomputable section

/-- The inherited zero-density gap. -/
def k (ν : ℝ) : ℝ := 10 * ν / (15 - 6 * ν)

/-- The retained slot slope supplied by the three detector polynomials. -/
def retainedSlope (ν : ℝ) : ℝ := k ν - 1 / 12

/-- The second envelope slope of the globally extended HIGH price. -/
def extendedMSlope (ν : ℝ) : ℝ := k ν + (ν - k ν + 1 / 12) / 10

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
    (223/444 : ℝ) ≤ retainedSlope ν ∧ retainedSlope ν ≤ ν := by
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
    0 < ν - k ν + 1/12 := by
  linarith [k_le_nu hν]

theorem extendedMSlope_bounds {ν : ℝ}
    (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4)) :
    0 ≤ extendedMSlope ν ∧ extendedMSlope ν ≤ 61/84 := by
  have hk := k_range hν
  have he := extensionCoeff_pos hν
  dsimp [extendedMSlope]
  constructor <;> linarith [hν.2]

/-- The global HIGH summand, defined even at negative widths and envelopes. -/
def g (ν P s M : ℝ) : ℝ :=
  ν * P - k ν * M + retainedSlope ν * s +
    (ν - k ν + 1/12) * max (s - M/10) 0

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

/-- The envelope field has the exact global bound `61/84`, for either sign. -/
theorem g_lipM {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M δ : ℝ) :
    g ν P s (M + δ) ≤ g ν P s M + (61/84 : ℝ) * |δ| := by
  rw [g_eq_max hν, g_eq_max hν]
  have hk := k_range hν
  have hm := extendedMSlope_bounds hν
  have ha : |-k ν| ≤ (61/84 : ℝ) := by
    rw [abs_neg, abs_of_nonneg (by linarith [hk.1])]
    linarith [hk.2]
  have hb : |-extendedMSlope ν| ≤ (61/84 : ℝ) := by
    rw [abs_neg, abs_of_nonneg hm.1]
    exact hm.2
  apply max_le_max_add
  · linarith [linear_increment_le ha δ]
  · linarith [linear_increment_le hb δ]

/-- A bound uniform in the density parameter; no width has a sign restriction. -/
theorem g_upper_bound {ν : ℝ} (hν : ν ∈ Set.Icc (13/20 : ℝ) (3/4))
    (P s M : ℝ) :
    g ν P s M ≤ (3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (61/84 : ℝ) * |M| := by
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
  refine ⟨(3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (61/84 : ℝ) * |M|, ?_⟩
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
    highSup q P s (M + δ) ≤ highSup q P s M + (61/84 : ℝ) * |δ| := by
  apply highSup_le hq.2
  intro ν hν hν'
  exact (g_lipM ⟨hq.1.trans hν, hν'⟩ P s M δ).trans
    (add_le_add (le_highSup hq.1 hν hν' P s M) le_rfl)

end

end Qrh.JointDetector
