/- Adapted from GTimG/QuasiRiemannTracker accepted PR63, head 52419a826d4a8465cdeb56aaa2d471c489221d1d. Original attribution retained in final package. -/
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace QRH.Record12518109Return
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A fixed affine count is available on an upward interval in the amplitude.
The value and its availability do not depend on the feedback parameter. -/
structure Branch where
  available : ℝ → ℝ → Prop
  value : ℝ → ℝ → ℝ
  upward : ∀ {δ p q : ℝ}, available δ p → p ≤ q → q ≤ 1/2 → available δ q
  antitone : ∀ {δ p q : ℝ}, available δ p → available δ q → p ≤ q →
    value δ q ≤ value δ p

def finiteEnvelope (base : ℝ → ℝ → ℝ → ℝ) :
    List Branch → ℝ → ℝ → ℝ → ℝ
  | [], κ, δ, p => base κ δ p
  | b :: bs, κ, δ, p =>
      if b.available δ p then min (b.value δ p) (finiteEnvelope base bs κ δ p)
      else finiteEnvelope base bs κ δ p

theorem finiteEnvelope_le_base (base : ℝ → ℝ → ℝ → ℝ)
    (bs : List Branch) (κ δ p : ℝ) : finiteEnvelope base bs κ δ p ≤ base κ δ p := by
  induction bs with
  | nil => exact le_rfl
  | cons b bs ih =>
    simp only [finiteEnvelope]
    split_ifs
    · exact (min_le_right _ _).trans ih
    · exact ih

theorem finiteEnvelope_le_branch (base : ℝ → ℝ → ℝ → ℝ)
    {b : Branch} {bs : List Branch} (hb : b ∈ bs) {κ δ p : ℝ}
    (ha : b.available δ p) : finiteEnvelope base bs κ δ p ≤ b.value δ p := by
  induction bs with
  | nil => simp at hb
  | cons c cs ih =>
    simp only [List.mem_cons] at hb
    simp only [finiteEnvelope]
    rcases hb with h | h
    · subst c
      rw [if_pos ha]
      exact min_le_left _ _
    · split_ifs
      · exact (min_le_right _ _).trans (ih h)
      · exact ih h

theorem min_one_sided_gap {c x y g : ℝ} (hg : 0 ≤ g) (hxy : x-y ≤ g) :
    min c x-min c y ≤ g := by
  rcases le_total c y with h | h
  · rw [min_eq_left h]
    have := min_le_left c x
    linarith
  · rw [min_eq_right h]
    have := min_le_right c x
    linarith

/-- Fixed minima preserve the old global one-sided feedback estimate. -/
theorem finiteEnvelope_gap (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    {a κ δ p g : ℝ} (hg : 0 ≤ g) (hbase : base κ δ p-base a δ p ≤ g) :
    finiteEnvelope base bs κ δ p-finiteEnvelope base bs a δ p ≤ g := by
  induction bs with
  | nil => exact hbase
  | cons b bs ih =>
    simp only [finiteEnvelope]
    split_ifs
    · exact min_one_sided_gap hg ih
    · exact ih

theorem finiteEnvelope_antitone (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    {κ δ p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 1/2)
    (hbase : base κ δ q ≤ base κ δ p) :
    finiteEnvelope base bs κ δ q ≤ finiteEnvelope base bs κ δ p := by
  induction bs with
  | nil => exact hbase
  | cons b bs ih =>
    by_cases hp : b.available δ p
    · have ha := b.upward hp hpq hq
      simp only [finiteEnvelope, if_pos hp, if_pos ha]
      exact min_le_min (b.antitone hp ha hpq) ih
    · simp only [finiteEnvelope, if_neg hp]
      split_ifs
      · exact (min_le_right _ _).trans ih
      · exact ih

/-- A finite minimum is attained at the old count or an actually available
fixed count. This is the interface for abstract count-moment premises. -/
theorem finiteEnvelope_attained (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    (κ δ p : ℝ) :
    finiteEnvelope base bs κ δ p=base κ δ p ∨
      ∃ b ∈ bs, b.available δ p ∧ finiteEnvelope base bs κ δ p=b.value δ p := by
  induction bs with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    by_cases ha : b.available δ p
    · simp only [finiteEnvelope, if_pos ha]
      rcases le_total (b.value δ p) (finiteEnvelope base bs κ δ p) with h | h
      · exact Or.inr ⟨b, by simp, ha, min_eq_left h⟩
      · rw [min_eq_right h]
        rcases ih with ih | ⟨c,hc,hac,heq⟩
        · exact Or.inl ih
        · exact Or.inr ⟨c, by simp [hc], hac, heq⟩
    · simp only [finiteEnvelope, if_neg ha]
      rcases ih with ih | ⟨c,hc,hac,heq⟩
      · exact Or.inl ih
      · exact Or.inr ⟨c, by simp [hc], hac, heq⟩

/-- Any common finite-family bound transfers at the selected exponent.
Analytic count-moment estimates are explicit hypotheses, not axioms. -/
theorem finiteEnvelope_bound (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    {κ δ p : ℝ} {P : ℝ → Prop} (hold : P (base κ δ p))
    (hfixed : ∀ b ∈ bs, b.available δ p → P (b.value δ p)) :
    P (finiteEnvelope base bs κ δ p) := by
  rcases finiteEnvelope_attained base bs κ δ p with h | ⟨b,hb,ha,h⟩
  · rw [h]
    exact hold
  · rw [h]
    exact hfixed b hb ha

end
end QRH.Record12518109Return

#print axioms QRH.Record12518109Return.finiteEnvelope_gap
#print axioms QRH.Record12518109Return.finiteEnvelope_antitone
#print axioms QRH.Record12518109Return.finiteEnvelope_bound
