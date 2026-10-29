/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- Uniform short forward transfers reach an endpoint after finitely many
applications. No closure under limits of the property is required. -/
theorem finite_forward_reachability (P : ℝ → Prop) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (ha : P a)
    (step : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      x < y → y-x ≤ δ → P x → P y) : P b := by
  rcases eq_or_lt_of_le hab with heq | hab
  · simpa [←heq] using ha
  obtain ⟨n,hn⟩ := exists_nat_gt ((b-a)/δ)
  let N := n+1
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  let h := (b-a)/(N:ℝ)
  have hh : 0 < h := div_pos (sub_pos.mpr hab) hN
  have hhδ : h ≤ δ := by
    apply (div_le_iff₀ hN).2
    have hnn : (b-a)/δ < (N:ℝ) := by dsimp [N]; exact hn.trans (by norm_num)
    have := (div_lt_iff₀ hδ).1 hnn
    nlinarith
  have hend : a+(N:ℝ)*h=b := by dsimp [h]; field_simp; ring
  have hi : ∀ i : ℕ, i ≤ N → P (a+(i:ℝ)*h) := by
    intro i
    induction i with
    | zero => intro _; simpa using ha
    | succ i ih =>
      intro hi
      have hiN : i ≤ N := Nat.le_trans (Nat.le_succ i) hi
      have hic : (i:ℝ) ≤ (N:ℝ) := by exact_mod_cast hiN
      have hisc : ((i+1:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hi
      have hix : a+(i:ℝ)*h ∈ Set.Icc a b := by
        constructor
        · have hnonneg : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
          nlinarith [mul_nonneg hnonneg hh.le]
        · rw [←hend]; nlinarith [mul_le_mul_of_nonneg_right hic hh.le]
      have hiy : a+((i+1:ℕ):ℝ)*h ∈ Set.Icc a b := by
        constructor
        · have hnonneg : 0 ≤ ((i+1:ℕ):ℝ) := Nat.cast_nonneg _
          nlinarith [mul_nonneg hnonneg hh.le]
        · rw [←hend]; nlinarith [mul_le_mul_of_nonneg_right hisc hh.le]
      apply step _ hix _ hiy
      · push_cast; nlinarith
      · push_cast; nlinarith
      · exact ih hiN
  simpa [hend] using hi N le_rfl

/-- The same finite argument for curves traversed from right to left. -/
theorem finite_backward_reachability (P : ℝ → Prop) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hb : P b)
    (step : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      x < y → y-x ≤ δ → P y → P x) : P a := by
  have hout := finite_forward_reachability (fun x => P (-x))
    (show -b ≤ -a by linarith) hδ (by simpa using hb) (by
      intro x hx y hy hxy hlen hp
      exact step (-y) ⟨by linarith [hy.2],by linarith [hy.1]⟩
        (-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
        (by linarith) (by linarith) hp)
  simpa using hout

/-- A source curve needs only uniformly valid finite transfers, not a
uniform arithmetic source theorem over all of its parameter values. -/
theorem finite_source_curve_reachability
    (Source : ℝ → ℝ → ℝ → Prop) (B L : ℝ → ℝ) (c : ℝ) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (seed : Source (B a) (L a) c)
    (step : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      x < y → y-x ≤ δ → Source (B x) (L x) c → Source (B y) (L y) c) :
    Source (B b) (L b) c :=
  finite_forward_reachability (fun x => Source (B x) (L x) c) hab hδ seed step

end
end Qrh.JointDetector.RepeatedMarks
#print axioms Qrh.JointDetector.RepeatedMarks.finite_forward_reachability
