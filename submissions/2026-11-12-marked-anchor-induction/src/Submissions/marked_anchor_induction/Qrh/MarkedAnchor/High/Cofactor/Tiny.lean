/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafContract

/-!
# High.Cofactor.Tiny

The tiny-core count for `LeafContract.tinyCore`:

`tiny_core_count`: for `v ≥ 0`, `δ > 0` there is `C` such that for every `Z ≥ 1`, `X ≥ 1` and every
finite set of nonzero `z` with `N(z) ≤ X` and `z = f⁶ c`, `N(c) ≤ Z^v`,
`#rows ≤ C · X^(1/6 + δ) · Z^(5v/6 + δ)`.

Proof: `z ↦ (f, c)` is injective; each pair has weight
`1 ≤ X^s (Z^v)^t N(f)^(-6s) N(c)^(-(s+t))` with `s = 1/6 + δ`, `t = 5/6 + δ/(v+1)`, and
`∑_{f,c ≠ 0} N(f)^(-6s) N(c)^(-(s+t))` converges (both exponents `> 1`, baseline
`frequencyWeight_summable_norm`).

This method (and any method using only the convergent element series) needs `X^(1/6+δ)`; the
exact power `X^(1/6)` would need a linear lattice-point count. In the leaf `X ≤ bΦ Z^Mcap`, so
`X^δ` is absorbed.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Cofactor
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical
local notation "O" => HeckeFamily.O

/-- The norm weight `N(u)^(-a)` on nonzero elements. -/
def normWeight (a : ℝ) (u : NonzeroFrequency) : ℝ := ((Ideal.span {u.val}).absNorm : ℝ) ^ (-a)

theorem normWeight_nonneg (a : ℝ) (u : NonzeroFrequency) : 0 ≤ normWeight a u :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem normWeight_summable (a : ℝ) (ha : 1 < a) : Summable (normWeight a) := by
  have hs := frequencyWeight_summable_norm (a : ℂ) (by simpa using ha)
  refine hs.congr fun u => ?_
  rw [frequencyWeight_norm]
  unfold normWeight
  have hn : 0 ≤ ‖ConcreteTraceCRT.eisEmbedding u.val‖ := norm_nonneg _
  rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← Real.rpow_natCast,
    ← Real.rpow_mul hn]
  congr 1
  simp only [Complex.ofReal_re]
  push_cast; ring

theorem absNorm_pos (u : NonzeroFrequency) : 1 ≤ ((Ideal.span {u.val}).absNorm : ℝ) := by
  have hp : 0 < (Ideal.span {u.val}).absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa [Ideal.span_singleton_eq_bot] using u.property))
  exact_mod_cast hp

/-- The pair weight is at least the inverse of the window: `X^(-s) (Z^v)^(-t) ≤ w(f, c)`. -/
theorem pair_weight {A B X Y s t : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hX : A ^ 6 * B ≤ X) (hY : B ≤ Y) :
    1 ≤ X ^ s * Y ^ t * (A ^ (-(6 * s)) * B ^ (-(s + t))) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have h1 : (A ^ 6 * B) ^ s ≤ X ^ s := Real.rpow_le_rpow (by positivity) hX hs
  have h2 : B ^ t ≤ Y ^ t := Real.rpow_le_rpow hB0.le hY ht
  have he : (A ^ 6 * B) ^ s * B ^ t * (A ^ (-(6 * s)) * B ^ (-(s + t))) = 1 := by
    rw [Real.mul_rpow (by positivity) hB0.le, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]
    have e1 : A ^ ((6 : ℕ) * s) * A ^ (-(6 * s)) = 1 := by
      rw [← Real.rpow_add hA0]; push_cast; simp
    have e2 : B ^ s * B ^ t * B ^ (-(s + t)) = 1 := by
      rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]; simp
    calc A ^ ((6 : ℕ) * s) * B ^ s * B ^ t * (A ^ (-(6 * s)) * B ^ (-(s + t)))
        = (A ^ ((6 : ℕ) * s) * A ^ (-(6 * s))) * (B ^ s * B ^ t * B ^ (-(s + t))) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  have hw : 0 ≤ A ^ (-(6 * s)) * B ^ (-(s + t)) := by positivity
  calc (1 : ℝ) = (A ^ 6 * B) ^ s * B ^ t * (A ^ (-(6 * s)) * B ^ (-(s + t))) := he.symm
    _ ≤ X ^ s * Y ^ t * (A ^ (-(6 * s)) * B ^ (-(s + t))) := by
        apply mul_le_mul_of_nonneg_right _ hw
        have hX0 : 0 ≤ X := le_trans (by positivity) hX
        exact mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg hX0 _)

/-- **Tiny-core count** (with `X^δ`). -/
theorem tiny_core_count (v δ : ℝ) (hv : 0 ≤ v) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ X : ℝ, 1 ≤ X →
    ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0 ∧ ((Ideal.span {z}).absNorm : ℝ) ≤ X ∧
      Qrh.MarkedAnchor.High.tinyCore Z v z) →
      (rows.card : ℝ) ≤ C * X ^ (1/6 + δ : ℝ) * Z ^ (5*v/6 + δ) := by
  set s : ℝ := 1/6 + δ with hsdef
  set t : ℝ := 5/6 + δ/(v+1) with htdef
  have hv1 : 0 < v + 1 := by linarith
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have h6s : 1 < 6 * s := by rw [hsdef]; linarith
  have hst : 1 < s + t := by
    rw [hsdef, htdef]; have : 0 ≤ δ/(v+1) := by positivity
    linarith
  have hg := normWeight_summable (6 * s) h6s
  have hh := normWeight_summable (s + t) hst
  have hgh := hg.mul_of_nonneg hh (fun _ => normWeight_nonneg _ _) (fun _ => normWeight_nonneg _ _)
  set D : ℝ := ∑' p : NonzeroFrequency × NonzeroFrequency,
    normWeight (6 * s) p.1 * normWeight (s + t) p.2 with hDdef
  have hD0 : 0 ≤ D := tsum_nonneg fun p =>
    mul_nonneg (normWeight_nonneg _ _) (normWeight_nonneg _ _)
  refine ⟨D + 1, by linarith, ?_⟩
  intro Z hZ X hX rows hrows
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  -- the chosen decomposition
  have hex : ∀ z ∈ rows, ∃ p : NonzeroFrequency × NonzeroFrequency,
      z = p.1.val ^ 6 * p.2.val ∧ (((Ideal.span {p.2.val}).absNorm : ℝ) ≤ Z ^ v) := by
    intro z hz
    obtain ⟨hz0, -, f, c, he, hc⟩ := hrows z hz
    have hf : f ≠ 0 := fun hf => hz0 (by rw [he, hf]; ring)
    have hc0 : c ≠ 0 := fun h0 => hz0 (by rw [he, h0]; ring)
    exact ⟨(⟨f, hf⟩, ⟨c, hc0⟩), he, hc⟩
  have : Nonempty NonzeroFrequency := ⟨⟨1, one_ne_zero⟩⟩
  choose! pr hpr using hex
  have hinj : Set.InjOn pr rows := by
    intro z hz z' hz' he
    rw [(hpr z hz).1, (hpr z' hz').1, he]
  -- each row is bounded by its pair weight
  have hrow (z : O) (hz : z ∈ rows) : (1 : ℝ) ≤ X ^ s * (Z ^ v) ^ t *
      (normWeight (6 * s) (pr z).1 * normWeight (s + t) (pr z).2) := by
    obtain ⟨he, hc⟩ := hpr z hz
    have hn := (hrows z hz).2.1
    have hmul : ((Ideal.span {z}).absNorm : ℝ) =
        ((Ideal.span {(pr z).1.val}).absNorm : ℝ) ^ 6 *
          ((Ideal.span {(pr z).2.val}).absNorm : ℝ) := by
      conv_lhs => rw [he]
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, map_mul,
        map_pow]
      push_cast; ring
    unfold normWeight
    exact pair_weight (absNorm_pos _) (absNorm_pos _) hs0 ht0 (hmul ▸ hn) hc
  have hcard : (rows.card : ℝ) ≤ X ^ s * (Z ^ v) ^ t * D := by
    have hK : 0 ≤ X ^ s * (Z ^ v) ^ t := by positivity
    calc (rows.card : ℝ) = ∑ z ∈ rows, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ rows, X ^ s * (Z ^ v) ^ t *
          (normWeight (6 * s) (pr z).1 * normWeight (s + t) (pr z).2) := Finset.sum_le_sum hrow
      _ = X ^ s * (Z ^ v) ^ t * ∑ p ∈ rows.image pr,
          normWeight (6 * s) p.1 * normWeight (s + t) p.2 := by
          rw [Finset.mul_sum, Finset.sum_image hinj]
      _ ≤ X ^ s * (Z ^ v) ^ t * D := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact hgh.sum_le_tsum _ (fun p _ => mul_nonneg (normWeight_nonneg _ _)
            (normWeight_nonneg _ _))
  have hZt : (Z ^ v) ^ t ≤ Z ^ (5*v/6 + δ) := by
    rw [← Real.rpow_mul hZ0.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    rw [htdef]
    have : v * (δ / (v+1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ hv1]; nlinarith
    nlinarith
  calc (rows.card : ℝ) ≤ X ^ s * (Z ^ v) ^ t * D := hcard
    _ ≤ X ^ s * Z ^ (5*v/6 + δ) * (D + 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hZt (by positivity)) (by linarith) hD0
        positivity
    _ = (D + 1) * X ^ (1/6 + δ : ℝ) * Z ^ (5*v/6 + δ) := by rw [hsdef]; ring

end
end Qrh.MarkedAnchor.High.Cofactor
