/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Noncircular successor input module, 2026-11-03, Zhongpai Gao with AI assistance.
Apache-2.0. Original theorem/dependency attribution below is retained.
Input module paths are relocated only; declaration namespaces stay original.
The old Hecke endpoint is supplied from the disjoint frozen original proof DAG.
Full native-import checking and successor endpoint verification remain pending.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.PhragmenLindelof.QuadraticGrowthStripBounds
public import Mathlib

@[expose] public section

namespace Refinement9672Interpolation

theorem polynomial_strip
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (k : ℕ) (H : ℝ) (hH : 0 ≤ H) (f : ℂ → ℂ)
    (hhol : DiffContOnCl ℂ f {s : ℂ | a < s.re ∧ s.re < b})
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, a < s.re ∧ s.re < b →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hboundary : ∀ s : ℂ, (s.re = a ∨ s.re = b) →
      ‖f s‖ ≤ H * (2 + |s.im|) ^ k) :
    ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖f s‖ ≤ 6 ^ k * H * (2 + |s.im|) ^ k := by

  have hden : ∀ s : ℂ, a ≤ s.re → 1 ≤ ‖s + 2‖ := by
    intro s hs
    have h1 : (s + 2).re = s.re + 2 := by simp [Complex.add_re]
    have h2 : 1 ≤ (s + 2).re := by rw [h1]; linarith
    exact le_trans h2 (Complex.re_le_norm (s + 2))
  have hden_ne : ∀ s : ℂ, a ≤ s.re → (s + 2) ^ k ≠ 0 := by
    intro s hs
    refine pow_ne_zero k ?_
    exact norm_pos_iff.mp (lt_of_lt_of_le one_pos (hden s hs))
  have hcl : closure {s : ℂ | a < s.re ∧ s.re < b} ⊆ {s : ℂ | a ≤ s.re} :=
    closure_minimal (fun s hs => le_of_lt hs.1) (isClosed_Ici.preimage Complex.continuous_re)
  set g : ℂ → ℂ := fun s => f s / (s + 2) ^ k with hgdef
  have hg_apply : ∀ s : ℂ, g s = f s / (s + 2) ^ k := fun s => by rw [hgdef]
  have hgdiff : DiffContOnCl ℂ g {s : ℂ | a < s.re ∧ s.re < b} := by
    refine ⟨?_, ?_⟩
    · exact (hhol.1.div ((differentiableOn_id.add_const 2).pow k)
        (fun s hs => hden_ne s (le_of_lt hs.1)))
    · exact (hhol.2.div (((continuous_id.add continuous_const).pow k).continuousOn)
        (fun s hs => hden_ne s (hcl hs)))

  have hgrowth_g : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, a < s.re ∧ s.re < b →
        ‖g s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    obtain ⟨M, B, hM, hB, hgr⟩ := hgrowth
    refine ⟨M, B, hM, hB, ?_⟩
    intro s hs
    have hden1 : 1 ≤ ‖s + 2‖ := hden s (le_of_lt hs.1)
    have hdiv : ‖g s‖ ≤ ‖f s‖ := by
      rw [hg_apply, norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ hden1)
    exact le_trans hdiv (hgr s hs)

  have hbound_g : ∀ s : ℂ, (s.re = a ∨ s.re = b) → ‖g s‖ ≤ 3 ^ k * H := by
    intro s hs
    have hre : a ≤ s.re := by rcases hs with h | h <;> linarith
    have hden1 : 1 ≤ ‖s + 2‖ := hden s hre
    have him : |s.im| ≤ ‖s + 2‖ := by
      simpa using Complex.abs_im_le_norm (s + 2)
    have h3 : 2 + |s.im| ≤ 3 * ‖s + 2‖ := by
      have h2 : (2 : ℝ) ≤ 2 * ‖s + 2‖ := by linarith
      linarith [him, h2, norm_nonneg (s + 2)]
    have hfb := hboundary s hs
    have hpos : 0 < ‖s + 2‖ ^ k := pow_pos (lt_of_lt_of_le one_pos hden1) k
    rw [hg_apply, norm_div, norm_pow, div_le_iff₀ hpos]
    calc ‖f s‖ ≤ H * (2 + |s.im|) ^ k := hfb
      _ ≤ H * (3 * ‖s + 2‖) ^ k := by
          refine mul_le_mul_of_nonneg_left ?_ hH
          exact pow_le_pow_left₀ (by positivity) h3 k
      _ = 3 ^ k * H * ‖s + 2‖ ^ k := by rw [mul_pow]; ring
  have hquad := DedekindZetaZeroFree.norm_le_on_closed_strip_of_quadratic_exp_growth (a) (b) (3 ^ k * H)
    hab g hgdiff hgrowth_g
    (fun s hs => hbound_g s (Or.inl hs)) (fun s hs => hbound_g s (Or.inr hs))
  intro s hs
  have hgb : ‖g s‖ ≤ 3 ^ k * H := hquad s hs
  have hden1 : 1 ≤ ‖s + 2‖ := hden s hs.1
  have hnorm : ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := by
    have hne : (s + 2) ^ k ≠ 0 := hden_ne s hs.1
    have h2 : g s * (s + 2) ^ k = f s := by rw [hg_apply, div_mul_cancel₀ _ hne]
    calc ‖f s‖ = ‖g s * (s + 2) ^ k‖ := by rw [h2]
      _ = ‖g s‖ * ‖s + 2‖ ^ k := by rw [norm_mul, norm_pow]
  have h3 : ‖s + 2‖ ≤ 2 * (2 + |s.im|) := by
    have hnormle := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre2 : (s + 2).re = s.re + 2 := by simp [Complex.add_re]
    have him2 : (s + 2).im = s.im := by simp [Complex.add_im]
    have hrepos : 0 ≤ s.re + 2 := by linarith [hs.1, ha]
    rw [hre2, him2, abs_of_nonneg hrepos] at hnormle
    have hle : s.re + 2 ≤ 3 := by linarith [hs.2, hb]
    linarith [hnormle, hle, abs_nonneg s.im]
  calc ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := hnorm
    _ ≤ (3 ^ k * H) * (2 * (2 + |s.im|)) ^ k := by
        refine mul_le_mul hgb ?_ (by positivity) (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) h3 k
    _ = 6 ^ k * H * (2 + |s.im|) ^ k := by
        have h36 : (3 : ℝ) ^ k * 2 ^ k = 6 ^ k := by rw [← mul_pow]; norm_num
        rw [mul_pow, ← h36]; ring

end Refinement9672Interpolation

namespace Refinement9672Interpolation

/-- A polynomial height bound gives an admissible quadratic exponential bound.
Its exponent is independent of the conductor and of epsilon. -/
theorem height_rpow_le_quadratic_exp (A : ℝ) (hA : 0 ≤ A) (t : ℝ) :
    (2 + |t|) ^ A ≤ Real.exp (A * (1 + |t|) ^ 2) := by
  have hT : 0 < (2 + |t| : ℝ) := by positivity
  have hlog : Real.log (2 + |t|) ≤ 1 + |t| := by
    have h := Real.log_le_sub_one_of_pos hT
    linarith
  have hsq : 1 + |t| ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  rw [Real.rpow_def_of_pos hT]
  apply Real.exp_le_exp.mpr
  calc Real.log (2 + |t|) * A ≤ (1 + |t|) * A := mul_le_mul_of_nonneg_right hlog hA
    _ ≤ A * (1 + |t|) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsq hA]

/-- Uniform conductor interpolation between .03 and .97. The growth constant
inside the strip may depend on the individual function; the output constant
depends only on the common boundary constant and polynomial height degree. -/
theorem numerator_interpolation
    (Q H ε : ℝ) (hQ : 1 ≤ Q) (hH : 0 ≤ H) (k : ℕ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, (3 / 100 : ℝ) < s.re ∧ s.re < 97 / 100 →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hleft : ∀ s : ℂ, s.re = (3 / 100 : ℝ) →
      ‖f s‖ ≤ H * Q ^ ((47 / 100 : ℝ) + ε) * (2 + |s.im|) ^ k)
    (hright : ∀ s : ℂ, s.re = (97 / 100 : ℝ) →
      ‖f s‖ ≤ H * Q ^ ε * (2 + |s.im|) ^ k) :
    ∀ t : ℝ, ‖f (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (6 ^ k * H) * Q ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ k := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  let g : ℂ → ℂ := fun s => f s * (Q : ℂ) ^ ((s - (97 / 100 : ℂ)) / 2)
  have hg : Differentiable ℂ g := by
    exact hf.mul (((differentiable_id.sub_const (97 / 100 : ℂ)).div_const 2).const_cpow
      (Or.inl hQne))
  have norm_g (s : ℂ) : ‖g s‖ = ‖f s‖ * Q ^ ((s.re - 97 / 100) / 2) := by
    dsimp [g]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQpos]
    congr 2
    simp
  have hweight (s : ℂ) (hs : s.re ≤ (97 / 100 : ℝ)) :
      Q ^ ((s.re - 97 / 100) / 2) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hQ
      (show (s.re - 97 / 100) / 2 ≤ 0 by linarith)
    simpa using h
  have hggrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, (3 / 100 : ℝ) < s.re ∧ s.re < 97 / 100 →
        ‖g s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    obtain ⟨M, B, hM, hB, hgr⟩ := hgrowth
    refine ⟨M, B, hM, hB, fun s hs => ?_⟩
    calc ‖g s‖ = ‖f s‖ * Q ^ ((s.re - 97 / 100) / 2) := norm_g s
      _ ≤ ‖f s‖ * 1 := mul_le_mul_of_nonneg_left (hweight s hs.2.le) (norm_nonneg _)
      _ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by simpa using hgr s hs
  have hgboundary : ∀ s : ℂ, (s.re = (3 / 100 : ℝ) ∨ s.re = 97 / 100) →
      ‖g s‖ ≤ (H * Q ^ ε) * (2 + |s.im|) ^ k := by
    intro s hs
    rcases hs with hs | hs
    · have he : (s.re - 97 / 100) / 2 = -(47 / 100 : ℝ) := by rw [hs]; norm_num
      have hpow : Q ^ ((47 / 100 : ℝ) + ε) * Q ^ (-(47 / 100 : ℝ)) = Q ^ ε := by
        rw [← Real.rpow_add hQpos]
        congr 1
        ring
      rw [norm_g, he]
      calc ‖f s‖ * Q ^ (-(47 / 100 : ℝ)) ≤
          (H * Q ^ ((47 / 100 : ℝ) + ε) * (2 + |s.im|) ^ k) * Q ^ (-(47 / 100 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hleft s hs) (Real.rpow_nonneg hQpos.le _)
        _ = (H * Q ^ ε) * (2 + |s.im|) ^ k := by
          calc _ = H * (Q ^ ((47 / 100 : ℝ) + ε) * Q ^ (-(47 / 100 : ℝ))) *
              (2 + |s.im|) ^ k := by ring
            _ = _ := by rw [hpow]
    · rw [norm_g, hs]
      norm_num
      exact hright s hs
  have hgb := polynomial_strip (3 / 100) (97 / 100) (by norm_num)
    (by norm_num) (by norm_num) k (H * Q ^ ε)
    (mul_nonneg hH (Real.rpow_nonneg hQpos.le _)) g hg.diffContOnCl hggrowth hgboundary
  intro t
  let s : ℂ := ((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hsre : s.re = (3 / 25 : ℝ) := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hkey := hgb s (by rw [hsre]; constructor <;> norm_num)
  have he : (s.re - 97 / 100) / 2 = -(17 / 40 : ℝ) := by rw [hsre]; norm_num
  rw [norm_g, he, hsim] at hkey
  have hmul := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hQpos.le (17 / 40 : ℝ))
  have hcancel : Q ^ (-(17 / 40 : ℝ)) * Q ^ (17 / 40 : ℝ) = 1 := by
    rw [← Real.rpow_add hQpos]
    norm_num
  have hpow : Q ^ ε * Q ^ (17 / 40 : ℝ) = Q ^ ((17 / 40 : ℝ) + ε) := by
    rw [← Real.rpow_add hQpos]
    congr 1
    ring
  calc
    ‖f s‖ = (‖f s‖ * Q ^ (-(17 / 40 : ℝ))) * Q ^ (17 / 40 : ℝ) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ (6 ^ k * (H * Q ^ ε) * (2 + |t|) ^ k) * Q ^ (17 / 40 : ℝ) := hmul
    _ = (6 ^ k * H) * Q ^ ((17 / 40 : ℝ) + ε) * (2 + |t|) ^ k := by
      calc
        _ = (6 ^ k * H) * (Q ^ ε * Q ^ (17 / 40 : ℝ)) * (2 + |t|) ^ k := by ring
        _ = _ := by rw [hpow]

#print axioms polynomial_strip
#print axioms height_rpow_le_quadratic_exp
#print axioms numerator_interpolation

end Refinement9672Interpolation
