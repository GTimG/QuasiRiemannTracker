/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
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

public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativeBaselineLogBootstrap

@[expose] public section

noncomputable section
open scoped Classical
open Complex Metric Set

namespace PrimitiveStripBootstrap

/-- This closes the disk geometry and all uniformity bookkeeping from the native
primitive strip-growth theorem. The only zero-free input is the older endpoint. -/
theorem subpower_line_97_of_strip
    {ι : Type*} (L E : ι → ℂ → ℂ) (Q : ι → ℝ)
    (hQ : ∀ i, 1 ≤ Q i)
    (hL : ∀ i, Differentiable ℂ (L i))
    (hnz : ∀ i s, (31 / 32 : ℝ) < s.re → L i s ≠ 0)
    (hstrip : ∃ v : ℝ, 0 ≤ v ∧ ∃ K : ℝ, 0 < K ∧
      ∀ i (s : ℂ), (4 / 5 : ℝ) ≤ s.re → s.re ≤ 4 →
        ‖L i s‖ ≤ K * Q i ^ ((11 : ℝ) / 10) * (2 + |s.im|) ^ v)
    (hEuler : ∃ A : ℝ, 0 < A ∧ ∀ i,
      AnalyticOnNhd ℂ (E i) {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, (1 : ℝ) < s.re → Complex.exp (E i s) = L i s) ∧
      (∀ s : ℂ, (1001 / 1000 : ℝ) ≤ s.re → ‖E i s‖ ≤ A)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ i (t : ℝ),
      ‖L i (((97 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Q i ^ ε * (2 + |t|) := by
  obtain ⟨v, hv, K, hK, hbound⟩ := hstrip
  obtain ⟨A, hA, hEuler⟩ := hEuler
  apply BaselineLogBootstrap.subpower_line_97 L E Q (max 1 A) (K * 2 ^ v)
    (11 / 10) v (le_max_left _ _) (by positivity) (by norm_num) hv hQ hL hnz
  · intro i t z hz
    have hd : ‖z - ((2 : ℂ) + (t : ℂ) * Complex.I)‖ <
        2 - (31 / 32 : ℝ) - 3 * (1 / 10000 : ℝ) := by
      simpa [mem_ball, dist_eq_norm] using hz
    have hre : |z.re - 2| ≤ ‖z - ((2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h := Complex.abs_re_le_norm (z - ((2 : ℂ) + (t : ℂ) * Complex.I))
      simpa using h
    have him : |z.im - t| ≤ ‖z - ((2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h := Complex.abs_im_le_norm (z - ((2 : ℂ) + (t : ℂ) * Complex.I))
      simpa using h
    have hrelo : (4 / 5 : ℝ) ≤ z.re := by
      linarith [neg_le_abs (z.re - 2)]
    have hrehi : z.re ≤ 4 := by linarith [le_abs_self (z.re - 2)]
    have him' : |z.im| ≤ |z.im - t| + |t| := by
      simpa using abs_add_le (z.im - t) t
    have hT : 2 + |z.im| ≤ 2 * (2 + |t|) := by linarith [abs_nonneg t]
    have hpow : (2 + |z.im|) ^ v ≤ 2 ^ v * (2 + |t|) ^ v := by
      calc (2 + |z.im|) ^ v ≤ (2 * (2 + |t|)) ^ v :=
          Real.rpow_le_rpow (by positivity) hT hv
        _ = 2 ^ v * (2 + |t|) ^ v := Real.mul_rpow (by norm_num) (by positivity)
    calc ‖L i z‖ ≤ K * Q i ^ ((11 : ℝ) / 10) * (2 + |z.im|) ^ v :=
        hbound i z hrelo hrehi
      _ ≤ K * Q i ^ ((11 : ℝ) / 10) * (2 ^ v * (2 + |t|) ^ v) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hK.le (Real.rpow_nonneg (zero_le_one.trans (hQ i)) _))
      _ = K * 2 ^ v * Q i ^ ((11 : ℝ) / 10) * (2 + |t|) ^ v := by ring
  · exact fun i => (hEuler i).1.differentiableOn
  · exact fun i => (hEuler i).2.1
  · intro i s hs
    exact ((hEuler i).2.2 s (by linarith)).trans (le_max_right _ _)

#print axioms subpower_line_97_of_strip

end PrimitiveStripBootstrap
