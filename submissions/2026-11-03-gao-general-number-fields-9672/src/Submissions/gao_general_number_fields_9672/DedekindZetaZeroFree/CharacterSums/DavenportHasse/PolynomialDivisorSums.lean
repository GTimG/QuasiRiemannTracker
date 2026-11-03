/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/CharacterSums/DavenportHasse/PolynomialDivisorSums.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.CharacterSums.DavenportHasse.MonicPolynomialCounting

@[expose] public section

open Polynomial

namespace DavenportHasse.PolyPart

open scoped Classical

variable {k : Type*} [Field k] [Fintype k]

theorem convolution_reindexed (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, b χ ψ m * a χ ψ (n - m)) =
      ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
        if d * j ≤ n then
          (∑ P ∈ Mon k d,
            if Irreducible P then
              (d : ℂ) * wt χ ψ P ^ j * a χ ψ (n - d * j)
            else 0)
        else 0 := by
  calc
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors,
        ∑ P ∈ Mon k d, if Irreducible P then
          (d : ℂ) * wt χ ψ P ^ (m / d) * a χ ψ (n - d * (m / d))
        else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      unfold b
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.sum_mul, ← sum_Mon]
      have hdm : d * (m / d) = m := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      simp only [hdm, ite_mul, zero_mul]
    _ = _ := divisors_reindex n (fun d j =>
      ∑ P ∈ Mon k d, if Irreducible P then
        (d : ℂ) * wt χ ψ P ^ j * a χ ψ (n - d * j) else 0)

end DavenportHasse.PolyPart
