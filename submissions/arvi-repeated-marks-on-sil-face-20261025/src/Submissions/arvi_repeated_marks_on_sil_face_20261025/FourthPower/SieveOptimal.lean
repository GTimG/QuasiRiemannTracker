/- Copyright (c) 2026 Sil. Apache-2.0.
Close the concrete optimal sextic sieve obligation from the proved iteration.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveImprovement

set_option autoImplicit false
namespace Candidate.FourthPower.SieveOptimal
noncomputable section
open OAI OAI.SevenEighths
open SexticSieve SieveRanges SieveExponent SieveImprovement

theorem majorant_swap (M N : ℝ) : majorant N M = majorant M N := by
  unfold majorant
  ring

theorem ordered_shape (α δ M N : ℝ) (hδ : 0 ≤ δ) (hα : α ≤ 7/6+δ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M) :
    exponentShape α M N ≤ 2*(M*N)^δ*majorant M N := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hl : 1 ≤ (M*N)^δ := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN) hδ
  have hc : N^(7/6 : ℝ) ≤ M^(5/6 : ℝ)*N^(1/3 : ℝ) := by
    calc
      _ = N^(5/6 : ℝ)*N^(1/3 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hN0.le hNM (by norm_num : (0 : ℝ) ≤ 5/6)) (by positivity)
  have hn : N^α ≤ (M*N)^δ*(M^(5/6 : ℝ)*N^(1/3 : ℝ)) := by
    calc
      _ ≤ N^(7/6+δ) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N^(7/6 : ℝ)*N^δ := Real.rpow_add hN0 _ _
      _ ≤ (M^(5/6 : ℝ)*N^(1/3 : ℝ))*(M*N)^δ :=
        mul_le_mul hc (Real.rpow_le_rpow hN0.le
          (show N ≤ M*N by nlinarith) hδ) (by positivity) (by positivity)
      _ = _ := mul_comm _ _
  have hm : M ≤ (M*N)^δ*M := le_mul_of_one_le_left hM0.le hl
  have hv : M^(5/6 : ℝ)*N^(1/3 : ℝ) ≤ (M*N)^δ*(M^(5/6 : ℝ)*N^(1/3 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hl
  have hmajorant : M+2*(M^(5/6 : ℝ)*N^(1/3 : ℝ)) ≤ 2*majorant M N := by
    unfold majorant
    have hw : 0 ≤ M^(1/3 : ℝ)*N^(5/6 : ℝ) := by positivity
    linarith
  unfold exponentShape
  calc
    _ ≤ (M*N)^δ*M+(M*N)^δ*(M^(5/6 : ℝ)*N^(1/3 : ℝ))+
        (M*N)^δ*(M^(5/6 : ℝ)*N^(1/3 : ℝ)) := add_le_add (add_le_add hm hn) hv
    _ = (M*N)^δ*(M+2*(M^(5/6 : ℝ)*N^(1/3 : ℝ))) := by ring
    _ ≤ (M*N)^δ*(2*majorant M N) := mul_le_mul_of_nonneg_left hmajorant (by positivity)
    _ = _ := by ring

theorem theta_optimal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      theta M N ≤ C*(M*N)^ε*majorant M N := by
  have hδ : 0 < ε/2 := by positivity
  obtain ⟨α,hα,hα₂,hclose,h⟩ := arbitrary_close (ε/2) hδ
  obtain ⟨C,hC,hb⟩ := h (ε/2) hδ
  have hordered (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M) :
      theta M N ≤ 2*C*(M*N)^ε*majorant M N := by
    have hM0 : 0 < M := zero_lt_one.trans_le hM
    have hN0 : 0 < N := zero_lt_one.trans_le hN
    have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
      rw [← Real.rpow_add (mul_pos hM0 hN0)]
      congr 1
      ring
    calc
      _ ≤ C*(M*N)^(ε/2)*exponentShape α M N := hb M N hM hN
      _ ≤ C*(M*N)^(ε/2)*(2*(M*N)^(ε/2)*majorant M N) :=
        mul_le_mul_of_nonneg_left (ordered_shape α (ε/2) M N hδ.le hclose.le hM hN hNM) (by positivity)
      _ = 2*C*((M*N)^(ε/2)*(M*N)^(ε/2))*majorant M N := by ring
      _ = _ := by rw [he]
  refine ⟨512*C,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hm : 0 ≤ majorant M N := by unfold majorant; positivity
  by_cases hNM : N ≤ M
  · apply (hordered M N hM hN hNM).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by nlinarith : 2*C ≤ 512*C) (by positivity)) hm
  · calc
      _ ≤ 256*theta N M := theta_reverse M N
      _ ≤ 256*(2*C*(N*M)^ε*majorant N M) :=
        mul_le_mul_of_nonneg_left (hordered N M hN hM (le_of_not_ge hNM)) (by norm_num)
      _ = _ := by rw [majorant_swap,mul_comm N M]; ring

/-- Unconditional optimal sextic large sieve for the exact finite families
and common coefficients used by the fourth-power reference argument. -/
theorem optimal_bound : OptimalBound := by
  intro ε hε
  obtain ⟨C,hC,hb⟩ := theta_optimal ε hε
  refine ⟨C,hC,?_⟩
  intro A B hA hB rows columns hr hc a
  exact (energy_le_theta A B rows columns hr hc a).trans
    (mul_le_mul_of_nonneg_right (hb A B hA hB) (coefficientMass_nonneg columns a))

end
end Candidate.FourthPower.SieveOptimal
