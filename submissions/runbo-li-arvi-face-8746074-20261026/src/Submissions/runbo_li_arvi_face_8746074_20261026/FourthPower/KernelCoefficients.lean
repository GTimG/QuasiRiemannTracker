/- Copyright (c) 2026 Sil. Apache-2.0.
Connect the actual formal-series coefficients to the finite monomial tables
whose anisotropic masses were proved in KernelForwardMass and KernelMarkedMass.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelFormal
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelMarkedMass

set_option autoImplicit false
namespace Candidate.FourthPower.KernelCoefficients
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open KernelFormal KernelForwardMass KernelMarkedMass

theorem ordinary_series_expansion :
    kernelSeries = ∑ i : Fin 12, ordinaryCoefficient i •
      (formalX^(ordinaryExponent i).1*formalY^(ordinaryExponent i).2) := by
  rw [kernelSeries,LocalKernels.ordinary_expansion]
  norm_num [ordinaryCoefficient,ordinaryExponent,Fin.sum_univ_succ]
  ring

theorem marked_series_expansion :
    LocalKernels.base formalX formalY-kernelSeries = ∑ i : Fin 14, markedCoefficient i •
      (formalX^(markedExponent i).1*formalY^(markedExponent i).2) := by
  rw [kernelSeries,LocalKernels.ordinary_expansion]
  norm_num [LocalKernels.base,markedCoefficient,markedExponent,Fin.sum_univ_succ]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_coefficient_table (j k : ℕ) :
    kernelCoeff (exponent j k) = ∑ i : Fin 12,
      if j=(ordinaryExponent i).1 ∧ k=(ordinaryExponent i).2 then ordinaryCoefficient i else 0 := by
  rw [kernelCoeff,ordinary_series_expansion,map_sum]
  simp_rw [formal_power_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases i <;> dsimp [ordinaryCoefficient,ordinaryExponent] <;>
    simp [MvPowerSeries.coeff_monomial,exponent_injective]

set_option backward.isDefEq.respectTransparency false in
theorem marked_coefficient_table (j k : ℕ) :
    MvPowerSeries.coeff (exponent j k) (LocalKernels.base formalX formalY-kernelSeries) =
      ∑ i : Fin 14,
      if j=(markedExponent i).1 ∧ k=(markedExponent i).2 then markedCoefficient i else 0 := by
  rw [marked_series_expansion,map_sum]
  simp_rw [formal_power_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases i <;> dsimp [markedCoefficient,markedExponent] <;>
    simp [MvPowerSeries.coeff_monomial,exponent_injective]

theorem ordinaryExponent_injective : Function.Injective ordinaryExponent := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [ordinaryExponent] at *

theorem markedExponent_injective : Function.Injective markedExponent := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [markedExponent] at *

theorem ordinary_coefficient_at_index (i : Fin 12) :
    kernelCoeff (exponent (ordinaryExponent i).1 (ordinaryExponent i).2) = ordinaryCoefficient i := by
  rw [ordinary_coefficient_table]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [ite_eq_right]
    intro h
    exact hji (ordinaryExponent_injective (Prod.ext h.1 h.2).symm)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem ordinary_coefficient_nonzero (j k : ℕ) (h : kernelCoeff (exponent j k) ≠ 0) :
    ∃ i : Fin 12, ordinaryExponent i = (j,k) := by
  by_contra hn
  apply h
  rw [ordinary_coefficient_table]
  apply Finset.sum_eq_zero
  intro i hi
  rw [ite_eq_right]
  intro he
  exact hn ⟨i,Prod.ext he.1.symm he.2.symm⟩

end
end Candidate.FourthPower.KernelCoefficients
