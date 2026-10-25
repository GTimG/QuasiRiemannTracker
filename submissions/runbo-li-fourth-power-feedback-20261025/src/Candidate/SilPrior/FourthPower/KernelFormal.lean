/- Copyright (c) 2026 Sil. Apache-2.0.
Fifth-free formal local series. The geometric-series and finite reindexing
lemmas are reused unchanged from Hailey Collet's PR69; its squarefree kernel
is not used as the fifth-free kernel.
-/
import Candidate.SilPrior.FourthPower.LocalKernels
import Submissions.hailey_collet_1252270103.Record1252270103TwoIdeal.RectangularConvolution

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.KernelFormal
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal

def truncatedSeries : LocalSeries := LocalKernels.truncated formalX formalY
def kernelSeries : LocalSeries := LocalKernels.ordinary formalX formalY
def reciprocalSeries : LocalSeries := MvPowerSeries.invOfUnit kernelSeries 1
def kernelCoeff (n : Exponent) : ℤ := MvPowerSeries.coeff n kernelSeries
def reciprocalCoeff (n : Exponent) : ℤ := MvPowerSeries.coeff n reciprocalSeries
def restrictedCoeff (n : Exponent) : ℤ := if n 0+n 1 < 5 then 1 else 0

theorem truncated_coefficient_at (i j : ℕ) :
    MvPowerSeries.coeff (exponent i j) truncatedSeries = if i+j < 5 then 1 else 0 := by
  have he : truncatedSeries = formalX^0*formalY^0+formalX^1*formalY^0+
      formalX^0*formalY^1+formalX^2*formalY^0+formalX^1*formalY^1+
      formalX^0*formalY^2+formalX^3*formalY^0+formalX^2*formalY^1+
      formalX^1*formalY^2+formalX^0*formalY^3+formalX^4*formalY^0+
      formalX^3*formalY^1+formalX^2*formalY^2+formalX^1*formalY^3+
      formalX^0*formalY^4 := by
    dsimp [truncatedSeries,LocalKernels.truncated]
    ring
  rw [he]
  simp only [map_add,formal_power_monomial,coeff_monomial_at]
  by_cases hi : i ≤ 4
  · by_cases hj : j ≤ 4
    · interval_cases i <;> interval_cases j <;> norm_num
    · have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      have h2 : j ≠ 2 := by omega
      have h3 : j ≠ 3 := by omega
      have h4 : j ≠ 4 := by omega
      simp [h0,h1,h2,h3,h4,show ¬i+j < 5 by omega]
  · have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    simp [h0,h1,h2,h3,h4,show ¬i+j < 5 by omega]

theorem truncated_coefficient (n : Exponent) :
    MvPowerSeries.coeff n truncatedSeries = restrictedCoeff n := by
  rw [← exponent_reconstruct n,truncated_coefficient_at]
  simp [restrictedCoeff,exponent]

theorem kernel_constant : MvPowerSeries.constantCoeff kernelSeries = 1 := by
  simp [kernelSeries,LocalKernels.ordinary,LocalKernels.base,LocalKernels.truncated,
    formalX,formalY,MvPowerSeries.constantCoeff_X]

theorem kernelCoeff_zero : kernelCoeff 0 = 1 := kernel_constant

theorem restrictedCoeff_zero : restrictedCoeff 0 = 1 := by norm_num [restrictedCoeff]

theorem forward_divisor_identity : kernelSeries*ordinarySeries = truncatedSeries := by
  calc
    kernelSeries*ordinarySeries = truncatedSeries*((1-formalX)*(1-formalY)*ordinarySeries) := by
      dsimp [kernelSeries,truncatedSeries,LocalKernels.ordinary,LocalKernels.base]
      ring
    _ = truncatedSeries := by rw [ordinary_geometric_identity,mul_one]

theorem kernel_reciprocal : kernelSeries*reciprocalSeries = 1 :=
  MvPowerSeries.mul_invOfUnit kernelSeries 1 kernel_constant

theorem reciprocal_kernel : reciprocalSeries*kernelSeries = 1 :=
  MvPowerSeries.invOfUnit_mul kernelSeries 1 kernel_constant

theorem reciprocalCoeff_zero : reciprocalCoeff 0 = 1 := by
  change MvPowerSeries.constantCoeff reciprocalSeries = 1
  have h := congrArg MvPowerSeries.constantCoeff kernel_reciprocal
  simpa only [map_mul,kernel_constant,one_mul,map_one] using h

theorem inverse_divisor_identity : reciprocalSeries*truncatedSeries = ordinarySeries := by
  rw [← forward_divisor_identity,← mul_assoc,reciprocal_kernel,one_mul]

theorem forward_rectangular_convolution (a b : ℕ) :
    (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
      kernelCoeff (exponent i j)) = if a+b < 5 then 1 else 0 := by
  have h := congrArg (MvPowerSeries.coeff (exponent a b)) forward_divisor_identity
  rw [MvPowerSeries.coeff_mul,truncated_coefficient_at,
    ← rectangular_antidiagonal_sum a b
      (fun x y => MvPowerSeries.coeff x kernelSeries*MvPowerSeries.coeff y ordinarySeries)] at h
  simpa only [coeff_ordinarySeries,mul_one,kernelCoeff] using h

theorem inverse_rectangular_convolution (a b : ℕ) :
    (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
      reciprocalCoeff (exponent i j)*(if (a-i)+(b-j) < 5 then 1 else 0)) = 1 := by
  have h := congrArg (MvPowerSeries.coeff (exponent a b)) inverse_divisor_identity
  rw [MvPowerSeries.coeff_mul,coeff_ordinarySeries,
    ← rectangular_antidiagonal_sum a b
      (fun x y => MvPowerSeries.coeff x reciprocalSeries*MvPowerSeries.coeff y truncatedSeries)] at h
  simpa only [reciprocalCoeff,truncated_coefficient_at] using h

/-- Exact equality of formal marked series: no analytic evaluation or
nonvanishing assumption on x or y is used. The residual remains unrestricted. -/
theorem forward_marked_series :
    LocalKernels.markedMul
      (kernelSeries,LocalKernels.base formalX formalY-kernelSeries)
      (ordinarySeries,ordinarySeries) = (truncatedSeries,1) := by
  apply Prod.ext
  · exact forward_divisor_identity
  · change kernelSeries*ordinarySeries+
      (LocalKernels.base formalX formalY-kernelSeries)*ordinarySeries = 1
    calc
      _ = (1-formalX)*(1-formalY)*ordinarySeries := by
        dsimp [LocalKernels.base]
        ring
      _ = 1 := ordinary_geometric_identity

/-- For inverse extraction the marked kernel multiplies T, not 1 or a
punctured ordinary series. This preserves the coefficient of x^2 z. -/
theorem inverse_marked_series :
    LocalKernels.markedMul
      (reciprocalSeries,(kernelSeries-LocalKernels.base formalX formalY)*reciprocalSeries^2)
      (truncatedSeries,1) = (ordinarySeries,ordinarySeries) := by
  apply Prod.ext
  · exact inverse_divisor_identity
  · change reciprocalSeries*1+
      (kernelSeries-LocalKernels.base formalX formalY)*reciprocalSeries^2*truncatedSeries = ordinarySeries
    have ht : (1-formalX)*(1-formalY)*truncatedSeries = kernelSeries := rfl
    calc
      _ = reciprocalSeries*(1+(kernelSeries*reciprocalSeries)*truncatedSeries-
          reciprocalSeries*((1-formalX)*(1-formalY)*truncatedSeries)) := by
        dsimp [LocalKernels.base]
        ring
      _ = reciprocalSeries*truncatedSeries := by rw [ht,kernel_reciprocal,reciprocal_kernel]; ring
      _ = ordinarySeries := inverse_divisor_identity

end
end Candidate.SilPrior.FourthPower.KernelFormal
