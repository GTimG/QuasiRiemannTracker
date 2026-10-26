/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Prime-dependent ideal convolution and exact frozen/live allocation identities.
The finite divisor-enumeration pattern is adapted from PR69 DivisorConvolution;
all local series are the new fifth-free ones, including the correct marked residual.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelInverseMarkedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelAllocationIdentity
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.IdealMobiusDivisorSum (idealDivisors)
open KernelFormal
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

def kernelOn (S : Finset PrimeIdeal) (A : S → LocalSeries) (I J : Id) : ℤ :=
  ∏ P : S, MvPowerSeries.coeff (localExponent I J P.val.val) (A P)

theorem kernelOn_decode (S : Finset PrimeIdeal) (A : S → LocalSeries) (a : S → ℕ × ℕ) :
    kernelOn S A (decodePair S a).1 (decodePair S a).2 =
      ∏ P : S, MvPowerSeries.coeff (exponent (a P).1 (a P).2) (A P) := by
  unfold kernelOn
  apply Finset.prod_congr rfl
  intro P hP
  simp only [localExponent,decodePair,valuation_decode]

/-- No common-coefficient or constant-one condition is required: marked primes
may carry different local series, whose constant coefficient can be zero. -/
theorem divisor_convolution (S : Finset PrimeIdeal) (A B : S → LocalSeries)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hs : pairSupport I J ⊆ primeValues S) :
    (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      kernelOn S A d.1 d.2*kernelOn S B (cofactorPair I J d).1 (cofactorPair I J d).2) =
      kernelOn S (fun P => A P*B P) I J := by
  rw [← divisor_pair_enumeration hI hJ S hs,
    Finset.sum_image (fun a _ b _ h => decodePair_injective S h)]
  calc
    _ = ∑ a ∈ pairBox S I J, ∏ P : S,
        MvPowerSeries.coeff (exponent (a P).1 (a P).2) (A P)*
        MvPowerSeries.coeff (exponent (valuation I P.val.val-(a P).1)
          (valuation J P.val.val-(a P).2)) (B P) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [cofactorPair_decodePair hI hJ S hs ha,kernelOn_decode,kernelOn_decode,
        Finset.prod_mul_distrib]
    _ = ∏ P : S, ∑ ij ∈ Finset.range (valuation I P.val.val+1) ×ˢ
        Finset.range (valuation J P.val.val+1),
        MvPowerSeries.coeff (exponent ij.1 ij.2) (A P)*
        MvPowerSeries.coeff (exponent (valuation I P.val.val-ij.1)
          (valuation J P.val.val-ij.2)) (B P) := by
      unfold pairBox
      exact (Finset.prod_univ_sum
        (fun P : S => Finset.range (valuation I P.val.val+1) ×ˢ Finset.range (valuation J P.val.val+1))
        (fun P : S => fun ij : ℕ × ℕ =>
          MvPowerSeries.coeff (exponent ij.1 ij.2) (A P)*
          MvPowerSeries.coeff (exponent (valuation I P.val.val-ij.1)
            (valuation J P.val.val-ij.2)) (B P))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [localExponent,MvPowerSeries.coeff_mul,
        ← rectangular_antidiagonal_sum _ _ (fun n m => MvPowerSeries.coeff n (A P)*MvPowerSeries.coeff m (B P))]
      exact Finset.sum_product _ _ _

theorem allocation_expansion {β : Type*} [DecidableEq β] (S : Finset PrimeIdeal)
    (T : S → Finset β) (A : (P : S) → β → LocalSeries) (I J : Id) :
    (∑ a ∈ Fintype.piFinset T, kernelOn S (fun P => A P (a P)) I J) =
      kernelOn S (fun P => ∑ b ∈ T P, A P b) I J := by
  unfold kernelOn
  simp_rw [map_sum]
  exact (Finset.prod_univ_sum T (fun P : S => fun b : β =>
    MvPowerSeries.coeff (localExponent I J P.val.val) (A P b))).symm

def choices (marked : Bool) : Finset Bool := if marked then Finset.univ else {false}

def forwardFactor (freeze : Bool) : LocalSeries :=
  if freeze then LocalKernels.base formalX formalY-kernelSeries else kernelSeries

def inverseFactor (freeze : Bool) : LocalSeries :=
  if freeze then KernelInverseMarkedMass.markedSeries else reciprocalSeries

def inverseResidual (marked freeze : Bool) : LocalSeries :=
  if marked && !freeze then 1 else truncatedSeries

theorem forward_local (marked : Bool) :
    (∑ b ∈ choices marked, forwardFactor b*ordinarySeries) =
      if marked then 1 else truncatedSeries := by
  cases marked with
  | false => simp [choices,forwardFactor,KernelFormal.forward_divisor_identity]
  | true =>
    have h := congrArg Prod.snd forward_marked_series
    simpa [choices,forwardFactor,Fintype.sum_bool,LocalKernels.markedMul,add_comm] using h

theorem inverse_local (marked : Bool) :
    (∑ b ∈ choices marked, inverseFactor b*inverseResidual marked b) = ordinarySeries := by
  cases marked with
  | false => simp [choices,inverseFactor,inverseResidual,KernelFormal.inverse_divisor_identity]
  | true =>
    have h := congrArg Prod.snd inverse_marked_series
    simpa [choices,inverseFactor,inverseResidual,KernelInverseMarkedMass.markedSeries,
      Fintype.sum_bool,LocalKernels.markedMul,add_comm] using h

/-- Forward extraction retains the unrestricted ordinary residual even at
a supplying marked prime. The target forces no ordinary occurrence there. -/
theorem forward_allocated_identity (S : Finset PrimeIdeal) (marked : S → Bool)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    (∑ a ∈ Fintype.piFinset (fun P => choices (marked P)),
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
        kernelOn S (fun P => forwardFactor (a P)) d.1 d.2*
        kernelOn S (fun _P => ordinarySeries) (cofactorPair I J d).1 (cofactorPair I J d).2) =
      kernelOn S (fun P => if marked P then 1 else truncatedSeries) I J := by
  simp_rw [divisor_convolution S _ _ hI hJ hs]
  rw [allocation_expansion S (fun P => choices (marked P))
    (fun _P b => forwardFactor b*ordinarySeries) I J]
  simp_rw [forward_local]

/-- A frozen inverse marked kernel multiplies T. Only a marked occurrence
that remains in the restricted residual has ordinary series 1 at that prime. -/
theorem inverse_allocated_identity (S : Finset PrimeIdeal) (marked : S → Bool)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    (∑ a ∈ Fintype.piFinset (fun P => choices (marked P)),
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
        kernelOn S (fun P => inverseFactor (a P)) d.1 d.2*
        kernelOn S (fun P => inverseResidual (marked P) (a P))
          (cofactorPair I J d).1 (cofactorPair I J d).2) = 1 := by
  simp_rw [divisor_convolution S _ _ hI hJ hs]
  rw [allocation_expansion S (fun P => choices (marked P))
    (fun P b => inverseFactor b*inverseResidual (marked P) b) I J]
  simp_rw [inverse_local]
  simp [kernelOn,localExponent,coeff_ordinarySeries]

end
end Candidate.FourthPower.KernelAllocationIdentity
