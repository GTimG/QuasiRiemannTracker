/- Copyright (c) 2026 Sil. Apache-2.0.
One raw exceptional reference bound for both genuine centering and the
old low-volume reference. The fixed c^(-2/3) is never replaced by one.

-/
import Candidate.SilPrior.FourthPower.RepairedRawExceptional

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedRawReferenceScale
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalCentered
open MixedInnerExceptionalBlock MixedFirstExceptionalNormalization MixedFirstGeometricCaps MixedFirstChosenEnergy
open RepairedRawExceptional
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- c=1 gives the centered reference. c=2/9,ell=0 gives the actual low
branch with its finite comparison cost. No new analytic input occurs. -/
theorem raw_reference_of_lower_minimum (root : Source ι a b) (hunit : root.d = (1,1))
    (η τ : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (B : actualAllocations (tuplePools root) C)
    (K Z Tfirst Cfirst ξ padding v ell c : ℝ) (hZ : 1 < Z) (hK : Z ≤ K)
    (hCf : 1 ≤ Cfirst) (hξ : 0 ≤ ξ) (hc : 0 < c)
    (hL : c * Z^ell ≤ root.L) (hV : Real.logb Z (sourceVolume root) ≤ v)
    (hmod : τ.modulus = η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72:O)} *
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E * activeConductor C D})
    (hfirst : Tfirst ≤ Cfirst * firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (sourceVolume root))
    (n : ℤ) (hn : Retained (frequencyRadius Tfirst Z ξ) n) (u : Id) :
    allocationShape root C B (nominalChildScale C D E K (sourceVolume root) Z padding n) 1 /
      (reference τ C D (sourceVolume root) Z * (u.absNorm : ℝ)) ≤
    (slotCost root / (u.absNorm : ℝ)) * c^(-2/3:ℝ) *
      Z^(v-5/6-2*ell/3+5*(frequencyLoss Z Cfirst ξ+padding)/6) := by
  have hz := zero_lt_one.trans hZ
  have hk : 0 < K := hz.trans_le hK
  have he := raw_allocation_reference_seed root η τ C D hC hD hCD E B K Z Tfirst Cfirst ξ padding
    hk hZ hCf hξ hmod hfirst n hn u
  have hR : 1 ≤ inputWidth η K Z := by
    have hh : 1 ≤ Real.logb Z K := by
      simpa only [Real.logb_self_eq_one hZ] using Real.logb_le_logb_of_le hZ hz hK
    have hη := Real.logb_nonneg hZ (ideal_norm_one_le η.modulus_ne_bot)
    have hf := Real.logb_nonneg hZ fixed_presentation_one_le
    unfold inputWidth
    linarith
  have hmin : Real.logb Z c + ell ≤ Real.logb Z root.L := by
    have hh := Real.logb_le_logb_of_le hZ (mul_pos hc (Real.rpow_pos_of_pos hz _)) hL
    rwa [Real.logb_mul hc.ne' (Real.rpow_pos_of_pos hz ell).ne', Real.logb_rpow hz hZ.ne'] at hh
  have hprefix : Real.logb Z (prefixNormMax root.d) = 0 := by
    simp only [hunit, prefixNormMax, map_one, Nat.cast_one, max_self, Real.logb_one]
  have hfactor : 0 ≤ slotCost root / (u.absNorm : ℝ) :=
    div_nonneg (slotCost_nonneg root) (Nat.cast_nonneg _)
  apply he.trans
  calc
    _ ≤ (slotCost root / (u.absNorm : ℝ)) *
        Z^((-2*Real.logb Z c/3)+(v-5/6-2*ell/3+5*(frequencyLoss Z Cfirst ξ+padding)/6)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by rw [hprefix]; linarith)) hfactor
    _ = _ := by
      have hp : Z^(-2*Real.logb Z c/3) = c^(-2/3:ℝ) := by
        rw [show -2*Real.logb Z c/3 = Real.logb Z c*(-2/3) by ring,
          Real.rpow_mul hz.le, Real.rpow_logb hz hZ.ne' hc]
      rw [Real.rpow_add hz, hp]
      ring

end
end Candidate.SilPrior.FourthPower.RepairedRawReferenceScale
