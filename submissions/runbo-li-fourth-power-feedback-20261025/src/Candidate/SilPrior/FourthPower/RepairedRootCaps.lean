/- Copyright (c) 2026 Sil. Apache-2.0.
Fixed-exponent arithmetic caps from the actual face. No energy bound.

-/
import Candidate.SilPrior.FourthPower.RepairedRawContext
import Candidate.SilPrior.FourthPower.RepairedRemainderGeometry
import Candidate.SilPrior.FourthPower.MixedFirstInactiveConductor
import Candidate.SilPrior.FourthPower.MixedOriginalTailCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedRootCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalAllowance CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedFirstLiveSource MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstCutoffs MixedFirstExceptionalNormalization
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail MixedOriginalTailCaps
open OuterFreshSource OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedRootParameters RepairedRawContext RepairedRemainderGeometry
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Arbitrary first subsets cost at most NC squared; used only for caps. -/
theorem first_modulus_norm (η τ : Character) (C D : Id) (hC : C ≠ 0)
    (E : Finset (CommonIndex C D))
    (hmod : τ.modulus = η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72:O)} *
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E * activeConductor C D}) :
    (τ.modulus.absNorm:ℝ) ≤ fixedPresentationCost * (η.modulus.absNorm:ℝ) * (C.absNorm:ℝ)^2 := by
  have he : Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} ∣ C := by
    rw [primeSubsetGenerator, span_idealGenerator]
    have hh : (∏ P ∈ E,P.val) ∣ ∏ P : CommonIndex C D,P.val :=
      Finset.prod_dvd_prod_of_subset E Finset.univ (fun P : CommonIndex C D => P.val) (Finset.subset_univ E)
    rw [common_ideal_product] at hh
    exact hh.trans ((commonRadical_dvd_commonPart C D).trans (commonPart_dvd C D hC))
  have ha : Ideal.span {activeConductor C D} ∣ C := (activeConductor_span_dvd C D).trans (commonPart_dvd C D hC)
  have hEn := CenteredExceptionalCount.norm_le_of_dvd hC he
  have hAn := CenteredExceptionalCount.norm_le_of_dvd hC ha
  have hfixed : 0 ≤ fixedPresentationCost := fixedPresentationCost_pos.le
  rw [hmod, ← Ideal.span_singleton_mul_span_singleton]
  simp only [map_mul, Nat.cast_mul]
  calc
    _ = (fixedPresentationCost*(η.modulus.absNorm:ℝ)) *
        ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}).absNorm:ℝ) *
        ((Ideal.span {activeConductor C D}).absNorm:ℝ) := by unfold fixedPresentationCost; ring
    _ ≤ (fixedPresentationCost*(η.modulus.absNorm:ℝ))*(C.absNorm:ℝ)*(C.absNorm:ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEn (by positivity)) hAn (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem envelope_eq_normcap {κ : Type u} [Fintype κ] (r : Source κ (1/4) (9/4)) :
    secondSourceEnvelope r = sourceNormCap r.P (9/4) r.T r.d := by
  have hp : 1 ≤ (2:ℝ)^Fintype.card κ := one_le_pow₀ (by norm_num)
  have hc : 1 ≤ (9/4:ℝ)^2 * (2:ℝ)^Fintype.card κ :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hp
  rw [sharp_support_factored]
  unfold secondSourceEnvelope capConstant effectiveVolume
  rw [max_eq_right hc]

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀)

theorem root_product : (∏ i, d.root.P i) = Z^(∑ i, d.w i) := by
  simp_rw [d.hcanonical.2.2.2.2]
  exact (Real.rpow_sum_of_pos (zero_lt_one.trans d.one_lt_Z) _ _).symm

theorem root_product_cap : (∏ i, d.root.P i) ≤ Z := by
  rw [root_product M H hH d]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
    (show (∑ i, d.w i) ≤ (1:ℝ) by linarith [d.hface.2.1])

theorem root_volume_log : Real.logb Z (sourceVolume d.root) = Real.logb Z d.root.T + ∑ i, d.w i := by
  have hp : 0 < ∏ i, d.root.P i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (d.root.hP i))
  change Real.logb Z (d.root.X₁*d.root.X₂*(∏ i,d.root.P i)) = _
  rw [d.root.hpX, Real.logb_mul d.root.total_pos.ne' hp.ne', root_product M H hH d,
    Real.logb_rpow (zero_lt_one.trans d.one_lt_Z) d.one_lt_Z.ne']

theorem root_volume_cap : sourceVolume d.root ≤ Z := by
  have hv := face_volume d.hface
  rw [← root_volume_log M H hH d] at hv
  have he := Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
    (show Real.logb Z (sourceVolume d.root) ≤ (1:ℝ) by norm_num [rootReserve] at hv; linarith)
  simpa only [Real.rpow_logb (zero_lt_one.trans d.one_lt_Z) d.one_lt_Z.ne' (sourceVolume_pos d.root),
    Real.rpow_one] using he

theorem root_volume_inverse : (sourceVolume d.root)⁻¹ ≤ Z^(2:ℝ) := by
  have hp := Real.one_le_rpow d.one_lt_Z.le d.hell
  have hL : (2/9:ℝ) ≤ d.root.L := (le_mul_of_one_le_right (by norm_num) hp).trans d.hminimum
  have hx := hL.trans d.root.hX₁
  have hy := hL.trans d.root.hX₂
  have hprod : 1 ≤ ∏ i, d.root.P i := Finset.one_le_prod₀ (fun i _ => d.root.hP i)
  have hv : (4/81:ℝ) ≤ sourceVolume d.root := by
    have hh : (4/81:ℝ) ≤ d.root.X₁*d.root.X₂ := by nlinarith
    exact hh.trans (le_mul_of_one_le_right (by nlinarith : 0 ≤ d.root.X₁*d.root.X₂) hprod)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4/81) hv
  have hi' : (sourceVolume d.root)⁻¹ ≤ (81/4:ℝ) := by simpa only [one_div, inv_div] using hi
  apply hi'.trans
  rw [Real.rpow_two]
  nlinarith [d.hZ]

theorem root_norm_cap_two (hcard : Fintype.card ι ≤ N)
    (hconst : (9/4:ℝ)^2 * (2:ℝ)^N ≤ Z) :
    sourceNormCap d.root.P (9/4) d.root.T d.root.d ≤ Z^(2:ℝ) := by
  rw [sharp_support_factored, d.hunit]
  simp only [pairNorm, map_one, Nat.cast_one, one_mul, div_one]
  have hc : (9/4:ℝ)^2 * (2:ℝ)^Fintype.card ι ≤ Z :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcard) (sq_nonneg _)).trans hconst
  apply (mul_le_mul hc (root_volume_cap M H hH d) (sourceVolume_pos d.root).le (zero_lt_one.trans d.one_lt_Z).le).trans_eq
  rw [Real.rpow_two]
  ring

theorem common_norm_caps (hcard : Fintype.card ι ≤ N)
    (hconst : (9/4:ℝ)^2 * (2:ℝ)^N ≤ Z)
    (p : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)) :
    (p.val.1.absNorm:ℝ) ≤ Z^(2:ℝ) ∧ (p.val.2.absNorm:ℝ) ≤ Z^(2:ℝ) := by
  have hcap := root_norm_cap_two M H hH d hcard hconst
  have hp := commonLabel_norm_bounds (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1)
    (sourceNormCap d.root.P (9/4) d.root.T d.root.d)
    (fun I _ hI => (original_coefficient_cap d.root (by norm_num) 1 I hI).2) _ _ p.property
  exact ⟨hp.1.trans hcap,hp.2.trans hcap⟩

theorem first_modulus_cap (hcard : Fintype.card ι ≤ N)
    (hconst : (9/4:ℝ)^2 * (2:ℝ)^N ≤ Z) (hfixed : fixedPresentationCost ≤ Z)
    (p : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1))
    (E : Finset (CommonIndex p.val.1 p.val.2)) (τ : Character)
    (hmod : τ.modulus = η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72:O)} *
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex p.val.1 p.val.2 => P.val) E * activeConductor p.val.1 p.val.2}) :
    (τ.modulus.absNorm:ℝ) ≤ Z^(6:ℝ) := by
  have hsupp := commonLabels_supported _ _ _ p.property
  have hc := (common_norm_caps M H hH d hcard hconst p).1
  have hηcap := d.hη
  have hz := zero_lt_one.trans d.one_lt_Z
  apply (first_modulus_norm η τ p.val.1 p.val.2 hsupp.1.1 E hmod).trans
  calc
    _ ≤ Z*Z*(Z^(2:ℝ))^2 := by gcongr
    _ = _ := by norm_num [Real.rpow_natCast, pow_succ]; ring

theorem child_inverse_cap (hε : 0 < ε) (hcard : Fintype.card ι ≤ N)
    (hconst : (9/4:ℝ)^2 * (2:ℝ)^N ≤ Z)
    (p : ActiveLabel (sourceColumns d.root) (sourceCoefficient d.root (by norm_num) 1))
    (E : Finset (CommonIndex p.val.1 p.val.2)) (n : ℤ) :
    (nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss N ε) n)⁻¹ ≤ Z^(10:ℝ) := by
  have hs := commonLabels_supported _ _ _ p.property
  have hCD : CompletedGauss.primeSupport p.val.1 = CompletedGauss.primeSupport p.val.2 :=
    (commonLabels_data _ _ _ _ p.property).2.2
  have hc := (common_norm_caps M H hH d hcard hconst p).1
  have hv := sourceVolume_pos d.root
  have hk := d.radial_pos
  have hz : 0 < Z := zero_lt_one.trans d.one_lt_Z
  have hkcap := d.hKcap
  have hC : 0 < (p.val.1.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hs.1.1)
  have hpad : 0 ≤ cutoffLoss N ε := (internal_losses_paid N ε hε).1.le
  have hfloor := child_floor p.val.1 p.val.2 hs.1 hs.2 hCD E d.Kroot (sourceVolume d.root) Z
    (cutoffLoss N ε) d.radial_pos hv d.one_lt_Z hpad n
  have hpos : 0 < (sourceVolume d.root)^2/(d.Kroot*(p.val.1.absNorm:ℝ)^2) := by positivity
  have hi := one_div_le_one_div_of_le hpos hfloor
  have hi' : (nominalChildScale p.val.1 p.val.2 E d.Kroot (sourceVolume d.root) Z (cutoffLoss N ε) n)⁻¹ ≤
      d.Kroot*(p.val.1.absNorm:ℝ)^2*((sourceVolume d.root)⁻¹)^2 := by
    convert hi using 1 <;> field_simp [hv.ne',d.radial_pos.ne',hC.ne'] <;> ring
  apply hi'.trans
  calc
    _ ≤ Z^(2:ℝ)*(Z^(2:ℝ))^2*(Z^(2:ℝ))^2 := by
      have hvinv := root_volume_inverse M H hH d
      gcongr
    _ = _ := by norm_num [Real.rpow_natCast, pow_succ]; ring

end
end Candidate.SilPrior.FourthPower.RepairedRootCaps
