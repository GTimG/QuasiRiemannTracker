/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual full-pool and raw-corner support for exceptional first children. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalNormalizedFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialTruncatedCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalChildBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalPoolTransport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedAllocatedNormCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow
open Cycle61InitialMass OAI.SevenEighths.Record1252270103Source
open QRH.Record1252270103Low InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized ForcedCost
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- Every actual sector ideal divides a stored full column. Zero coefficients
are irrelevant: this is a statement about the full finite pool. -/
theorem sector_full_pool_cap (S:Finset (Ideal O))(D:Ideal O)(hD:D≠0)(Y:ℝ)
    (hS:∀I∈S,(I.absNorm:ℝ)≤Y)(I:sectorPool D hD S):
    ((I:Ideal O).absNorm:ℝ)≤Y := by
  have hm: D*(I:Ideal O)∈supportedColumns S :=
    (mem_residualPool D hD _ I).mp (Finset.mem_filter.mp I.property).1
  have hs:=(Finset.mem_filter.mp hm)
  exact (corrected_norm_mono_of_dvd _ _ hs.2.1 (dvd_mul_left (I:Ideal O) D)).trans (hS _ hs.1)

/-- The original reference radius survives an actual first common allocation
with exactly its common-ideal denominator. No positive plain floor is added. -/
theorem child_reference_raw_lower {ι:Type*}[Fintype ι](s:Input ι)(C R:Ideal O)
    (hC:C≠0)(B:actualAllocations s.pools C)(τ:Character)(t L:ℝ)
    (hL:0<L)(hX₁:L≤s.X₁)(hX₂:L≤s.X₂)(hY₁:L≤s.Y₁)(hY₂:L≤s.Y₂):
    0<L/(C.absNorm:ℝ) ∧ L/(C.absNorm:ℝ)≤(child s C R B τ t).X₁ ∧
      L/(C.absNorm:ℝ)≤(child s C R B τ t).X₂ ∧
      L/(C.absNorm:ℝ)≤(child s C R B τ t).Y₁ ∧
      L/(C.absNorm:ℝ)≤(child s C R B τ t).Y₂ := by
  have hN:(0:ℝ)<C.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hl:=child_raw_lower_bound s C R B τ t L hL hX₁ hX₂ hY₁ hY₂
  have hmono:L/(C.absNorm:ℝ)≤L/ordinaryNorm B.val:=
    div_le_div_of_nonneg_left hL.le (zero_lt_one.trans_le (ordinaryNorm_ge_one s C B))
      (ordinaryNorm_le_common s C hC B)
  exact ⟨div_pos hL hN,hmono.trans hl.1,hmono.trans hl.2.1,hmono.trans hl.2.2.1,hmono.trans hl.2.2.2⟩

theorem reference_lower_polynomial (Z L:ℝ)(C:Ideal O)(hZ:1<Z)(hC:C≠0)
    (hL:1≤L)(hCcap:(C.absNorm:ℝ)≤Z^(2:ℝ)):
    Z^(-2:ℝ)≤L/(C.absNorm:ℝ) := by
  have hN:(0:ℝ)<C.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  rw [Real.rpow_neg (zero_lt_one.trans hZ).le,←one_div]
  exact (div_le_div_of_nonneg_left zero_le_one hN hCcap).trans
    (div_le_div_of_nonneg_right hL hN.le)

/-- The full common frequency is a product of two divisors of C. -/
theorem common_frequency_norm_cap (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (heq:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D)):
    ((Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}).absNorm:ℝ)≤
      (C.absNorm:ℝ)^2 := by
  have hG:Ideal.span {commonFrequencyGenerator C D}∣C:=by
    have hd:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD heq).1
    rw [primary_span_supported C hC] at hd
    exact hd
  have hV:nonunitFrequencyGenerator C D U∣primaryGenerator C:=by
    rw [←left_generator_product C D hC heq]
    unfold nonunitFrequencyGenerator
    apply dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>dvd_pow_self _ (ne_of_gt (leftExponent_pos C D P))))
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  have hV':Ideal.span {nonunitFrequencyGenerator C D U}∣C:=by
    have hd:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hV
    rw [primary_span_supported C hC] at hd
    exact hd
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,pow_two]
  exact mul_le_mul (corrected_norm_mono_of_dvd _ C hC.1 hG)
    (corrected_norm_mono_of_dvd _ C hC.1 hV') (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A polynomial common-ideal cap bounds the literal frequency uniformly
over every inactive subset, without selecting nonzero rows. -/
theorem frequency_cap_four (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (heq:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (Z:ℝ)(hZ:0<Z)(hCcap:(C.absNorm:ℝ)≤Z^(2:ℝ)):
    ((Ideal.span {commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U}).absNorm:ℝ)≤Z^(4:ℝ) := by
  apply (common_frequency_norm_cap C D hC hD heq U).trans
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hCcap 2).trans_eq
  rw [←Real.rpow_mul_natCast hZ.le]
  norm_num

/-- Positivity of both generator norms keeps the canonical ball scale below
its true retained radius envelope. -/
theorem retained_scale_cap (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D))
    (radius Z Br:ℝ)(hZ:1≤Z)(hBr:0≤Br)(hr:radius≤Z^Br)(hfour:(4:ℝ)≤Z):
    Cycle61FinalNatural.retainedScale radius C D U≤Z^(Br+1) := by
  have hg:1≤normValue (commonFrequencyGenerator C D):=
    normValue_ge_one _ (commonFrequencyGenerator_ne_zero C D hC)
  have hv:1≤normValue (nonunitFrequencyGenerator C D U):=
    normValue_ge_one _ (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hprod:1≤normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U):=
    one_le_mul_of_one_le_of_one_le hg hv
  unfold Cycle61FinalNatural.retainedScale
  apply max_le (Real.one_le_rpow hZ (by linarith))
  have hupper:4*radius/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U))≤4*Z^Br:=by
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num))
      (zero_le_one.trans hprod)).trans (div_le_self (by positivity) hprod)
  apply hupper.trans
  rw [Real.rpow_add (zero_lt_one.trans_le hZ),Real.rpow_one]
  nlinarith [Real.rpow_nonneg (zero_le_one.trans hZ) Br]

/-- All four raw corners dominate the short reference whenever both original
factors do. This uses the actual equal-product identity, including Y1. -/
theorem long_reference_all_corners (X₁ X₂ Y₁ Y₂:ℝ)
    (hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂)(hl₁:Y₂≤X₁)(hl₂:Y₂≤X₂):
    Y₂≤X₁ ∧ Y₂≤X₂ ∧ Y₂≤Y₁ ∧ Y₂≤Y₂ := by
  have hh:Y₂*Y₂≤X₁*X₂:=mul_le_mul hl₁ hl₂ hY₂.le (hY₂.trans_le hl₁).le
  rw [←hprod] at hh
  exact ⟨hl₁,hl₂,(mul_le_mul_iff_left₀ hY₂).mp hh,le_rfl⟩

end
end QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.sector_full_pool_cap
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.child_reference_raw_lower
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.reference_lower_polynomial
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.common_frequency_norm_cap

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.frequency_cap_four
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.retained_scale_cap
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.long_reference_all_corners
