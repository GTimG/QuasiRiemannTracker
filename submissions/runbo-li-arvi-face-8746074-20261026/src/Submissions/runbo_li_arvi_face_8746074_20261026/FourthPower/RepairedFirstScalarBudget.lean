/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first-allocation scalar gates for the repaired RAW budget. The
full first common norm and its canonical allowance are retained. These
are consequences of the literal first allocation and retained scale.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedLargeSupplierBudget
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRawReferenceScale
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstLiveRemainders

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedFirstScalarBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentAllocationCost
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentFirstPhysicalSource
open CenteredMomentFirstMixedAllowance
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiveNormalization
open MixedFirstNonexceptionalAllocation MixedFirstExceptionalNormalization MixedFirstGeometricCaps
open MixedInnerExceptionalBlock MixedFirstCutoffs
open RepairedRawContext RepairedFirstPoint RepairedRootParameters RepairedRootCaps RepairedCapEvent
open RepairedRawReference RepairedSupplierSplit RepairedRawReferenceScale RepairedSupplierProfiles
open CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization
open MixedCommonEnergy
open MixedFirstChosenEnergy
open MixedPrincipalCentered
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}

-- Keep the checked Point constructor's concrete classical index instance.
local instance (priority := 2000) (p : Point d) : DecidableEq p.Index := Classical.decEq _

def scalar (p : Point d) : ℝ := ‖firstScalar d.root p.label.val.1 p.allocation‖^2
def ref (p : Point d) : ℝ := reference p.tau p.label.val.1 p.label.val.2 (sourceVolume d.root) Z

theorem ref_pos (p : Point d) : 0 < ref p := by
  have hC := (commonLabels_supported _ _ _ p.label.property).1
  have hc := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hv := sourceVolume_pos d.root
  have ht := zero_lt_one.trans_le (ideal_norm_one_le p.tau.modulus_ne_bot)
  have hz := zero_lt_one.trans d.one_lt_Z
  unfold ref reference
  positivity

theorem frozen_scalar_cap (p : Point d) (hcard : Fintype.card ι ≤ N) (hKslot : 1 ≤ Kslot) :
    scalar p ≤ Kslot^(2*N) := by
  have hcoef := frozenCoefficient_norm p.allocation.val p.label.val.1 d.root.R d.root.ν d.root.Wslot d.root.P
    d.root.M d.root.hν d.root.hWnorm d.root.hM
  have hnorm := (frozen_scalar_norm_le (punctureProduct d.root.S d.root.H) p.allocation.val
    (frozenCoefficient p.allocation.val p.label.val.1 d.root.R d.root.ν d.root.Wslot d.root.P)).trans hcoef
  have hm := product_slot_cap d.root.M N Kslot hcard hKslot
    (fun i => zero_le_one.trans (d.root.hM i)) d.hM
  apply (pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hm) 2).trans_eq
  rw [← pow_mul]
  congr 1
  omega

theorem first_volume_cap (p : Point d) (hcard : Fintype.card ι ≤ N) :
    sourceVolume p.source / pairNorm p.source.d ≤
      (2:ℝ)^N*sourceVolume d.root/(p.label.val.1.absNorm:ℝ) := by
  have hB := (allocation_data (tuplePools d.root) p.label.val.1 p.allocation.val
    (Finset.mem_filter.mp p.allocation.property).1).1
  have hprod := (Finset.mem_filter.mp p.allocation.property).2
  have hP : ∀ i,0 < d.root.P i := fun i => zero_lt_one.trans_le (d.root.hP i)
  have hC := (commonLabels_supported _ _ _ p.label.property).1
  have hc := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hred := rawReduction_pos p.allocation.val hB d.root.P hP
  have hredcap := (actual_reduction_norm p.allocation.val hB p.label.val.1 d.root.R hprod
    d.root.ν d.root.Wslot d.root.P hP 1 2 zero_lt_one d.root.hW p.frozen_nonzero).2
  rw [max_eq_right (by norm_num : (1:ℝ) ≤ 2)] at hredcap
  have hi : (1:ℝ)/rawReduction p.allocation.val d.root.P ≤ (2:ℝ)^N/(p.label.val.1.absNorm:ℝ) := by
    apply (div_le_div_iff₀ hred hc).mpr
    simpa only [one_mul] using hredcap.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) hred.le)
  have he := live_volume_ratio p.allocation.val hB d.root.d d.root.T d.root.P hP
  have hvol : sourceVolume p.source / pairNorm p.source.d =
      sourceVolume d.root/rawReduction p.allocation.val d.root.P := by
    change (d.root.X₁*d.root.X₂*(∏ i : p.Index,d.root.P i.val)) /
      pairNorm (d.root.d.1*p.allocation.val (Sum.inr 0),d.root.d.2*p.allocation.val (Sum.inr 1)) = _
    rw [d.root.hpX,he]
    simp only [d.hunit,pairNorm,map_one,Nat.cast_one,one_mul,div_one]
    rw [← d.root.hpX]
    rfl
  rw [hvol,div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hi (sourceVolume_pos d.root).le
  convert hh using 1 <;> ring

theorem base_le_reference (p : Point d) :
    referenceBase p.tau p.label.val.1 (sourceVolume d.root) ≤ ref p := by
  let B := (p.tau.modulus.absNorm:ℝ)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hallow : 1 ≤ Z^(allowance p.label.val.1 p.label.val.2 Z) :=
    Real.one_le_rpow d.one_lt_Z.le (allowance_nonneg _ _ _)
  calc
    _ = B/fixedPresentationCost := rfl
    _ ≤ B := div_le_self hB fixed_presentation_one_le
    _ ≤ B*Z^(allowance p.label.val.1 p.label.val.2 Z) := le_mul_of_one_le_right hB hallow
    _ = _ := rfl

theorem allocation_shape_identity (p : Point d) :
    scalar p*shape (sourceVolume p.source) (pairNorm p.source.d) (prefixNormMax p.source.d) p.source.L p.scale 1 =
      allocationShape d.root p.label.val.1 p.allocation p.scale 1 := by
  unfold scalar firstScalar allocationShape
  change _ = _ * shape (d.root.T*∏ i : p.Index,d.root.P i.val) _ _ _ _ _
  rw [← d.root.hpX]
  rfl

/-- The genuine moving-L estimate is now applied at every actual first
allocation. Its margin pays all later exceptional small powers. -/
theorem exceptional_shape_reference (p : Point d) (hε : 0 < ε) (hevent : Event.{u} N ε Z) :
    scalar p*shape (sourceVolume p.source) (pairNorm p.source.d) (prefixNormMax p.source.d) p.source.L p.scale 1 ≤
      (slotCost d.root*(2/9:ℝ)^(-2/3:ℝ))*ref p*Z^(-9*omegaLoss ε) := by
  have hs := commonLabels_supported _ _ _ p.label.property
  have hCD := (commonLabels_data _ _ _ _ p.label.property).2.2
  have hδ := (internal_losses_paid N ε hε).1.le
  have he := raw_reference_of_lower_minimum d.root d.hunit η p.tau p.label.val.1 p.label.val.2
    hs.1 hs.2 hCD p.inactive p.allocation d.Kroot Z
    (firstCutoff p.label.val.1 p.label.val.2 p.inactive d.Kroot (sourceVolume d.root))
    1 (cutoffLoss N ε) (cutoffLoss N ε) (Real.logb Z (sourceVolume d.root)) d.ell (2/9)
    d.one_lt_Z d.hKlow (by norm_num) hδ (by norm_num) d.hminimum le_rfl p.modulus
    (by simp only [firstCutoff,one_mul]; exact le_rfl) p.index p.retained 1
  simp only [map_one,Nat.cast_one,mul_one,div_one] at he
  have hexp : Real.logb Z (sourceVolume d.root)-5/6-2*d.ell/3+
      5*(frequencyLoss Z 1 (cutoffLoss N ε)+cutoffLoss N ε)/6 ≤ -9*omegaLoss ε := by
    have hi := (internal_spec N ε hε).2.2.1
    have hf := hevent.uniform.2.2.1
    have hm := d.hmargin
    have hω := (omega_spec ε hε).1
    unfold cutoffLoss at hi hf ⊢
    linarith
  have he' := he.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le hexp)
    (mul_nonneg (slotCost_nonneg d.root) (Real.rpow_nonneg (by norm_num) _)))
  change allocationShape d.root p.label.val.1 p.allocation p.scale 1 / ref p ≤ _ at he'
  rw [← allocation_shape_identity p] at he'
  have hh := (div_le_iff₀ (ref_pos p)).mp he'
  convert hh using 1 <;> ring

/-- After the full first-common shortening, the zero term needs only
W≤Z^Sroot. The original3.72 face gives a strict reserve even with this
coarse choice; no selected-width improvement is spent here. -/
theorem zero_geometry_reference (p : Point d) (hε : 0 < ε)
    (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z) :
    p.scale*Z^(∑ i,d.w i)*(sourceVolume p.source/pairNorm p.source.d) ≤ (2:ℝ)^N*ref p := by
  have hs := commonLabels_supported _ _ _ p.label.property
  have hCD := (commonLabels_data _ _ _ _ p.label.property).2.2
  have ht := zero_lt_one.trans_le (ideal_norm_one_le p.tau.modulus_ne_bot)
  have hc := zero_lt_one.trans_le (ideal_norm_one_le hs.1.1)
  have hv := sourceVolume_pos d.root
  have hz := zero_lt_one.trans d.one_lt_Z
  have hk : 0 < p.scale := Real.rpow_pos_of_pos hz _
  have hr := retained_child_ratio η p.tau p.label.val.1 p.label.val.2 hs.1 hs.2 hCD p.inactive
    d.Kroot (sourceVolume d.root) Z
    (firstCutoff p.label.val.1 p.label.val.2 p.inactive d.Kroot (sourceVolume d.root))
    1 (cutoffLoss N ε) (cutoffLoss N ε) d.radial_pos hv d.one_lt_Z (by norm_num)
    (internal_losses_paid N ε hε).1.le p.modulus
    (by simp only [firstCutoff,one_mul]; exact le_rfl) p.index p.retained
  have hinput : 1 ≤ inputWidth η d.Kroot Z := by
    have hK : 1 ≤ Real.logb Z d.Kroot := by
      simpa only [Real.logb_self_eq_one d.one_lt_Z] using Real.logb_le_logb_of_le d.one_lt_Z hz d.hKlow
    have hη := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le η.modulus_ne_bot)
    have hF := Real.logb_nonneg d.one_lt_Z fixed_presentation_one_le
    unfold inputWidth
    linarith
  have hexp : Real.logb Z (sourceVolume d.root)-inputWidth η d.Kroot Z+
      frequencyLoss Z 1 (cutoffLoss N ε)+cutoffLoss N ε+(∑ i,d.w i) ≤ 0 := by
    have hface := d.hface.2.2
    have hS := d.hface.1
    have hvlog := root_volume_log M H hH d
    have hf := hevent.uniform.2.2.1
    have hreserve := original_reserve_paid N ε hε
    have hmesh := (mesh_spec ε hε).1.le
    norm_num [mixedReserve,rootReserve] at hreserve hface
    linarith
  have hratio : (p.scale*(p.label.val.1.absNorm:ℝ)/((p.tau.modulus.absNorm:ℝ)*sourceVolume d.root))*
      Z^(∑ i,d.w i) ≤ 1 := by
    apply (mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hz.le _)).trans
    rw [← Real.rpow_add hz]
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le hexp
  have hscaled : p.scale*Z^(∑ i,d.w i)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ)) ≤
      (p.tau.modulus.absNorm:ℝ)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2 := by
    have he := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg ht.le (sq_nonneg (sourceVolume d.root/(p.label.val.1.absNorm:ℝ))))
    convert he using 1 <;> field_simp [hc.ne',ht.ne',hv.ne'] <;> ring
  have hallow : 1 ≤ Z^(allowance p.label.val.1 p.label.val.2 Z) :=
    Real.one_le_rpow d.one_lt_Z.le (allowance_nonneg _ _ _)
  calc
    _ ≤ p.scale*Z^(∑ i,d.w i)*((2:ℝ)^N*sourceVolume d.root/(p.label.val.1.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left (first_volume_cap p hcard) (mul_nonneg hk.le (Real.rpow_nonneg hz.le _))
    _ = (2:ℝ)^N*(p.scale*Z^(∑ i,d.w i)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))) := by ring
    _ ≤ (2:ℝ)^N*((p.tau.modulus.absNorm:ℝ)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2) :=
      mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ ≤ (2:ℝ)^N*ref p := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_right (mul_nonneg ht.le (sq_nonneg _)) hallow

/-- A coarse polynomial lower reference is sufficient only for the
arbitrary-saving tail. No such coarsening is used on retained/exceptional
components. -/
theorem inverse_reference_cap (p : Point d) (hε : 0 < ε)
    (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z) : (ref p)⁻¹ ≤ Z^(8:ℝ) := by
  have hs := (commonLabels_supported _ _ _ p.label.property).1
  have hc := zero_lt_one.trans_le (ideal_norm_one_le hs.1)
  have hv := sourceVolume_pos d.root
  have hz := zero_lt_one.trans d.one_lt_Z
  have hCcap := (common_norm_caps M H hH d hcard hevent.dimension p.label).1
  have hVcap := root_volume_inverse M H hH d
  have hq : (p.label.val.1.absNorm:ℝ)/sourceVolume d.root ≤ Z^(4:ℝ) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul hCcap hVcap (inv_nonneg.mpr hv.le) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [← Real.rpow_add hz]
    norm_num
  have hq2 : ((p.label.val.1.absNorm:ℝ)/sourceVolume d.root)^2 ≤ Z^(8:ℝ) := by
    apply (pow_le_pow_left₀ (div_nonneg hc.le hv.le) hq 2).trans_eq
    rw [pow_two,← Real.rpow_add hz]
    norm_num
  have hallow : 1 ≤ Z^(allowance p.label.val.1 p.label.val.2 Z) :=
    Real.one_le_rpow d.one_lt_Z.le (allowance_nonneg _ _ _)
  have ht := ideal_norm_one_le p.tau.modulus_ne_bot
  have hb : (sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2 ≤ ref p := by
    calc
      _ ≤ (p.tau.modulus.absNorm:ℝ)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2 :=
        le_mul_of_one_le_left (sq_nonneg _) ht
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hallow
  have hi := (inv_le_inv₀ (ref_pos p) (sq_pos_of_pos (div_pos hv hc))).mpr hb
  apply hi.trans
  convert hq2 using 1 <;> field_simp [hc.ne',hv.ne'] <;> ring

theorem tail_power_reference (p : Point d) (hε : 0 < ε)
    (hcard : Fintype.card ι ≤ N) (hevent : Event.{u} N ε Z) : Z^(-(40:ℝ)) ≤ ref p := by
  have hz := zero_lt_one.trans d.one_lt_Z
  have hi := inverse_reference_cap p hε hcard hevent
  have hh : Z^(-(40:ℝ))/ref p ≤ 1 := by
    calc
      _ = Z^(-(40:ℝ))*(ref p)⁻¹ := div_eq_mul_inv _ _
      _ ≤ Z^(-(40:ℝ))*Z^(8:ℝ) := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hz.le _)
      _ = Z^(-(32:ℝ)) := by rw [← Real.rpow_add hz]; norm_num
      _ ≤ 1 := by
        simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
          (by norm_num : -(32:ℝ) ≤ 0)
  simpa only [one_mul] using (div_le_iff₀ (ref_pos p)).mp hh

end
end Candidate.FourthPower.RepairedFirstScalarBudget
