/- Copyright (c) 2026 Sil. Apache-2.0.
Exact raw zero/tail normalization and original-seed algebra. No analytic
estimate is assumed here. 
-/
import Candidate.FourthPower.RepairedRawExceptional
import Candidate.FourthPower.OuterFreshCompletion
import Candidate.FourthPower.MixedFirstLiveRemainders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRemainderGeometry
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open QRH.Record1252270103KernelMass
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstPhysicalSource
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiveNormalization
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open MixedFirstLiveRemainders
open OuterFreshSource OuterFreshSelected OuterFreshWindowPair OuterFreshAssembly OuterFreshConsumer OuterFreshCompletion
open OuterFreshCutoffAllowance RepairedGroupedConsumer RepairedRawSupplier RepairedRawExceptional
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem grouped_norm_le_average (q : Data ι) (x : Frozen q) (τ : Character)
    (hP : ∀ i, 0 < q.P i) (f : Selected q → ℂ) :
    ‖selectedSum q x τ f‖ ≤ selectedVolume q * average q x τ (fun y => ‖f y‖) := by
  have hw := selectedVolume_pos q hP
  apply (RepairedGroupedConsumer.selected_norm_le q x τ f).trans_eq
  unfold average
  field_simp [hw.ne']

/-- Subunit sharp support forces the actual coefficient to vanish. -/
theorem coefficient_zero_of_cap_lt_one (s : Source ι a b) (ha : 0 < a)
    (seed : Id) (hcap : sourceNormCap s.P b s.T s.d < 1) (I : Id) :
    sourceCoefficient s ha seed I = 0 := by
  by_contra hn
  have hc := original_coefficient_cap s ha seed I hn
  exact (not_le_of_gt hcap) ((ideal_norm_one_le hc.1).trans hc.2)

theorem outer_zero_of_cap_lt_one (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (ha : 0 < a) (hm : Matches q x r ha)
    (seed : Id) (ξ : RayCharacter) (τ : Character) (t K : ℝ)
    (hcap : sourceNormCap r.P b r.T r.d < 1) :
    outerZero q x y r seed τ ξ t K = 0 := by
  have hcoeff (I : Id) : outerColumn q x y seed ξ I = 0 := by
    by_contra hn
    exact (outer_coefficient_nonzero q x y r ha hm seed ξ I hn)
      (coefficient_zero_of_cap_lt_one r ha seed hcap I)
  rw [outerZero_eq_sourceSecondZero]
  simp only [sourceSecondZero, secondZeroEnergy, hcoeff, zero_mul, star_zero,
    mul_zero, Finset.sum_const_zero]

theorem residual_profileCap_le (s : Source ι a b) (ha : 0 < a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    profileCap (residualSource s ha cover u L J x) ≤ profileCap s := by
  have he := residual_slot_mass s ha cover u L J x
  have hp : 0 ≤ 2 * supControl s.W₁ * supControl s.W₂ := by
    have h₁ := supControl_nonneg s.W₁
    have h₂ := supControl_nonneg s.W₂
    positivity
  exact mul_le_mul_of_nonneg_left he hp

theorem sharp_support_factored (s : Source ι a b) :
    sourceNormCap s.P b s.T s.d = b^2 * (2 : ℝ)^Fintype.card ι * (sourceVolume s / pairNorm s.d) := by
  rw [source_cap_factored, ← s.hpX]
  rfl

private theorem linear_seed_scalar (F f seed u T : ℝ)
    (hF : 0 < F) (hf : 0 < f) (hs : 0 < seed) (hu : u = f * seed) (hcap : f ≤ T * F) :
    1 / (F * seed) ≤ T / u := by
  have hu0 : 0 < u := hu.symm ▸ mul_pos hf hs
  apply (div_le_div_iff₀ (mul_pos hF hs) hu0).mpr
  rw [one_mul, hu]
  convert mul_le_mul_of_nonneg_right hcap hs.le using 1 <;> ring

/-- Grouping contributes W, actual selected Cauchy contributes at most
256^N W. Exact sharp support and seed restoration then leave only ONE W.
No first-live or residual volume is silently removed. -/
theorem raw_zero_geometry (s : Source ι a b) (ha : 0 < a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i ∉ Lᶜ})
    (x : Frozen (supplierData s ha u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x ≠ 0)
    (seed : Id) (hseed : seed ≠ 0) (hu : u = frozenProduct (supplierData s ha u L J) x * seed)
    (N : ℕ) (hcard : Fintype.card ι ≤ N) (K : ℝ) (hK : 0 ≤ K) :
    let q := supplierData s ha u L J
    let r := residualSource s ha cover u L J x
    ((activeSelected q).card : ℝ) * selectedVolume q * K * sourceNormCap r.P b r.T r.d /
        (seed.absNorm : ℝ) ≤
      (1024 : ℝ)^N * b^2 * K * selectedVolume q * (sourceVolume s / pairNorm s.d) /
        (u.absNorm : ℝ) := by
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  have hP : ∀ i, 0 < q.P i := fun i => zero_lt_one.trans_le (s.hP i)
  have hF := frozenVolume_pos q hP
  have hW := selectedVolume_pos q hP
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hv := sourceVolume_pos r
  have hrest : Fintype.card (RestIndex q) ≤ N := (rest_card_le q).trans hcard
  have hfrozen : Fintype.card ↥Lᶜ ≤ N :=
    (Fintype.card_le_of_injective (fun i : ↥Lᶜ => i.val) Subtype.val_injective).trans hcard
  have hj : Fintype.card q.J ≤ N := (MixedSelectedVolume.selected_card_le q).trans hcard
  have hsel : ((activeSelected q).card : ℝ) ≤ (256 : ℝ)^N * selectedVolume q :=
    (active_selected_annular_card q (fun i => (hP i).le) (fun i I hI => (s.hpn i I hI).2)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hW.le)
  have hcap : ((frozenProduct q x).absNorm : ℝ) ≤ (2 : ℝ)^N * frozenVolume q :=
    (actual_frozen_window s ha u L J x hx).2.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hfrozen) hF.le)
  have hprod : (u.absNorm : ℝ) = ((frozenProduct q x).absNorm : ℝ) * (seed.absNorm : ℝ) := by
    rw [hu]
    simp only [map_mul, Nat.cast_mul]
    rfl
  have hseedN : 0 < (seed.absNorm : ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hseed)
  have hi := linear_seed_scalar (frozenVolume q) ((frozenProduct q x).absNorm : ℝ)
    (seed.absNorm : ℝ) (u.absNorm : ℝ) ((2 : ℝ)^N) hF
    (zero_lt_one.trans_le (ideal_norm_one_le (frozen_nonzero q x))) hseedN hprod hcap
  have hvol := residual_volume_partition s ha cover u L J x
  have htwo : (2 : ℝ)^Fintype.card (RestIndex q) ≤ (2 : ℝ)^N :=
    pow_le_pow_right₀ (by norm_num) hrest
  have hY : sourceNormCap r.P b r.T r.d ≤ b^2 * (2 : ℝ)^N * (sourceVolume r / pairNorm s.d) := by
    rw [sharp_support_factored]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htwo (sq_nonneg b)) (div_nonneg hv.le hp.le)
  have hY0 : 0 ≤ sourceNormCap r.P b r.T r.d := by
    rw [sharp_support_factored]
    positivity
  calc
    _ ≤ ((256 : ℝ)^N * selectedVolume q) * selectedVolume q * K *
        (b^2 * (2 : ℝ)^N * (sourceVolume r / pairNorm s.d)) / (seed.absNorm : ℝ) := by
      apply div_le_div_of_nonneg_right _ hseedN.le
      gcongr
    _ = ((256 : ℝ)^N * (2 : ℝ)^N * b^2 * K * selectedVolume q *
        (sourceVolume s / pairNorm s.d)) * (1 / (frozenVolume q * (seed.absNorm : ℝ))) := by
      rw [← hvol]
      field_simp [hF.ne', hW.ne', hp.ne', hseedN.ne']
      <;> ring
    _ ≤ ((256 : ℝ)^N * (2 : ℝ)^N * b^2 * K * selectedVolume q *
        (sourceVolume s / pairNorm s.d)) * ((2 : ℝ)^N / (u.absNorm : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hi
      have hs := sourceVolume_pos s
      positivity
    _ = _ := by
      have he : (256 : ℝ)^N * (2 : ℝ)^N * (2 : ℝ)^N = (1024 : ℝ)^N := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      calc
        _ = ((256 : ℝ)^N * (2 : ℝ)^N * (2 : ℝ)^N) * b^2 * K * selectedVolume q *
            (sourceVolume s / pairNorm s.d) / (u.absNorm : ℝ) := by ring
        _ = _ := by rw [he]

end
end Candidate.FourthPower.RepairedRemainderGeometry
