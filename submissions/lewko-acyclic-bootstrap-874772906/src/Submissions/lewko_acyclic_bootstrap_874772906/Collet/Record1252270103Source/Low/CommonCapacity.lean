/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CommonAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.ClippedQuotient
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CapGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Filter
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentEnergyBands
open CenteredMomentEnergyInputParentCapacity QRH.Record12518109Source
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Fixed-support loss; it is independent of allocations, slots and row data. -/
def commonSupportLoss (N : ℕ) (Z plain₁ plain₂ upper : ℝ) : ℝ :=
  Real.logb Z (max 1 plain₁*max 1 plain₂) + (N:ℝ)*Real.logb Z (max 1 upper)

/-- The literal quotient of either equal-product pair is admitted with the same
first-common frozen width. Both actual support witnesses are kept explicit. -/
theorem actual_pair_common_capacity (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (w : α → ℝ)
    (Z t lower upper X₁ X₂ : ℝ) (hZ : 1 < Z)
    (hlower : 0 < lower) (hslo : lower ≤ s.lower) (hshi : s.upper ≤ upper)
    (hscale : ∀i,s.P i = Z^(w i))
    (hfrozen : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hprod : X₁*X₂ = s.X₁*s.X₂)
    (ht : length Z s.X₁ + length Z s.X₂ ≤ t)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hne₁ : s.W₁ ((I.absNorm:ℝ)/(X₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0)
    (hne₂ : s.W₂ ((J.absNorm:ℝ)/(X₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0) :
    length Z (X₁/(B.val (Sum.inr 0)).absNorm) +
      length Z (X₂/(B.val (Sum.inr 1)).absNorm) ≤
      t-Real.logb Z (C.absNorm:ℝ)+firstFrozenWidth B.val w+
        commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper := by
  have hc := clipped_quotient_pair s.W₁ s.W₂ I J Z X₁ X₂
    ((B.val (Sum.inr 0)).absNorm:ℝ) ((B.val (Sum.inr 1)).absNorm:ℝ)
    s.b₁ s.b₂ hZ hX₁ hX₂ (alloc_norm_pos s C B _) (alloc_norm_pos s C B _)
    hI hJ s.support₁ s.support₂ hne₁ hne₂
  have ha := (frozen_width_norm_bounds s C R B w Z lower upper hZ hlower hslo hshi
    hscale hfrozen).2
  have hlog : Real.logb Z (X₁*X₂) ≤ t := by
    rw [hprod,Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne']
    exact (add_le_add (raw_log_le_length Z s.X₁ hZ s.X₁_pos)
      (raw_log_le_length Z s.X₂ hZ s.X₂_pos)).trans ht
  dsimp only [firstNormFrozen,firstPlainReduction] at ha
  dsimp only [commonSupportLoss]
  linarith only [hc,ha,hlog]

/-- A fixed support loss is eventually smaller than any prescribed reserve,
with the threshold chosen before moving common allocations and row data. -/
theorem eventual_common_support_loss (N : ℕ) (plain₁ plain₂ upper ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ 0 ≤ commonSupportLoss N Z plain₁ plain₂ upper ∧
      commonSupportLoss N Z plain₁ plain₂ upper ≤ ε := by
  filter_upwards [CenteredMomentCommonMaskChildCapacity.eventually_fixed_clipping_cost
    plain₁ plain₂ (ε/2) (by linarith),
    eventual_frozen_annular_loss N 1 upper (ε/2) (by norm_num) (by linarith)]
    with Z hz ha
  refine ⟨hz.1,?_,?_⟩
  · apply add_nonneg
    · exact Real.logb_nonneg hz.1
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg hz.1 (le_max_left _ _))
  · dsimp only [commonSupportLoss]
    linarith only [hz.2,ha.2.2]

/-- The strict graph guard pays the actual annular/clipping loss and radial
padding before the minimum cap is formed. -/
theorem raw_loss_cap_nonneg (B lam F t b c delta f loss rho h : ℝ)
    (hB : B ≤ 1) (hlam : 0 < lam) (hd : 0 ≤ delta) (hdc : delta ≤ c)
    (hf : f ≤ b) (hh : 0 ≤ h) (hQ : 0 ≤ F-delta-rho)
    (hguard : loss+B*rho ≤ B*F-t-b) :
    0 ≤ min ((B*(F-delta-rho)-(t-c+f+loss))/lam) (h*(F-delta-rho)) := by
  have hcd : 0 ≤ c-B*delta := by nlinarith only [hB,hd,hdc]
  apply le_min
  · apply div_nonneg _ hlam.le
    nlinarith only [hcd,hf,hguard]
  · exact mul_nonneg hh hQ

/-- Actual nonzero support and the common allocation produce a global source
cap and whole-slot erasure. There are no old positive plain floors or cell gates.
The two chosen ideals only certify support; constants and the erasure choice
remain independent of them. -/
theorem actual_common_global_admission (s : Input α) (C R₀ : Ideal O)
    (B : actualAllocations s.pools C) (w : α → ℝ) (S : Finset α)
    (Z t lower upper b F delta rho B₀ lam h slotMesh : ℝ)
    (hZ : 1 < Z) (hlower : 0 < lower) (hslo : lower ≤ s.lower) (hshi : s.upper ≤ upper)
    (hscale : ∀i,s.P i = Z^(w i))
    (hfrozen : frozenCoefficient B.val C R₀ s.ν s.W s.P ≠ 0)
    (ht : length Z s.X₁ + length Z s.X₂ ≤ t)
    (hw : ∀i,0 ≤ w i) (hwm : ∀i∈S,w i ≤ slotMesh)
    (hS : S ⊆ liveIndices B.val) (htotal : (∑i,w i) ≤ b)
    (hmesh : 0 ≤ slotMesh) (hB : B₀ ≤ 1) (hlam : 0 < lam)
    (hd : 0 ≤ delta) (hdc : delta ≤ Real.logb Z (C.absNorm:ℝ))
    (hh : 0 ≤ h) (hQ : 0 ≤ F-delta-rho)
    (hguard : commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+B₀*rho ≤ B₀*F-t-b) :
    let f := firstFrozenWidth B.val w
    let P := t-Real.logb Z (C.absNorm:ℝ)+f+commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper
    let Q := F-delta-rho
    let cap := min ((B₀*Q-P)/lam) (h*Q)
    ∃ R : Finset α,R ⊆ S ∧
      (∑i∈R,w i) ≤ max 0 (max (b-f-(B₀*Q-P)/lam) (b-f-h*Q))+slotMesh ∧
      ∀ X₁ X₂ : ℝ,0 < X₁ → 0 < X₂ → X₁*X₂ = s.X₁*s.X₂ →
      ∀ I J : Ideal O,I ≠ 0 → J ≠ 0 →
      s.W₁ ((I.absNorm:ℝ)/(X₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0 →
      s.W₂ ((J.absNorm:ℝ)/(X₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0 →
      ∀ n₁ n₂ : ℝ,0 ≤ n₁ → 0 ≤ n₂ →
      n₁ ≤ length Z (X₁/(B.val (Sum.inr 0)).absNorm) →
      n₂ ≤ length Z (X₂/(B.val (Sum.inr 1)).absNorm) →
      (SourceFace.mk B₀ lam 0 B₀ 0 h).Admissible n₁ n₂ (∑i∈S\R,w i) Q := by
  dsimp only
  have hf : firstFrozenWidth B.val w ≤ b :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hw i)).trans htotal
  have hcap := raw_loss_cap_nonneg B₀ lam F t b (Real.logb Z (C.absNorm:ℝ)) delta
    (firstFrozenWidth B.val w) (commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper)
    rho h hB hlam hd hdc hf hh hQ hguard
  obtain ⟨R,hR,hleft,hcost⟩ := global_frozen_erasure B.val w S b
    (min ((B₀*(F-delta-rho)-(t-Real.logb Z (C.absNorm:ℝ)+firstFrozenWidth B.val w+
      commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper))/lam) (h*(F-delta-rho)))
    slotMesh hw hwm hS htotal hmesh hcap
  refine ⟨R,hR,?_,?_⟩
  · simpa only [raw_erasure_cost] using hcost
  · intro X₁ X₂ hX₁ hX₂ hprod I J hI hJ hne₁ hne₂ n₁ n₂ hn₁ hn₂ h₁ h₂
    apply global_first_cap B₀ lam h _ (F-delta-rho) _ _ n₁ n₂ _ hlam
      (actual_pair_common_capacity s C R₀ B w Z t lower upper X₁ X₂ hZ hlower hslo hshi
        hscale hfrozen hX₁ hX₂ hprod ht I J hI hJ hne₁ hne₂)
      hn₁ hn₂ (Finset.sum_nonneg (fun i _=>hw i)) h₁ h₂ hleft

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.actual_pair_common_capacity
#print axioms QRH.Record1252270103Low.eventual_common_support_loss
#print axioms QRH.Record1252270103Low.actual_common_global_admission
