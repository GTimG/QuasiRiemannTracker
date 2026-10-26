/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.CommonCapacity

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

/-- Actual nonzero support and the common allocation produce a global source
cap and whole-slot erasure. There are no old positive plain floors or cell gates.
The two chosen ideals only certify support; constants and the erasure choice
remain independent of them. -/
theorem actual_common_rounded_admission (s : Input α) (C R₀ : Ideal O)
    (B : actualAllocations s.pools C) (w : α → ℝ) (S : Finset α)
    (Z t lower upper b F delta rho B₀ lam h slotMesh plainRound : ℝ)
    (hZ : 1 < Z) (hlower : 0 < lower) (hslo : lower ≤ s.lower) (hshi : s.upper ≤ upper)
    (hscale : ∀i,s.P i = Z^(w i))
    (hfrozen : frozenCoefficient B.val C R₀ s.ν s.W s.P ≠ 0)
    (ht : length Z s.X₁ + length Z s.X₂ ≤ t)
    (hw : ∀i,0 ≤ w i) (hwm : ∀i∈S,w i ≤ slotMesh)
    (hS : S ⊆ liveIndices B.val) (htotal : (∑i,w i) ≤ b)
    (hmesh : 0 ≤ slotMesh) (hround : 0 ≤ plainRound) (hB : B₀ ≤ 1) (hlam : 0 < lam)
    (hd : 0 ≤ delta) (hdc : delta ≤ Real.logb Z (C.absNorm:ℝ))
    (hh : 0 ≤ h) (hQ : 0 ≤ F-delta-rho)
    (hguard : (commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+2*plainRound)+B₀*rho ≤ B₀*F-t-b) :
    let f := firstFrozenWidth B.val w
    let P := t-Real.logb Z (C.absNorm:ℝ)+f+(commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+2*plainRound)
    let Q := F-delta-rho
    let cap := min ((B₀*Q-P)/lam) (h*Q)
    ∃ R : Finset α,R ⊆ S ∧
      (∑i∈R,w i) ≤ max 0 (max (b-f-(B₀*Q-P)/lam) (b-f-h*Q))+slotMesh ∧
      ∀ X₁ X₂ : ℝ,0 < X₁ → 0 < X₂ → X₁*X₂ = s.X₁*s.X₂ →
      ∀ I J : Ideal O,I ≠ 0 → J ≠ 0 →
      s.W₁ ((I.absNorm:ℝ)/(X₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0 →
      s.W₂ ((J.absNorm:ℝ)/(X₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0 →
      ∀ n₁ n₂ : ℝ,0 ≤ n₁ → 0 ≤ n₂ →
      n₁ ≤ length Z (X₁/(B.val (Sum.inr 0)).absNorm)+plainRound →
      n₂ ≤ length Z (X₂/(B.val (Sum.inr 1)).absNorm)+plainRound →
      (SourceFace.mk B₀ lam 0 B₀ 0 h).Admissible n₁ n₂ (∑i∈S\R,w i) Q := by
  dsimp only
  have hf : firstFrozenWidth B.val w ≤ b :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hw i)).trans htotal
  have hcap := raw_loss_cap_nonneg B₀ lam F t b (Real.logb Z (C.absNorm:ℝ)) delta
    (firstFrozenWidth B.val w) ((commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+2*plainRound))
    rho h hB hlam hd hdc hf hh hQ hguard
  obtain ⟨R,hR,hleft,hcost⟩ := global_frozen_erasure B.val w S b
    (min ((B₀*(F-delta-rho)-(t-Real.logb Z (C.absNorm:ℝ)+firstFrozenWidth B.val w+
      (commonSupportLoss (Fintype.card α) Z s.b₁ s.b₂ upper+2*plainRound)))/lam) (h*(F-delta-rho)))
    slotMesh hw hwm hS htotal hmesh hcap
  refine ⟨R,hR,?_,?_⟩
  · simpa only [raw_erasure_cost] using hcost
  · intro X₁ X₂ hX₁ hX₂ hprod I J hI hJ hne₁ hne₂ n₁ n₂ hn₁ hn₂ h₁ h₂
    have hpair := actual_pair_common_capacity s C R₀ B w Z t lower upper X₁ X₂ hZ hlower hslo hshi
      hscale hfrozen hX₁ hX₂ hprod ht I J hI hJ hne₁ hne₂
    apply global_first_cap B₀ lam h _ (F-delta-rho)
      (length Z (X₁/(B.val (Sum.inr 0)).absNorm)+plainRound)
      (length Z (X₂/(B.val (Sum.inr 1)).absNorm)+plainRound) n₁ n₂ _ hlam
      (by linarith only [hpair]) hn₁ hn₂ (Finset.sum_nonneg (fun i _=>hw i)) h₁ h₂ hleft

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.actual_common_rounded_admission
