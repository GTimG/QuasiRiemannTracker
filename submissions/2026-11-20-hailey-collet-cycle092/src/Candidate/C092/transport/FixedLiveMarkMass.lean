/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Sum the actual surviving marked assignments after both allocations.
Injectivity, punctures and character zeros can only reduce this absolute sum. -/
import Candidate.C092.transport.FixedCubeGaussColoredH8Projection
import Candidate.C092.transport.FixedCubeGaussActiveMarks
import Candidate.C092.transport.FixedMarkedVolume
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentCounting CenteredMomentSourceMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
namespace QRH.Cycle092.FixedCubeGauss
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

lemma frozen_scalar_bound {ι : Type*} [Fintype ι] (χ : Character) (R : Id) (pool : ι→Finset Id)
    (ν : ι→Id→ℂ) (W : ι→ℝ→ℂ) (P A : ι→ℝ) (p : (i:ι)→pool i)
    (hν : ∀ i, ‖ν i (p i).val‖≤1) (hW : ∀ i, ‖W i ((p i).val.absNorm/P i)‖≤A i) :
    ‖canonicalFrozenScalar χ R pool ν W P p‖ ≤ ∏ i,A i := by
  have hA (i) : 0≤A i := (norm_nonneg _).trans (hW i)
  unfold canonicalFrozenScalar
  split_ifs
  · rw [norm_mul,norm_prod]
    apply (mul_le_of_le_one_right (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (idealCoeff_norm_le_one ..)).trans
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν i)).trans (hW i)
  · rw [norm_zero]; exact Finset.prod_nonneg (fun i _ => hA i)

lemma live_mark_mass {ι : Type*} [Fintype ι] (χ : Character) (R : Id) (pool : ι→Finset Id)
    (ν : ι→Id→ℂ) (W : ι→ℝ→ℂ) (P A : ι→ℝ)
    (hP : ∀i,0<P i) (hA : ∀i,0≤A i)
    (hpool : ∀ i, pool i ⊆ idealBall (2*P i))
    (hν : ∀ i I,I ∈ pool i → ‖ν i I‖≤1)
    (hW : ∀ i I,I ∈ pool i → ‖W i ((I.absNorm:ℝ)/P i)‖≤A i) :
    (∑ p : (i:ι)→pool i,‖canonicalFrozenScalar χ R pool ν W P p‖) ≤ ∏ i,256*A i*P i := by
  calc
    _ ≤ ∑ _p : (i:ι)→pool i, ∏ i,A i := Finset.sum_le_sum (fun p _ =>
      frozen_scalar_bound χ R pool ν W P A p (fun i => hν i _ (p i).property) (fun i => hW i _ (p i).property))
    _ = (∏ i,((pool i).card:ℝ))*(∏ i,A i) := by simp [Fintype.card_pi]
    _ = ∏ i,((pool i).card:ℝ)*A i := (Finset.prod_mul_distrib ..).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hA i))
      intro i _
      have hcard := (Nat.cast_le.mpr (Finset.card_le_card (hpool i))).trans
        (idealBall_card (2*P i) (by have := hP i; positivity))
      exact (mul_le_mul_of_nonneg_right hcard (hA i)).trans_eq (by ring)

local instance c092LocalInst_Candidate_C092_transport_FixedLiveMarkMass_a71d32affee254bc_001 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _
set_option maxHeartbeats 900000 in
theorem residual_mark_mass {ι : Type*} [Fintype ι] {a b : ℝ} (r : Source ι a b)
    (D : QRH.Cycle092.SignedCenter.FixedCubeDatum) (G L : Id) (B : commonAlloc r G)
    (E : fullPrimaryAlloc r G B L) (v : ℝ) :
    (∑ p : (i : CenteredMomentCommonProfile.liveIndices E.val) → ↥(r.pool i.val.val),
      ‖canonicalFrozenScalar D.row.χ ((r.R*G)*L) (fun i : CenteredMomentCommonProfile.liveIndices E.val => r.pool i.val.val)
        (fun i => shiftedSlotCoefficient r v i.val.val) (fun i => r.Wslot i.val.val) (fun i => r.P i.val.val) p‖) ≤
      ∏ i : CenteredMomentCommonProfile.liveIndices E.val,256*r.M i.val.val*r.P i.val.val := by
  let pool := fun i : CenteredMomentCommonProfile.liveIndices E.val => r.pool i.val.val
  convert live_mark_mass D.row.χ ((r.R*G)*L) pool (fun i => shiftedSlotCoefficient r v i.val.val)
    (fun i => r.Wslot i.val.val) (fun i => r.P i.val.val) (fun i => r.M i.val.val)
    (fun i => zero_lt_one.trans_le (r.hP _)) (fun i => zero_le_one.trans (r.hM _))
    (fun i I hI => (mem_idealBall _ _).mpr ⟨(r.hp _ I hI).ne_zero,(r.hpn _ I hI).2⟩)
    (fun i I hI => shiftedSlotCoefficient_norm_le_one r v _ _ (r.hp _ I hI).ne_zero)
    (fun i I _ => r.hWnorm _ _) using 1
  apply Finset.sum_congr
  · ext p; simp
  · intro p hp; rfl

#print axioms residual_mark_mass
end QRH.Cycle092.FixedCubeGauss
end
