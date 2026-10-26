/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.HoleRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.FullEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem hole_positive_row {ι : Type*} [Fintype ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂ =
      ∑D∈mobiusPool,
        (mobiusSign D*rowWeight η m A z t ((mobiusPair D).1*(mobiusPair D).2)/
          (Real.sqrt (pairNorm (mobiusPair D)):ℂ))*
          positiveSlotRow η m A z W₁ W₂ S β P t
            (X₁/Ideal.absNorm (mobiusPair D).1) (X₂/Ideal.absNorm (mobiusPair D).2) := by
  unfold ordinaryHolePositiveSlotRow
  rw [hole_plain_mobius,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hdi := subsetProduct_nonzero D.1
  have hdj := subsetProduct_nonzero D.2
  have hi := shorten_positive hX₁ hdi
  have hj := shorten_positive hX₂ hdj
  rw [←ordinary_product_eq_pair_sum η m A z t W₁ W₂ b (X₁/Ideal.absNorm (mobiusPair D).1) (X₂/Ideal.absNorm (mobiusPair D).2) hi.1 hj.1 hs₁ hs₂]
  unfold positiveSlotRow
  have hv : 0<X₁*X₂*∏i,P i := mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hn := pairNorm_pos (d:=mobiusPair D) hdi hdj
  have heq : (X₁/(Ideal.absNorm (mobiusPair D).1:ℝ))*(X₂/(Ideal.absNorm (mobiusPair D).2:ℝ))*∏i,P i=
    (X₁*X₂*∏i,P i)/pairNorm (mobiusPair D) := by unfold pairNorm;ring
  rw [heq,normalized_divisor_identity _ _ hv hn]
  ring

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.hole_positive_row
