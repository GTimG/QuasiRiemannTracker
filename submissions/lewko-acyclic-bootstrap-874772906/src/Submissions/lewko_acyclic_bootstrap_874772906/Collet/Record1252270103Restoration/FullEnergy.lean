/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.SmallEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.MassBounds

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentInductionEnergy
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

def restorationMassBound (δ B U : ℝ) : ℝ :=
  ordinaryPrimeMassBound smallPrimes *
    ((eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1)))*U^δ)

theorem shorten_positive {X : ℝ} (hX : 0<X) {I : Ideal O} (hI : I≠0) :
    0<X/(Ideal.absNorm I:ℝ) ∧ X/(Ideal.absNorm I:ℝ)≤X := by
  have hN := ideal_norm_one_le hI
  exact ⟨div_pos hX (lt_of_lt_of_le zero_lt_one hN),div_le_self hX.le hN⟩

/-- Restoration consumes genuine squarefree energies at shorter plain lengths.
The profiles, marked ideals, character, keep predicate, radial weight and height
parameters are identical throughout both exact finite decompositions. -/
theorem restoration_energy_transfer {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (E : ℝ) (hEn : 0≤E)
    (δ B U : ℝ) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U) (hcut : b^2*X₁*X₂≤U^B)
    (hE : ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
      squarefreeEnergy η m A t W₁ W₂ b S β P Y₁ Y₂ keep Φ K ≤ E) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤
      (restorationMassBound δ B U)^2*E := by
  let L := (eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1)))*U^δ
  have hL : 0≤L := mul_nonneg
    (add_nonneg (eulerBound_pos _ _).le (eulerBound_pos _ _).le)
    (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have h := small_energy_transfer η m A W₁ W₂ b hs₁ hs₂ S β P hP t X₁ X₂ hX₁ hX₂
    keep Φ K hK hΦ (L^2*E) (mul_nonneg (sq_nonneg _) hEn) ?_
  · apply h.trans_eq
    unfold restorationMassBound
    dsimp [L]
    ring
  intro d hd
  have hdn := smallPool_nonzero hd
  have hy₁ := shorten_positive hX₁ hdn.1
  have hy₂ := shorten_positive hX₂ hdn.2
  have hcut' : b^2*(X₁/(Ideal.absNorm d.1:ℝ))*(X₂/(Ideal.absNorm d.2:ℝ))≤U^B := by
    apply le_trans _ hcut
    have hmul := mul_le_mul hy₁.2 hy₂.2 hy₂.1.le hX₁.le
    nlinarith [sq_nonneg b]
  have hinv := inverse_hole_energy_transfer η m A W₁ W₂ b S β P hP t _ _ hy₁.1 hy₂.1
    keep Φ K hK hΦ E ?_
  · exact hinv.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (inverseDivisorMass_nonneg _ _ _)
        (inverseDivisorMass_rankin δ B U b _ _ hδ hB hU hcut') 2) hEn)
  intro e he
  have hen := divisorPool_hole_good he
  have hz₁ := shorten_positive hy₁.1 hen.1
  have hz₂ := shorten_positive hy₂.1 hen.2.1
  exact hE _ _ hz₁.1 hz₂.1 (hz₁.2.trans hy₁.2) (hz₂.2.trans hy₂.2)

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.restoration_energy_transfer
