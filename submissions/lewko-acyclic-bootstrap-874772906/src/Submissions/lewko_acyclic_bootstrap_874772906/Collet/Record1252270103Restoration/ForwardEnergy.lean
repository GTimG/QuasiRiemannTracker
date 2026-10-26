/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.ForwardRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.WeightedEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

def forwardDivisorMass (b X₁ X₂ : ℝ) : ℝ :=
  ∑d∈divisorPool (holePairPool b X₁ X₂), |(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d)

theorem forward_hole_energy_transfer {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (E : ℝ)
    (hE : ∀d∈divisorPool (holePairPool b X₁ X₂),
      ordinaryHoleEnergy η m A t W₁ W₂ b S β P
        (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) keep Φ K ≤ E) :
    squarefreeEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K ≤
      (forwardDivisorMass b X₁ X₂)^2*E := by
  let D := divisorPool (holePairPool b X₁ X₂)
  let w := fun d : IdealPair=>|(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d)
  let c := fun (d : IdealPair) (z : O)=>
    (forwardKernel d.1 d.2:ℂ)*rowWeight η m A z t (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ)
  let f := fun (d : IdealPair) (z : O)=> ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t
    (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)
  let u := fun z : O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hw : ∀d∈D,0≤w d := fun d _=>div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hu : ∀z,0≤u z := by intro z;dsimp [u];split_ifs;exact hΦ _;exact le_rfl
  have hc : ∀d∈D,∀z,‖c d z‖≤w d := by
    intro d hd z
    dsimp [c,w]
    rw [norm_div,norm_mul,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (rowWeight_norm_le_one_all η m A z t _))
      (Real.sqrt_nonneg _)
  have he : ∀d∈D,∀R : Finset O,∑z∈R,‖f d z‖^2*u z≤E := by
    intro d hd R
    exact (ordinary_hole_finite_energy_le η m A W₁ W₂ b S β P t _ _ keep Φ K hK hΦ R).trans (hE d hd)
  have h := Record1252270103Source.weighted_sum_energy_le_uniform D w E c f u hw hu hc he
  change _ ≤ (forwardDivisorMass b X₁ X₂)^2*E at h
  apply le_trans (le_of_eq ?_) h
  unfold squarefreeEnergy
  apply tsum_congr
  intro z
  rw [forward_hole_positive_row η m A z W₁ W₂ b S β P hP t X₁ X₂ hX₁ hX₂]
  dsimp [c,f,u,D]
  split_ifs <;> simp

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.forward_hole_energy_transfer
