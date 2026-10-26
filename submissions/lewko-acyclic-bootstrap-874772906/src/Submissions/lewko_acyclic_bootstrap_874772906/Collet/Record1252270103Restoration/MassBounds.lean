/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.CompletedEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentSourceMass Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem norm_le_of_ideal_dvd {I d : Ideal O} (hI : I≠0) (hd : d∣I) :
    (Ideal.absNorm d:ℝ)≤Ideal.absNorm I := by
  have hdz := ne_zero_of_dvd_ne_zero hI hd
  have hcz := idealCofactor_ne_zero hI hd
  have he := congrArg (fun J : Ideal O=>(Ideal.absNorm J:ℝ)) (idealCofactor_mul hd)
  simp only [map_mul,Nat.cast_mul] at he
  have hco := ideal_norm_one_le hcz
  have hn : 0≤(Ideal.absNorm d:ℝ) := Nat.cast_nonneg _
  nlinarith

theorem divisorPool_norm_bound {b X₁ X₂ : ℝ} {d : IdealPair}
    (hd : d∈divisorPool (holePairPool b X₁ X₂)) : pairNorm d≤b^2*X₁*X₂ := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨n,hn,hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨e,he,hpe⟩ := Finset.mem_image.mp hp
  have hnz := holePairPool_good hn
  have hpool := Finset.mem_product.mp (Finset.mem_filter.mp hn).1
  have hi := norm_le_of_ideal_dvd hnz.1 ((OAI.IdealMobiusDivisorSum.mem_idealDivisors hnz.1).mp (Finset.mem_product.mp he).1)
  have hj := norm_le_of_ideal_dvd hnz.2.1 ((OAI.IdealMobiusDivisorSum.mem_idealDivisors hnz.2.1).mp (Finset.mem_product.mp he).2)
  have hb₁ := (mem_idealBall _ _).mp hpool.1 |>.2
  have hb₂ := (mem_idealBall _ _).mp hpool.2 |>.2
  have hne : p.1=e := congrArg Prod.fst hpe.symm
  rw [hne]
  unfold pairNorm
  calc
    _ ≤ (b*X₁)*(b*X₂) := mul_le_mul (hi.trans hb₁) (hj.trans hb₂)
      (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hb₁)
    _ = _ := by ring

theorem inverseDivisorMass_nonneg (b X₁ X₂ : ℝ) : 0 ≤ inverseDivisorMass b X₁ X₂ := by
  apply Finset.sum_nonneg
  intro d hd
  exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem inverseDivisorMass_rankin (ε B U b X₁ X₂ : ℝ) (hε : 0<ε) (hB : 0≤B) (hU : 1≤U)
    (hcut : b^2*X₁*X₂≤U^B) :
    inverseDivisorMass b X₁ X₂ ≤
      (eulerBound 5 (1/2+ε/(B+1))+eulerBound 432 (1/2+ε/(B+1)))*U^ε := by
  apply le_trans _ (good_absolute_rankin_nonnegative ε B U hε hB hU
    (divisorPool (holePairPool b X₁ X₂)) (fun d hd=>divisorPool_hole_good hd)
      (fun d hd=>(divisorPool_norm_bound hd).trans hcut))
  apply Finset.sum_le_sum
  intro d hd
  exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) (Real.sqrt_nonneg _)

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.inverseDivisorMass_rankin
