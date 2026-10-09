import QRH.PrimeRows.OptimizedCentralCost
import OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError
import QRH.Geometry
import OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual cube transport at optimized scales; original row objects unchanged. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.QRHPhysicalTails
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_prime_tuple_count {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=QRH.ell)
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^QRH.ell := by
  have hQRH : QRH.h≤9/10 := by norm_num [QRH.h,QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hlx : 0≤QRH.lx ∧ QRH.lx≤1 := by norm_num [QRH.lx,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hly : 0≤QRH.ly := by norm_num [QRH.ly,QRH.M,QRH.b,QRH.ell,QRH.theta]
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


end SevenEighths.QRHPhysicalTails
end
end OAI
