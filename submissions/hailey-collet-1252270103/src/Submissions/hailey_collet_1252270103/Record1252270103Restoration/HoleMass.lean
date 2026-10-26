/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.HoleEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators
open OAI Record1252270103KernelMass

theorem subset_half_weight (D : Finset PrimeIdeal) :
    normWeight (1/2) (subsetProduct D)=∏P∈D,(Ideal.absNorm P.val:ℝ)^(-(1/2:ℝ)) := by
  unfold normWeight subsetProduct
  rw [map_prod,Nat.cast_prod]
  exact (Real.finsetProd_rpow D (fun P : PrimeIdeal=>(Ideal.absNorm P.val:ℝ))
    (fun P _=>Nat.cast_nonneg _) _).symm

theorem mobius_half_weight (D : Finset PrimeIdeal×Finset PrimeIdeal) :
    (Real.sqrt (pairNorm (mobiusPair D)))⁻¹=
      normWeight (1/2) (subsetProduct D.1)*normWeight (1/2) (subsetProduct D.2) := by
  have hn := pairNorm_pos (d:=mobiusPair D) (subsetProduct_nonzero D.1) (subsetProduct_nonzero D.2)
  rw [Real.sqrt_eq_rpow,←Real.rpow_neg hn.le]
  unfold normWeight pairNorm mobiusPair
  exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem holeDeletionMass_eq_product :
    holeDeletionMass=∏P∈smallPrimes,(1+(Ideal.absNorm P.val:ℝ)^(-(1/2:ℝ)))^2 := by
  unfold holeDeletionMass
  simp_rw [mobius_half_weight]
  rw [mobiusPool,Finset.sum_product]
  simp only [Prod.fst,Prod.snd]
  rw [←Finset.sum_mul_sum]
  simp_rw [subset_half_weight]
  rw [←Finset.prod_one_add,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  ring

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.holeDeletionMass_eq_product
