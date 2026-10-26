/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonSummation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103KernelMass QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O

theorem newtonDivisorPair_product (S A : Finset (Ideal O)) (hA : A⊆S) :
    (newtonDivisorPair S A).1*(newtonDivisorPair S A).2=∏p∈S,p := by
  exact (mul_comm _ _).trans (Finset.prod_sdiff hA)

theorem newton_frozen_norm_bound (P S A : Finset (Ideal O))
    (hS : S⊆P) (hA : A⊆S) (depth : ℕ) (hdepth : S.card≤depth)
    (A₁ A₂ : Ideal O) (Z B ell : ℝ) (hZ : 1≤Z) (hell : 0≤ell)
    (hA₀ : ((A₁*A₂).absNorm:ℝ)≤Z^B)
    (hpool : ∀p∈P,(p.absNorm:ℝ)≤Z^ell) :
    (((A₁*(newtonDivisorPair S A).1)*(A₂*(newtonDivisorPair S A).2)).absNorm:ℝ)≤
      Z^(B+depth*ell) := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have he : (A₁*(newtonDivisorPair S A).1)*(A₂*(newtonDivisorPair S A).2)=
      (A₁*A₂)*(∏p∈S,p) := by rw [←newtonDivisorPair_product S A hA];ring
  rw [he,map_mul,Nat.cast_mul]
  have hprod : ((∏p∈S,p).absNorm:ℝ)≤(Z^ell)^S.card := by
    rw [map_prod,Nat.cast_prod]
    simpa only [Finset.prod_const] using
      Finset.prod_le_prod₀ (fun (p : Ideal O) _=>Nat.cast_nonneg (p.absNorm)) (fun p hp=>hpool p (hS hp))
  have hpow := pow_le_pow_right₀ (Real.one_le_rpow hZ hell) hdepth
  apply (mul_le_mul hA₀ (hprod.trans hpow) (Nat.cast_nonneg _) (Real.rpow_nonneg hZp.le _)).trans_eq
  rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le,←Real.rpow_add hZp]
  congr 1
  ring

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.newton_frozen_norm_bound
