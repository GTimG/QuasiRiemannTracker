/- Prepared rational cube transport; compiler and replay receipts are separate. -/
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.TailExtension.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open _root_.BelowSevenEighthsTight _root_.BelowSevenEighthsTight.PrincipalExtension
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale_retuned {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^lxRat)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^lyRat)^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num [lxRat,lyRat,ellRat,bRat];nlinarith)

lemma central_prime_product_bound_retuned {K : ℕ} (P : Fin K→PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=ellRat) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^ellRat := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound_retuned {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(hRat+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=ellRat)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*ellRat) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show hRat+ζ≤1 by norm_num [hRat,ellRat,bRat] at *;linarith))
  have hp := central_prime_product_bound_retuned P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^ellRat)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(ellRat*(3:ℕ))=Z^(6+3*ellRat) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

end SevenEighths.ProbeHighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.ProbeHighRowFamily.central_source_crude_scale_retuned
#print axioms OAI.SevenEighths.ProbeHighRowFamily.central_prime_product_bound_retuned
#print axioms OAI.SevenEighths.ProbeHighRowFamily.central_arithmetic_cost_bound_retuned
