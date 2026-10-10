import WeightedQRH.Parameters
import OAI.NumberTheory.DirichletL.Hecke.PrimeRow

/-! Crude selected physical prime products for discarded reflection tails. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedQRH.Numerator

/-- Any selected subproduct is bounded using the actual amplitude-bin upper
bounds. No row-count constant appears in this estimate. -/
theorem selected_product_crude {ι : Type*} [Fintype ι]
    (T : Finset ι) (U mesh:ℝ) (width g:ι→ℝ) (Q:ι→ℂ)
    (hU:1 ≤ U) (hmesh:0 ≤ mesh) (hmeshmax:mesh ≤ 1/100)
    (hw:∀i,0 ≤ width i) (hwsum:(∑i,width i) ≤ 167/500)
    (hg:∀i∈T,g i ≤ 1/2)
    (hQ:∀i∈T,‖Q i‖ ≤ U^(width i*(g i+mesh))) :
    ‖∏i∈T,Q i‖ ≤ U := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hselected : (∑i∈T,width i) ≤ 167/500 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun i _ _=>hw i)).trans hwsum
  have hexp : (∑i∈T,width i*(g i+mesh)) ≤ 1 := by
    calc
      _ ≤ ∑i∈T,width i*(51/100:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (by linarith [hg i hi]) (hw i)
      _ = (∑i∈T,width i)*(51/100:ℝ) := by rw [Finset.sum_mul]
      _ ≤ (167/500:ℝ)*(51/100) := mul_le_mul_of_nonneg_right hselected (by norm_num)
      _ ≤ 1 := by norm_num
  calc
    _ = ∏i∈T,‖Q i‖ := norm_prod _ _
    _ ≤ ∏i∈T,U^(width i*(g i+mesh)) :=
      Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) hQ
    _ = U^(∑i∈T,width i*(g i+mesh)) := (Real.rpow_sum_of_pos hUp _ _).symm
    _ ≤ U^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hU hexp
    _ = U := Real.rpow_one U

/-- The new physical slot geometry supplies the total width required above. -/
theorem physical_width_sum_crude {ι : Type*} [Fintype ι]
    (lengths:ι→ℝ) (d:ℝ) (hsum:(∑i,lengths i)=WeightedQRH.ell)
    (hd:(1/2:ℝ) ≤ d) :
    (∑i,lengths i/d) ≤ 167/500 := by
  rw [←Finset.sum_div,hsum]
  have hdp : 0 < d := by linarith
  apply (div_le_iff₀ hdp).mpr
  norm_num [WeightedQRH.ell] at *
  linarith

/-- In particular the actual canonical prime amplitudes have a uniform crude
subproduct bound, with all their natural zero extensions retained. -/
theorem canonical_selected_product_crude {ι : Type*} [Fintype ι]
    (M:Ideal OAI.SevenEighths.HeckeFamily.O)
    (H:Subgroup (OAI.SevenEighths.HeckeFamily.O ⧸ M)ˣ)
    (u:OAI.SevenEighths.HeckeFamily.O) (W:ℝ→ℂ) (T:Finset ι)
    (U mesh:ℝ) (width g:ι→ℝ) (z:ι→ℂ)
    (hU:1 ≤ U) (hmesh:0 ≤ mesh) (hmeshmax:mesh ≤ 1/100)
    (hw:∀i,0 ≤ width i) (hwsum:(∑i,width i) ≤ 167/500)
    (hg:∀i∈T,g i ≤ 1/2)
    (hQ:∀i∈T,‖OAI.SevenEighths.HeckePrimeRow.canonicalPrimeAmplitude M H u W 2
      (U^(width i)) (z i)‖ ≤ U^(width i*(g i+mesh))) :
    ‖∏i∈T,OAI.SevenEighths.HeckePrimeRow.canonicalPrimeAmplitude M H u W 2
      (U^(width i)) (z i)‖ ≤ U :=
  selected_product_crude T U mesh width g _ hU hmesh hmeshmax hw hwsum hg hQ

end WeightedQRH.Numerator
