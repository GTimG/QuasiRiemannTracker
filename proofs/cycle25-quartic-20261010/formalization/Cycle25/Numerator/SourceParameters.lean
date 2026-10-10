import Cycle25.Numerator.ActualBin
import Cycle25.Numerator.SourceSelection
import Cycle25.Numerator.PhysicalFront

/-! Eligibility of the actual physical source for the coefficient packet bound. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted OAI.SevenEighths.Cycle25DetectorRowCount
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification

theorem source_packet_lines {Δ : ℝ} (D : HighParameters.HighData Δ) (a : ℝ)
    (ha : (51/100:ℝ) ≤ a) (hatop : a ≤ 7/8) :
    0 ≤ (2*a-1)/4 ∧ (2*a-1)/4 ≤ 1 ∧
    1-a-6*D.e ≤ 1/2-(2*a-1)/4 ∧
    -(1/100:ℝ) ≤ 1/2-(2*a-1)/4 ∧
    1+4*D.e ≤ (a+16*D.e)+(1/2-(2*a-1)/4) := by
  have he := D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem source_complex_profile_norm {D : MomentData} (F : WeightedSourceData D) (y : ℝ) :
    ‖F.W y‖ ≤ 1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded y).1]
  exact (F.bounded y).2

theorem source_main_normalized_upper {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z d delta : ℝ) (hZ : 1 < Z) (hd : 0 < d)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ) (u : FreeRow) (z : ℂ)
    (hupper : ∀j∈main,‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z‖ ≤
      (Z^(D.ell j))^(g j+D.t)) :
    let q := HeckeDetectorPhysicalSelection.weightedMean Finset.univ (fun j=>D.ell j/d) (maskedGain main g)
    ‖(∏j∈main,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) /
      (((Z^d)^(D.t*(ell/d)):ℝ):ℂ)‖ ≤ (Z^d)^(q*(ell/d)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hd
  have hw (j : Fin D.N) : 0 ≤ D.ell j/d := (div_pos (D.slots_bounds j).1 hd).le
  have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd.ne']
  have hb := masked_main_product_upper main (fun j=>D.ell j/d) g (Z^d) D.t
    (fun j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)
    hU.le D.t_pos.le hw (by rw [hL];exact div_pos ell_pos hd) (by
      intro j hj
      calc
        _ ≤ (Z^(D.ell j))^(g j+D.t) := hupper j hj
        _ = _ := by rw [←hscale j,←Real.rpow_mul (zero_lt_one.trans hU).le])
  rw [hL] at hb
  exact upper_bin_normalized _ (Z^d) _ _ (zero_lt_one.trans hU) hb

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
