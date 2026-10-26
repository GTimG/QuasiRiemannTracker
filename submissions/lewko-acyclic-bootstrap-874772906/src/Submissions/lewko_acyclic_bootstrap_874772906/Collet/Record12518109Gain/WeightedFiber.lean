import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.ActualFiberCount

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Record12518109GainAssembly
open HeckeFamily HeckeDyadic HeckeDetectorPhysicalSelection HeckeDetectorInverseFiberCount
open Record12518109Gain

theorem weighted_bound_of_card {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (U ν binWidth A loss : ℝ) (hU : 1<U) (hbin : 0<binWidth)
    (hw : ∀s∈slots,0<widths s) (hL : 0≤∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (ν/2) binWidth (Q u s)=g s)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(ν/2+binWidth))
    (hcard : (rows.card : ℝ)≤A*U^(rho ν+ν*(∑s∈slots,widths s)-gain ν (∑s∈slots,widths s) 1-
      2*weightedMean slots widths g*(∑s∈slots,widths s)+loss)) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤ A*
      U^(rho ν+ν*(∑s∈slots,widths s)-gain ν (∑s∈slots,widths s) 1+
        loss+2*binWidth*(∑s∈slots,widths s)) := by
  let S := ∑s∈slots,widths s
  let q := weightedMean slots widths g
  have hmeanS : q*S=∑s∈slots,widths s*g s := by
    by_cases hLp : 0<∑s∈slots,widths s
    · exact div_mul_cancel₀ _ hLp.ne'
    · have hzero : (∑s∈slots,widths s)=0 := by linarith
      have hempty := slots_empty_of_width_sum_zero slots widths hw hzero
      subst slots
      simp [S,q]
  have hprod (u : Row) (hu : u∈rows) : ‖∏s∈slots,Q u s‖^2≤U^(2*q*S+2*binWidth*S) := by
    have hh := HeckePrimeAmplitudeBins.product_upper slots widths (Q u) U (ν/2) binWidth
      hU hbin hw (hQ u hu)
    have hg : (∑s∈slots,widths s*HeckePrimeAmplitudeBins.amplitude
        (U^(widths s)) (ν/2) binWidth (Q u s))=∑s∈slots,widths s*g s :=
      Finset.sum_congr rfl (fun s hs=>by rw [hbins u hu s hs])
    rw [hg,←hmeanS] at hh
    have hh' := (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)).mpr hh
    convert hh' using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ)≤U)]
    congr 1
    ring
  calc
    _ ≤ ∑u∈rows,U^(2*q*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*q*S+2*binWidth*S) := by simp
    _ ≤ (A*U^(rho ν+ν*S-gain ν S 1-2*q*S+loss))*U^(2*q*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith) _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by linarith : 0<U)]; congr 1; congr 1; ring

end OAI.SevenEighths.Record12518109GainAssembly
end
