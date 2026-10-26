import Candidate.Cycle63.Physical.InitialMass.SecondHighBins
import Candidate.Target836.SourceProvider.NamedSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.TargetHigh836
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators

/-- Rounding the scalar, missing radical, frequency and raw-volume
coordinates upward costs at most four bin widths throughout the high range. -/
theorem high_exponent_bin_payment (width δ : ℝ) (hw : 0<width)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4) (x : Fin 4→ℝ) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x)) ≤ 
      highExponentValue δ x+4*width := by
  have hρ := Named.rho_bounds_full hδ
  have hρ0 : 0 ≤ LocalMoment.unmarkedDensity δ := by change 0 ≤ Named.rho δ; linarith [hρ.1]
  have hρ1 : LocalMoment.unmarkedDensity δ ≤ 1 := by change Named.rho δ ≤ 1; linarith [hρ.2]
  have hd0 : 0 ≤ δ := by have hh:=hδ.1; norm_num [Named.q] at hh; linarith
  have h0 := (exponent_bin_enclosure width hw x 0).2
  have h1 := (exponent_bin_enclosure width hw x 1).2
  have h2 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 2).2 hρ0
  have h3 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 3).2 hd0
  have hρw := mul_le_mul_of_nonneg_right hρ1 hw.le
  have hdw := mul_le_mul_of_nonneg_right hδ.2 hw.le
  unfold highExponentValue
  nlinarith

theorem high_bin_reserve_transfer (width δ target reserve : ℝ) (hw : 0<width)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4) (x : Fin 4→ℝ)
    (hbound : highExponentValue δ x ≤ target-reserve) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x)) ≤ 
      target-reserve+4*width := (high_exponent_bin_payment width δ hw hδ x).trans (by linarith)

/-- Sum estimates proved on fixed exponent bins, charging only the fixed
number of bins. No additional count of the source rows appears. -/
theorem high_binned_sum {κ : Type*} (rows : Finset κ) (x : κ→Fin 4→ℝ)
    (energy : κ→ℝ) (width B δ Z C target reserve : ℝ)
    (hw : 0<width) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4)
    (hx : ∀k∈rows,∀i,-B ≤ x k i ∧ x k i ≤ B)
    (hpoint : ∀k∈rows,highExponentValue δ (x k) ≤ target-reserve)
    (hbin : ∀key∈rows.image (fun k=>exponentBin width (x k)),
      (∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k) ≤ 
        C*Z^(highExponentValue δ (exponentBinUpper width key))) :
    (∑k∈rows,energy k) ≤ 
      ((Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width)) := by
  let keys := rows.image (fun k=>exponentBin width (x k))
  have hsplit : (∑k∈rows,energy k)=
      ∑key∈keys,∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k := by
    exact (Finset.sum_fiberwise_of_maps_to (fun k hk=>Finset.mem_image.mpr ⟨k,hk,rfl⟩) _).symm
  have hcard := exponent_bins_card rows x width B hw hx
  rw [hsplit]
  calc
    _ ≤ ∑_key∈keys,C*Z^(target-reserve+4*width) := by
      apply Finset.sum_le_sum
      intro key hk
      have hh := hbin key hk
      obtain ⟨k,hrow,rfl⟩ := Finset.mem_image.mp hk
      exact hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ
          (high_bin_reserve_transfer width δ target reserve hw hδ (x k) (hpoint k hrow))) hC)
    _=(keys.card:ℝ)*(C*Z^(target-reserve+4*width)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end
end OAI.SevenEighths.TargetHigh836
#print axioms OAI.SevenEighths.TargetHigh836.high_exponent_bin_payment
#print axioms OAI.SevenEighths.TargetHigh836.high_bin_reserve_transfer
#print axioms OAI.SevenEighths.TargetHigh836.high_binned_sum
