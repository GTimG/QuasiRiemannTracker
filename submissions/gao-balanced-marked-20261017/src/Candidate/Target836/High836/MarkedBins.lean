import Candidate.Cycle63.Marked.MarkedBins
import Candidate.Target836.High836.SecondHighBins

set_option autoImplicit false
namespace OAI.SevenEighths.TargetHigh836
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators

/-- The amplitude count saves a monotone function of the frequency scale.
The original slot subset is fixed before forming these exponent bins. -/
theorem retained_high_bin_payment (width δ : ℝ) (hw : 0<width)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4)
    (gain : ℝ→ℝ) (hg : Monotone gain) (x : Fin 4→ℝ) :
    retainedHighExponent δ gain (exponentBinUpper width (exponentBin width x)) ≤ 
      retainedHighExponent δ gain x+4*width := by
  have hp:=high_exponent_bin_payment width δ hw hδ x
  have hg':=hg (exponent_bin_enclosure width hw x 2).1
  unfold retainedHighExponent
  linarith

/-- The same four coordinates suffice for the refined joint amplitude count.
Upward frequency rounding only improves the monotone retained saving. -/
theorem retained_high_binned_sum {κ : Type*} (rows : Finset κ) (x : κ→Fin 4→ℝ)
    (energy : κ→ℝ) (width B δ Z C target reserve : ℝ)
    (hw : 0<width) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4)
    (gain : ℝ→ℝ) (hg : Monotone gain)
    (hx : ∀k∈rows,∀i,-B ≤ x k i ∧ x k i ≤ B)
    (hpoint : ∀k∈rows,retainedHighExponent δ gain (x k) ≤ target-reserve)
    (hbin : ∀key∈rows.image (fun k=>exponentBin width (x k)),
      (∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k) ≤ 
        C*Z^(retainedHighExponent δ gain (exponentBinUpper width key))) :
    (∑k∈rows,energy k) ≤ 
      ((Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width)) := by
  let keys:=rows.image (fun k=>exponentBin width (x k))
  have hsplit : (∑k∈rows,energy k)=
      ∑key∈keys,∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k := by
    exact (Finset.sum_fiberwise_of_maps_to (fun k hk=>Finset.mem_image.mpr ⟨k,hk,rfl⟩) _).symm
  have hcard:=exponent_bins_card rows x width B hw hx
  rw [hsplit]
  calc
    _ ≤ ∑_key∈keys,C*Z^(target-reserve+4*width) := by
      apply Finset.sum_le_sum
      intro key hk
      have hh:=hbin key hk
      obtain ⟨k,hrow,rfl⟩:=Finset.mem_image.mp hk
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hZ
      exact (retained_high_bin_payment width δ hw hδ gain hg (x k)).trans (by linarith [hpoint k hrow])
    _=(keys.card:ℝ)*(C*Z^(target-reserve+4*width)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- Both the near-full sixth-power core gain and the complementary tail gain
are monotone, so their minimum is compatible with upward exponent bins. -/
theorem marked_raw_gain_monotone (supply a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Monotone (fun q=>min (a*min supply (b*q)) (c*q)) := by
  intro q r hqr
  exact min_le_min
    (mul_le_mul_of_nonneg_left (min_le_min_left supply (mul_le_mul_of_nonneg_left hqr hb)) ha)
    (mul_le_mul_of_nonneg_left hqr hc)

end
end OAI.SevenEighths.TargetHigh836
#print axioms OAI.SevenEighths.TargetHigh836.retained_high_binned_sum
#print axioms OAI.SevenEighths.TargetHigh836.marked_raw_gain_monotone
