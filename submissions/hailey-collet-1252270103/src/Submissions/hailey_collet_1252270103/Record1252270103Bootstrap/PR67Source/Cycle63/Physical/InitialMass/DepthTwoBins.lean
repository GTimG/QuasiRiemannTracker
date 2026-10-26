import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighBins
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Exponent bins in any number of coordinates: a coordinate lies between the edges of its bin, a sum over a set with
coordinates in a fixed box is at most the number of bins times a bound over one bin, and a weighted count over one bin
is at most the largest weight times the count. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators

/-- The lower edge of an exponent bin. -/
def exponentBinLower {n : ℕ} (width : ℝ) (key : Fin n → ℤ) : Fin n → ℝ := fun i => (key i : ℝ)*width

/-- A coordinate lies between the lower and the upper edge of its bin, and the upper edge is one width above the
lower one. -/
theorem exponent_bin_edges {n : ℕ} (width : ℝ) (hw : 0 < width) (x : Fin n → ℝ) (i : Fin n) :
    exponentBinLower width (exponentBin width x) i ≤ x i ∧ x i ≤ exponentBinUpper width (exponentBin width x) i ∧
      exponentBinUpper width (exponentBin width x) i = exponentBinLower width (exponentBin width x) i + width := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x i/width)) hw.le
  rw [div_mul_cancel₀ _ hw.ne'] at hlo
  refine ⟨hlo, (exponent_bin_enclosure width hw x i).1, ?_⟩
  simp only [exponentBinUpper, exponentBinLower]
  ring

/-- A sum over a finite set whose exponent coordinates lie in the box `[-Bbox, Bbox]^n` is at most the number of bins
of the box times a bound on the sum over each bin. The number of bins depends only on the box, the width and `n`. -/
theorem binned_sum_le {X : Type*} {n : ℕ} (S : Finset X) (coord : X → Fin n → ℝ) (f : X → ℝ)
    (width Bbox E : ℝ) (hw : 0 < width) (hE : 0 ≤ E)
    (hbox : ∀ x ∈ S, ∀ i, -Bbox ≤ coord x i ∧ coord x i ≤ Bbox)
    (hbin : ∀ key ∈ S.image (fun x => exponentBin width (coord x)),
      ∑ x ∈ S.filter (fun x => exponentBin width (coord x) = key), f x ≤ E) :
    ∑ x ∈ S, f x ≤ ((Finset.Icc (⌊-Bbox/width⌋ : ℤ) ⌊Bbox/width⌋).card^n : ℕ)*E := by
  let keys := S.image (fun x => exponentBin width (coord x))
  have hsplit : ∑ x ∈ S, f x = ∑ key ∈ keys, ∑ x ∈ S.filter (fun x => exponentBin width (coord x) = key), f x :=
    (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) _).symm
  have hcard := exponent_bins_card S coord width Bbox hw hbox
  rw [hsplit]
  calc ∑ key ∈ keys, ∑ x ∈ S.filter (fun x => exponentBin width (coord x) = key), f x
      ≤ ∑ _key ∈ keys, E := Finset.sum_le_sum hbin
    _ = (keys.card : ℝ)*E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- A weighted count over a finite set, with nonnegative counts and weights at most `Wmax`, is at most `Wmax` times the
total count. -/
theorem weighted_count_le {X : Type*} (T : Finset X) (w N : X → ℝ) (Wmax : ℝ) (hN : ∀ x ∈ T, 0 ≤ N x)
    (hw : ∀ x ∈ T, w x ≤ Wmax) : ∑ x ∈ T, w x*N x ≤ Wmax*∑ x ∈ T, N x := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hw x hx) (hN x hx))

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
