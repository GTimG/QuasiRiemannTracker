/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact finite scale-fiber collection, preserving every original row weight. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowScaleGrouping
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowScaleGrouping
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Cycle61InitialMass
variable {Row : Type*}

theorem weighted_scale_fibers (rows : Finset Row) (X₁ X₂ Q : Row → ℝ)
    (width Z : ℝ) (value : Row → ℂ) (weight : Row → ℝ) :
    (∑ r ∈ rows, ‖value r‖^2*weight r) =
      ∑ k ∈ rows.image (fun r => key width Z (X₁ r) (X₂ r) (Q r)),
        ∑ r ∈ rows.filter (fun r => key width Z (X₁ r) (X₂ r) (Q r)=k),
          ‖value r‖^2*weight r := by
  exact (Finset.sum_fiberwise_of_maps_to
    (fun r hr => Finset.mem_image.mpr ⟨r,hr,rfl⟩) _).symm

/-- The raw row count is absent: each analytic estimate is used on a whole
scale fiber, and only the fixed exponent-box cardinality is paid. -/
theorem weighted_scale_collection (rows : Finset Row) (X₁ X₂ Q : Row → ℝ)
    (width Z bound Mmax Qmax error C : ℝ) (value : Row → ℂ) (weight : Row → ℝ)
    (hwidth : 0 < width) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hbox : ∀ r ∈ rows, ∀ i, -bound ≤ coordinates Z (X₁ r) (X₂ r) (Q r) i ∧
      coordinates Z (X₁ r) (X₂ r) (Q r) i ≤ bound)
    (hQ : ∀ r ∈ rows, Q r ≤ Qmax)
    (hbin : ∀ k ∈ rows.image (fun r => key width Z (X₁ r) (X₂ r) (Q r)),
      (∑ r ∈ rows.filter (fun r => key width Z (X₁ r) (X₂ r) (Q r)=k),
        ‖value r‖^2*weight r) ≤ C*Z^(radial width Mmax k+error)) :
    (∑ r ∈ rows, ‖value r‖^2*weight r) ≤
      ((Finset.Icc (⌊-bound/width⌋:ℤ) ⌊bound/width⌋).card^3:ℕ)*
        (C*Z^(Qmax+width+error)) := by
  let keys := rows.image (fun r => key width Z (X₁ r) (X₂ r) (Q r))
  have hc := scale_keys_card rows X₁ X₂ Q Z width bound hwidth hbox
  rw [weighted_scale_fibers rows X₁ X₂ Q width Z value weight]
  calc
    _ ≤ ∑ _k ∈ keys, C*Z^(Qmax+width+error) := by
      apply Finset.sum_le_sum
      intro k hk
      have hb := hbin k hk
      obtain ⟨r,hr,hkey⟩ := Finset.mem_image.mp hk
      have hrange := (same_key_enclosure width Z (X₁ r) (X₂ r) (Q r) hwidth k hkey).2.2.2.2.2
      have hrad : radial width Mmax k+error ≤ Qmax+width+error := by
        have hm : radial width Mmax k ≤ Q r+width := (min_le_right _ _).trans hrange
        linarith only [hm,hQ r hr]
      exact hb.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hrad) hC)
    _ = (keys.card:ℝ)*(C*Z^(Qmax+width+error)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
      (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hZ) _))

/-- Every fiber is an actual restriction of the original nonnegative weights,
so zero rows and zero weights are retained by the exact partition. -/
theorem weighted_scale_fiber_nonneg (rows : Finset Row) (X₁ X₂ Q : Row → ℝ)
    (width Z : ℝ) (value : Row → ℂ) (weight : Row → ℝ)
    (hw : ∀ r ∈ rows, 0 ≤ weight r) (k : Fin 3 → ℤ) :
    0 ≤ ∑ r ∈ rows.filter (fun r => key width Z (X₁ r) (X₂ r) (Q r)=k),
      ‖value r‖^2*weight r :=
  Finset.sum_nonneg (fun r hr => mul_nonneg (sq_nonneg _) (hw r (Finset.mem_filter.mp hr).1))

end
end QRH.Record1252270103Source.RegularLowScaleGrouping
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.weighted_scale_fibers
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.weighted_scale_collection
#print axioms QRH.Record1252270103Source.RegularLowScaleGrouping.weighted_scale_fiber_nonneg
