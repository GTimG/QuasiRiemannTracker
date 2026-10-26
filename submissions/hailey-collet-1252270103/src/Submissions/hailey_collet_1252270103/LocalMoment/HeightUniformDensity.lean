import Submissions.hailey_collet_1252270103.LocalMoment.UniformDensity

/-! Uniformity in the independent height is retained through the bounded
window completion and the sixth-power convolution. These theorems require
an eventual estimate with its threshold chosen before the parameter.
They do not manufacture such uniformity from pointwise eventual estimates. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge

theorem uniform_free_density_weighted_of_eventually {α : Type*}
    (P : α → FreeRow → Prop) (C : ℝ) (ρ weight : α → ℝ)
    (hρ : ∀ p, 0 ≤ ρ p) (hw : ∀ p, 1 ≤ weight p)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) →
        (F.card : ℝ) ≤ C * weight p * Y ^ ρ p) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) →
        (F.card : ℝ) ≤ C' * weight p * Y ^ ρ p := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hevent
  let B : ℝ := max 1 Y₀
  let C' : ℝ := max C (128 * B)
  have hB : 1 ≤ B := le_max_left _ _
  have hC' : 0 < C' := lt_of_lt_of_le (by dsimp [B]; positivity) (le_max_right _ _)
  refine ⟨C', hC', le_max_left _ _, ?_⟩
  intro Y hY p F hF
  have hw0 : 0 ≤ weight p := zero_le_one.trans (hw p)
  by_cases hlarge : Y₀ ≤ Y
  · exact (hY₀ Y hlarge p F hF).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
        (Real.rpow_nonneg (by linarith) _))
  · have hc : (F.card : ℝ) ≤ 128 * B :=
      freeRow_count F B hB (fun u hu => (hF u hu).1.trans
        ((le_of_not_ge hlarge).trans (le_max_right _ _)))
    have hp : 1 ≤ Y ^ ρ p := Real.one_le_rpow hY (hρ p)
    have hcw : C' ≤ C' * weight p := by nlinarith [hw p]
    calc
      (F.card : ℝ) ≤ 128 * B := hc
      _ ≤ C' := le_max_right _ _
      _ ≤ C' * weight p := hcw
      _ ≤ C' * weight p * Y ^ ρ p := by
        exact le_mul_of_one_le_right (mul_nonneg hC'.le hw0) hp

/-- A common eventual threshold for all bins/heights remains common after
bounded-window completion and passage from free cores to all integer rows.
For application take `weight p = (1 + |height p|)^J`. -/
theorem raw_density_weighted_from_eventual_free
    {α ι : Type*} [Fintype ι]
    (data : α → ι → RowData) (a b T weight ρ : α → ℝ) (C ρ₀ : ℝ)
    (hρ₀ : 1 / 6 < ρ₀) (hρ : ∀ p, ρ₀ ≤ ρ p)
    (hw : ∀ p, 1 ≤ weight p)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧
        rawZeroBin (data p) (a p) (b p) (T p) ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C * weight p * Y ^ ρ p) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : α, ∀ H : ℝ, 0 < H →
      ∀ R : Finset ProbePhysical.NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧
        rawZeroBin (data p) (a p) (b p) (T p) h) →
        (R.card : ℝ) ≤ K * weight p * H ^ ρ p := by
  let P : α → FreeRow → Prop := fun p u =>
    rawZeroBin (data p) (a p) (b p) (T p) ⟨u.val, u.property.1⟩
  obtain ⟨C', hC', _, hfree⟩ :=
    uniform_free_density_weighted_of_eventually P C ρ weight
      (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨D, hD, hraw⟩ := raw_density_uniform_exponent ρ₀ hρ₀
  refine ⟨C' * D, mul_pos hC' hD, ?_⟩
  intro p H hH R hR
  have hcp : 0 ≤ C' * weight p :=
    mul_nonneg hC'.le (zero_le_one.trans (hw p))
  have hb := hraw (data p) (a p) (b p) (T p) (C' * weight p) (ρ p)
    hcp (hρ p) (fun Y hY F hF => hfree Y hY p F hF) H hH R hR
  convert hb using 1
  ring

#print axioms uniform_free_density_weighted_of_eventually
#print axioms raw_density_weighted_from_eventual_free

end SevenEighths.LocalMoment
end
end OAI
