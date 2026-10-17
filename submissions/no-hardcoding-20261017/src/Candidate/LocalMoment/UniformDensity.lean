import Candidate.LocalMoment.RawSixthDensity

/-! Extend an eventual free-row estimate to every window at least one.
The bounded-window constant is uniform in the row predicate, so it does
not introduce dependence on a selected label, zero bin, or frequency.
The substantive eventual density hypothesis is retained explicitly. -/

namespace OAI
noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge

theorem uniform_free_density_varying_of_eventually {α : Type*}
    (P : α → FreeRow → Prop) (C : ℝ) (ρ : α → ℝ) (hρ : ∀ p, 0 ≤ ρ p)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C * Y ^ ρ p) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C' * Y ^ ρ p := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hevent
  let B : ℝ := max 1 Y₀
  let C' : ℝ := max C (128 * B)
  have hB : 1 ≤ B := le_max_left _ _
  have hC' : 0 < C' := lt_of_lt_of_le (by dsimp [B]; positivity) (le_max_right _ _)
  refine ⟨C', hC', le_max_left _ _, ?_⟩
  intro Y hY p F hF
  by_cases hlarge : Y₀ ≤ Y
  · exact (hY₀ Y hlarge p F hF).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
  · have hc : (F.card : ℝ) ≤ 128 * B :=
      freeRow_count F B hB (fun u hu => (hF u hu).1.trans
        ((le_of_not_ge hlarge).trans (le_max_right _ _)))
    have hp : 1 ≤ Y ^ ρ p := Real.one_le_rpow hY (hρ p)
    calc
      (F.card : ℝ) ≤ 128 * B := hc
      _ ≤ C' := le_max_right _ _
      _ ≤ C' * Y ^ ρ p := by nlinarith

theorem uniform_free_density_of_eventually {α : Type*}
    (P : α → FreeRow → Prop) (C ρ : ℝ) (hρ : 0 ≤ ρ)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C * Y ^ ρ) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∀ p : α, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C' * Y ^ ρ :=
  uniform_free_density_varying_of_eventually P C (fun _ => ρ) (fun _ => hρ) hevent

/-- A single convolution constant works for every exponent above a fixed
summability threshold, for every finite fixed character list and every bin. -/
theorem raw_density_uniform_exponent (ρ₀ : ℝ) (hρ₀ : 1 / 6 < ρ₀) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type*} [Fintype ι] (data : ι → RowData)
      (a b T C ρ : ℝ), 0 ≤ C → ρ₀ ≤ ρ →
      (∀ Y : ℝ, 1 ≤ Y → ∀ F : Finset FreeRow,
        (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin data a b T ⟨u.val, u.property.1⟩) →
          (F.card : ℝ) ≤ C * Y ^ ρ) →
      ∀ H : ℝ, 0 < H → ∀ R : Finset ProbePhysical.NonzeroFrequency,
        (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h) →
          (R.card : ℝ) ≤ C * D * H ^ ρ := by
  let w := fun B : HeckeInverseAmplification.NonzeroIdeal =>
    (B.val.absNorm : ℝ) ^ (-6 * ρ₀)
  have hw := ideal_sixth_power_summable ρ₀ hρ₀
  have hw0 : ∀ B, 0 ≤ w B := fun B => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D := (∑' B : HeckeInverseAmplification.NonzeroIdeal, w B) + 1
  have hsum : 0 ≤ ∑' B : HeckeInverseAmplification.NonzeroIdeal, w B := tsum_nonneg hw0
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro ι _ data a b T C ρ hC hρ hfree H hH R hR
  have hc := raw_sixth_convolution data a b T H C ρ hH hC R hR hfree
  have hn (B : HeckeInverseAmplification.NonzeroIdeal) : 1 ≤ (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  simp_rw [sixth_window_power H _ ρ hH (lt_of_lt_of_le zero_lt_one (hn _))] at hc
  calc
    (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
        C * (H ^ ρ * (B.val.absNorm : ℝ) ^ (-6 * ρ)) := hc
    _ ≤ ∑ B ∈ (sixthPairs R).image Prod.snd, C * (H ^ ρ * w B) := by
      apply Finset.sum_le_sum
      intro B _
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hH.le _)
      exact Real.rpow_le_rpow_of_exponent_le (hn B) (by linarith)
    _ = (C * H ^ ρ) * ∑ B ∈ (sixthPairs R).image Prod.snd, w B := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ ≤ (C * H ^ ρ) * ∑' B : HeckeInverseAmplification.NonzeroIdeal, w B :=
      mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun B _ => hw0 B)) (by positivity)
    _ ≤ C * D * H ^ ρ := by
      have ht : (∑' B : HeckeInverseAmplification.NonzeroIdeal, w B) ≤ D := by
        dsimp [D]; linarith
      calc
        _ ≤ (C * H ^ ρ) * D := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by ring

/-- The all-integer-row conclusion needs only an eventual free-row density
estimate. No density assumption is required in the bounded residual windows
of the sixth-power convolution. -/
theorem raw_density_from_eventual_free {ι : Type*} [Fintype ι]
    (data : ι → RowData) (a b T C ρ : ℝ) (hρ : 1 / 6 < ρ)
    (hevent : ∀ᶠ Y : ℝ in atTop, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin data a b T ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C * Y ^ ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 0 < H → ∀ R : Finset ProbePhysical.NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h) →
        (R.card : ℝ) ≤ K * H ^ ρ := by
  let P : Unit → FreeRow → Prop :=
    fun _ u => rawZeroBin data a b T ⟨u.val, u.property.1⟩
  have hevent' : ∀ᶠ Y : ℝ in atTop, ∀ p : Unit, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C * Y ^ ρ := by
    filter_upwards [hevent] with Y hY
    exact fun _ => hY
  obtain ⟨C', hC', _, hfree⟩ := uniform_free_density_of_eventually P C ρ
    (by linarith) hevent'
  obtain ⟨D, hD, hraw⟩ := raw_density_from_free data a b T C' ρ hC'.le hρ
    (fun Y hY => hfree Y hY ())
  exact ⟨C' * D, mul_pos hC' hD, hraw⟩

end SevenEighths.LocalMoment
end
end OAI
