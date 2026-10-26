import Submissions.lewko_acyclic_bootstrap_874772906.Collet.LocalMoment.SixthRowMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros HeckeFiniteDeletion
open ProbePhysical ProbeHighRowFamily ConcretePrimeRowBridge CubicEisenstein
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- A complete finite character-family bin, including both boundaries. -/
def rawZeroBin {ι : Type*} [Fintype ι] (data : ι → RowData)
    (a b T : ℝ) (u : NonzeroElement) : Prop :=
  ∃ hn : ∀ i, ((data i).character u).residue ≠ 1,
    a ≤ zeroMaximum (fun i => (data i).character u) hn T ∧
      zeroMaximum (fun i => (data i).character u) hn T ≤ b

theorem rawZeroBin_amplified_iff {ι : Type*} [Fintype ι]
    (data : ι → RowData) (a b T : ℝ) (u : NonzeroElement) (B : NZIdeal) :
    rawZeroBin data a b T (amplifiedElement u B) ↔ rawZeroBin data a b T u := by
  constructor
  · rintro ⟨hn, hlo, hhi⟩
    have hu : ∀ i, ((data i).character u).residue ≠ 1 := by
      intro i hp
      exact hn i ((principal_iff_of_mask _ _ (amplified_modulus_mask (data i) u B)).mpr hp)
    have he := amplified_zeroMaximum data (fun _ => u) (fun _ => B) hu T
    exact ⟨hu, he ▸ hlo, he ▸ hhi⟩
  · rintro ⟨hu, hlo, hhi⟩
    have he := amplified_zeroMaximum data (fun _ => u) (fun _ => B) hu T
    exact ⟨fun i => amplified_nonprincipal (data i) u B (hu i), he.symm ▸ hlo, he.symm ▸ hhi⟩

def rawFrequencyNorm (h : NonzeroFrequency) : ℝ := (Ideal.span {h.val}).absNorm

def sixthPairs (R : Finset NonzeroFrequency) : Finset (FreeRow × NZIdeal) :=
  R.image sixthFrequencyEquiv.symm

def sixthFreeFiber (R : Finset NonzeroFrequency) (B : NZIdeal) : Finset FreeRow :=
  ((sixthPairs R).filter (fun p => p.2 = B)).image Prod.fst

lemma mem_sixthPairs (R : Finset NonzeroFrequency) (p : FreeRow × NZIdeal) :
    p ∈ sixthPairs R ↔ sixthFrequencyEquiv p ∈ R := by
  simp only [sixthPairs, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa using hh
  · intro hp
    exact ⟨sixthFrequencyEquiv p, hp, sixthFrequencyEquiv.symm_apply_apply p⟩

lemma sixthPairs_card (R : Finset NonzeroFrequency) : (sixthPairs R).card = R.card :=
  Finset.card_image_of_injective R sixthFrequencyEquiv.symm.injective

lemma sixthFreeFiber_card (R : Finset NonzeroFrequency) (B : NZIdeal) :
    (sixthFreeFiber R B).card = ((sixthPairs R).filter (fun p => p.2 = B)).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  apply Prod.ext he
  exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm

theorem raw_sixth_cardinality (R : Finset NonzeroFrequency) :
    R.card = ∑ B ∈ (sixthPairs R).image Prod.snd, (sixthFreeFiber R B).card := by
  rw [← sixthPairs_card R, Finset.card_eq_sum_card_image Prod.snd]
  apply Finset.sum_congr rfl
  intro B hB
  exact (sixthFreeFiber_card R B).symm

lemma raw_sixth_norm (p : FreeRow × NZIdeal) :
    rawFrequencyNorm (sixthFrequencyEquiv p) = rowNorm p.1 * (p.2.val.absNorm : ℝ) ^ 6 := by
  change ((Ideal.span {rowMap p}).absNorm : ℝ) =
    ((Ideal.span {p.1.val}).absNorm : ℝ) * (p.2.val.absNorm : ℝ) ^ 6
  exact_mod_cast rowMap_norm p

theorem sixthFreeFiber_bound_and_bin {ι : Type*} [Fintype ι]
    (data : ι → RowData) (a b T H : ℝ) (_hH : 0 < H)
    (R : Finset NonzeroFrequency)
    (hR : ∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h)
    (B : NZIdeal) (u : FreeRow) (hu : u ∈ sixthFreeFiber R B) :
    rowNorm u ≤ H / (B.val.absNorm : ℝ) ^ 6 ∧
      rawZeroBin data a b T ⟨u.val, u.property.1⟩ := by
  obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hp
  have he : p = (u, B) := Prod.ext hpu hpB
  subst p
  have hr := hR _ ((mem_sixthPairs R (u, B)).mp hp)
  have hB : 0 < (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  rw [raw_sixth_norm] at hr
  exact ⟨(le_div_iff₀ (pow_pos hB 6)).mpr hr.1,
    (rawZeroBin_amplified_iff data a b T ⟨u.val, u.property.1⟩ B).mp hr.2⟩

/-- Exact finite raw-row convolution. A subunit fibre contributes zero;
the upstream free density is used only on integral windows at least one. -/
theorem raw_sixth_convolution {ι : Type*} [Fintype ι]
    (data : ι → RowData) (a b T H C ρ : ℝ) (hH : 0 < H) (hC : 0 ≤ C)
    (R : Finset NonzeroFrequency)
    (hR : ∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h)
    (hfree : ∀ Y : ℝ, 1 ≤ Y → ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin data a b T ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C * Y ^ ρ) :
    (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd,
      C * (H / (B.val.absNorm : ℝ) ^ 6) ^ ρ := by
  rw [raw_sixth_cardinality R, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro B hB
  let Y := H / (B.val.absNorm : ℝ) ^ 6
  have hb := sixthFreeFiber_bound_and_bin data a b T H hH R hR B
  by_cases hY : 1 ≤ Y
  · exact hfree Y hY (sixthFreeFiber R B) hb
  · have he : sixthFreeFiber R B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hY ((rowNorm_ge_one u).trans (hb u hu).1)
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)

lemma ideal_sixth_power_summable (ρ : ℝ) (hρ : 1 / 6 < ρ) :
    Summable (fun B : NZIdeal => (B.val.absNorm : ℝ) ^ (-6 * ρ)) := by
  have hs := (fullIdealWeight_summable_norm ((6 * ρ : ℝ) : ℂ)
    (by simp only [Complex.ofReal_re]; linarith)).subtype (fun I => I ≠ 0)
  apply hs.congr
  intro B
  have hb : 0 < (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  change ‖fullIdealWeight ((6 * ρ : ℝ) : ℂ) B.val‖ = _
  rw [fullIdealWeight, ite_eq_right B.property]
  change ‖((B.val.absNorm : ℝ) : ℂ) ^ (-((6 * ρ : ℝ) : ℂ))‖ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
  congr 1
  simp only [Complex.neg_re, Complex.ofReal_re]
  ring

lemma sixth_window_power (H N ρ : ℝ) (hH : 0 < H) (hN : 0 < N) :
    (H / N ^ 6) ^ ρ = H ^ ρ * N ^ (-6 * ρ) := by
  rw [Real.div_rpow hH.le (pow_nonneg hN.le 6), ← Real.rpow_natCast_mul hN.le]
  rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]
  congr 2
  ring

/-- LP.8's raw integer rows inherit every free-row density exponent
greater than one sixth, with the complete actual zero bin unchanged. -/
theorem raw_density_from_free {ι : Type*} [Fintype ι]
    (data : ι → RowData) (a b T C ρ : ℝ) (hC : 0 ≤ C) (hρ : 1 / 6 < ρ)
    (hfree : ∀ Y : ℝ, 1 ≤ Y → ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ rawZeroBin data a b T ⟨u.val, u.property.1⟩) →
        (F.card : ℝ) ≤ C * Y ^ ρ) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 0 < H → ∀ R : Finset NonzeroFrequency,
      (∀ h ∈ R, rawFrequencyNorm h ≤ H ∧ rawZeroBin data a b T h) →
        (R.card : ℝ) ≤ C * D * H ^ ρ := by
  let w := fun B : NZIdeal => (B.val.absNorm : ℝ) ^ (-6 * ρ)
  have hw := ideal_sixth_power_summable ρ hρ
  have hw0 : ∀ B, 0 ≤ w B := fun B => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D := (∑' B : NZIdeal, w B) + 1
  have hsum : 0 ≤ ∑' B : NZIdeal, w B := tsum_nonneg hw0
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro H hH R hR
  have hc := raw_sixth_convolution data a b T H C ρ hH hC R hR hfree
  have hn (B : NZIdeal) : 0 < (B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  simp_rw [sixth_window_power H _ ρ hH (hn _)] at hc
  calc
    (R.card : ℝ) ≤ ∑ B ∈ (sixthPairs R).image Prod.snd, C * (H ^ ρ * w B) := hc
    _ = (C * H ^ ρ) * ∑ B ∈ (sixthPairs R).image Prod.snd, w B := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      ring
    _ ≤ (C * H ^ ρ) * ∑' B : NZIdeal, w B :=
      mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun B _ => hw0 B)) (by positivity)
    _ ≤ C * D * H ^ ρ := by
      have ht : (∑' B : NZIdeal, w B) ≤ D := by dsimp [D]; linarith
      calc
        _ ≤ (C * H ^ ρ) * D := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by ring

end SevenEighths.LocalMoment
end
end OAI
