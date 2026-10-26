import Candidate.LocalMoment.SixthRowMask
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
  refine Finset.sum_congr rfl fun B hB => ?_
  exact (sixthFreeFiber_card R B).symm

lemma raw_sixth_norm (p : FreeRow × NZIdeal) :
    rawFrequencyNorm (sixthFrequencyEquiv p) = rowNorm p.1 * (p.2.val.absNorm : ℝ) ^ 6 := by
  change ((Ideal.span {rowMap p}).absNorm : ℝ) =
    ((Ideal.span {p.1.val}).absNorm : ℝ) * (p.2.val.absNorm : ℝ) ^ 6
  exact_mod_cast rowMap_norm p

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

end SevenEighths.LocalMoment
end
end OAI
