/- Packaging rehearsal. Original notices retained; separate replay required. -/
import OAI.NumberTheory.DirichletL.Detector.SixthDecomposition
import OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import OAI.NumberTheory.DirichletL.Hecke.MaskDescent
import OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
import OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns

/- BEGIN ORIGINAL LocalMoment.FiniteDeletionBins; sha256 e6d42d5b92afdfb9b7e27948701c630e747cd96889fbe1b7e0745421963272af -/
section
                                                                
                                                       

/-! Exact zero-bin transport through retained finite Euler holes.  This
interface compares zeros, rather than asserting equality of the two
imprimitive L-functions. -/

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDetectorZeros HeckeFiniteDeletion

/-- A retained Euler puncture has no zeros on the positive half-plane.
Both directions include the point `s = 1`, since the actual row is
nonprincipal. -/
theorem positive_zeros_eq_of_mask (χ ψ : Character)
    (hχ : χ.residue ≠ 1)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = 0 ↔ LFunction ψ s = 0 := by
  rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

/-- Inclusion of the positive-real zero sets is enough to compare the
buffered detector maximum; equality of the L-functions is unnecessary. -/
theorem zeroMaximum_le_of_zero_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → Character) (ψ : κ → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ j, (ψ j).residue ≠ 1) (T : ℝ)
    (hinclude : ∀ i, ∃ j, ∀ s : ℂ, 0 < s.re →
      LFunction (χ i) s = 0 → LFunction (ψ j) s = 0) :
    zeroMaximum χ hχ T ≤ zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51 / 100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i, s, hz, ht, hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j, hj⟩ := hinclude i
    rw [← hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · exact hj s (by rw [hs]; linarith) hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

/-- Every retained finite Euler puncture preserves the complete buffered
bin of a finite row-character family, including its baseline and boundary. -/
theorem zeroMaximum_eq_of_mask {ι : Type*} [Fintype ι]
    (χ ψ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (hψ : ∀ i, (ψ i).residue ≠ 1) (T : ℝ)
    (hmask : ∀ i, ∀ I : Ideal O, idealCoeff (χ i) I =
      if IsCoprime I (χ i).modulus then idealCoeff (ψ i) I else 0) :
    zeroMaximum χ hχ T = zeroMaximum ψ hψ T := by
  apply le_antisymm
  · apply zeroMaximum_le_of_zero_inclusion χ ψ hχ hψ T
    intro i
    exact ⟨i, fun s hs hz => (positive_zeros_eq_of_mask (χ i) (ψ i)
      (hχ i) (hmask i) hs).mp hz⟩
  · apply zeroMaximum_le_of_zero_inclusion ψ χ hψ hχ T
    intro i
    exact ⟨i, fun s hs hz => (positive_zeros_eq_of_mask (χ i) (ψ i)
      (hχ i) (hmask i) hs).mpr hz⟩

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.FiniteDeletionBins -/

/- BEGIN ORIGINAL LocalMoment.SixthRowMask; sha256 f5ab31c8dd5929addcee424b7c19bd2e14e1a1455b88b3c45d48409f2fd53fd9 -/
section
                                                              
                                                                   
                                                    
                                     

/-! Exact raw-row sixth decomposition, with all Euler punctures retained. -/

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeRowClosure HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredExceptionalProfile HeckeFiniteDeletion HeckeDetectorZeros
local notation "O" => HeckeFamily.O

lemma rowData_character_zero (data : RowData) (u : NonzeroElement) :
    elementCoeff (data.character u) 0 = 0 := by
  rw [data.character_spec]
  exact rowTwist_zero_of_not_supported (elementHom data.η) data.m data.f u.val 0
    data.lambda_dvd data.two_dvd (by
      intro hs
      exact hs.1 (by simp))

/-- Multiplication of the integer row by an arbitrary ideal generator's
sixth power adds exactly its original coprimality holes. -/
theorem amplified_ideal_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) (I : Ideal O) :
    idealCoeff (data.character (amplifiedElement u B)) I =
      if IsCoprime I B.val then idealCoeff (data.character u) I else 0 := by
  by_cases hs : Supported I
  · rw [idealCoeff_eq_row data.η (data.character (amplifiedElement u B))
      data.m data.f (amplifiedElement u B).val
      (data.character_spec (amplifiedElement u B)) I]
    change idealCoeff data.η I *
      idealRowHom (data.m ^ 6 * data.f ^ 4 *
        (u.val * (idealGenerator B.val) ^ 6)) I = _
    rw [show data.m ^ 6 * data.f ^ 4 * (u.val * (idealGenerator B.val) ^ 6) =
      (data.m ^ 6 * data.f ^ 4 * u.val) * (idealGenerator B.val) ^ 6 by ring,
      idealRowHom_argument_mul, idealRowHom_sixth_mask _ I hs,
      span_idealGenerator]
    by_cases hc : IsCoprime I B.val
    · rw [ite_eq_left hc, mul_one, ite_eq_left hc]
      exact (idealCoeff_eq_row data.η (data.character u) data.m data.f u.val
        (data.character_spec u) I).symm
    · simp only [hc, ite_false, mul_zero]
  · rw [row_coeff_zero_unsupported data.η (data.character (amplifiedElement u B))
      data.m data.f (amplifiedElement u B).val
      (data.character_spec (amplifiedElement u B)) data.lambda_dvd data.two_dvd I hs,
      row_coeff_zero_unsupported data.η (data.character u) data.m data.f u.val
        (data.character_spec u) data.lambda_dvd data.two_dvd I hs]
    split_ifs <;> rfl

theorem amplified_element_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) (n : O) :
    elementCoeff (data.character (amplifiedElement u B)) n =
      if IsCoprime n (idealGenerator B.val) then elementCoeff (data.character u) n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [rowData_character_zero]
    split_ifs <;> rfl
  · have h := amplified_ideal_mask data u B (Ideal.span {n})
    rw [idealCoeff_span _ hn, idealCoeff_span _ hn,
      ← span_idealGenerator B.val, Ideal.isCoprime_span_singleton_iff] at h
    exact h

theorem inducedBy_self (χ : Character) : InducedBy χ χ := by
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc]
  · have hz : idealCoeff χ I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn).2
    rw [ite_eq_right hc, hz]

/-- The exact modulus-mask relation expected by finite Euler deletion. -/
theorem amplified_modulus_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) :
    InducedBy (data.character (amplifiedElement u B)) (data.character u) :=
  HeckeMaskDescent.inducedBy_mask (data.character u)
    (data.character (amplifiedElement u B)) (data.character u)
    (idealGenerator B.val) (amplified_element_mask data u B)
    (inducedBy_self (data.character u))

theorem amplified_nonprincipal (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character u).residue ≠ 1) :
    (data.character (amplifiedElement u B)).residue ≠ 1 := by
  intro hp
  exact hu ((principal_iff_of_mask _ _ (amplified_modulus_mask data u B)).mp hp)

theorem amplified_positive_zeros (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character u).residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction (data.character (amplifiedElement u B)) s = 0 ↔
      LFunction (data.character u) s = 0 :=
  positive_zeros_eq_of_mask _ _ (amplified_nonprincipal data u B hu)
    (amplified_modulus_mask data u B) hs

theorem amplified_zeroMaximum {ι : Type*} [Fintype ι]
    (data : ι → RowData) (u : ι → NonzeroElement)
    (B : ι → HeckeInverseAmplification.NonzeroIdeal)
    (hu : ∀ i, ((data i).character (u i)).residue ≠ 1) (T : ℝ) :
    zeroMaximum (fun i => (data i).character (amplifiedElement (u i) (B i)))
      (fun i => amplified_nonprincipal (data i) (u i) (B i) (hu i)) T =
        zeroMaximum (fun i => (data i).character (u i)) hu T :=
  zeroMaximum_eq_of_mask _ _ _ hu T
    (fun i => amplified_modulus_mask (data i) (u i) (B i))

/-- Bind the general hole identity to the source's actual bijective
decomposition of every nonzero raw integer frequency. -/
theorem sixthFrequency_character_mask (data : RowData)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal) (I : Ideal O) :
    idealCoeff (data.character (ProbePhysical.sixthFrequencyEquiv p)) I =
      if IsCoprime I p.2.val then
        idealCoeff (data.character ⟨p.1.val, p.1.property.1⟩) I else 0 := by
  exact amplified_ideal_mask data ⟨p.1.val, p.1.property.1⟩ p.2 I

theorem sixthFrequency_positive_zeros (data : RowData)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character ⟨p.1.val, p.1.property.1⟩).residue ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction (data.character (ProbePhysical.sixthFrequencyEquiv p)) s = 0 ↔
      LFunction (data.character ⟨p.1.val, p.1.property.1⟩) s = 0 :=
  amplified_positive_zeros data ⟨p.1.val, p.1.property.1⟩ p.2 hu hs

theorem sixthFrequency_zeroMaximum {ι : Type*} [Fintype ι]
    (data : ι → RowData)
    (p : ι → FreeRow × HeckeInverseAmplification.NonzeroIdeal)
    (hu : ∀ i, ((data i).character ⟨(p i).1.val, (p i).1.property.1⟩).residue ≠ 1)
    (T : ℝ) :
    zeroMaximum (fun i => (data i).character (ProbePhysical.sixthFrequencyEquiv (p i)))
      (fun i => amplified_nonprincipal (data i)
        ⟨(p i).1.val, (p i).1.property.1⟩ (p i).2 (hu i)) T =
      zeroMaximum (fun i => (data i).character ⟨(p i).1.val, (p i).1.property.1⟩) hu T :=
  amplified_zeroMaximum data (fun i => ⟨(p i).1.val, (p i).1.property.1⟩)
    (fun i => (p i).2) hu T

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.SixthRowMask -/

/- BEGIN ORIGINAL LocalMoment.RawSixthDensity; sha256 27488b3e82912202f47099c7bfd2481132a454f3575e99f14f61ae49ef971e22 -/
section
                               
                                                         
                                                               

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

end
/- END ORIGINAL LocalMoment.RawSixthDensity -/

/- BEGIN ORIGINAL LocalMoment.UniformDensity; sha256 5c5d6f1a0826b8015cbfeaaed96b9240a80afee5441e18e314cdf49b0a9ee7b7 -/
section
                                  

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

end
/- END ORIGINAL LocalMoment.UniformDensity -/
