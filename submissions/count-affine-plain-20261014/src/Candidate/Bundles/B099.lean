/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B096
import Candidate.Bundles.B097
import Candidate.Bundles.B098

/- BEGIN ORIGINAL LocalMoment.HeightUniformDensity; sha256 55de8050440d3e473ac32820cf5e57e7a8bf207bd9a9cf1811bc58f96fb78eee -/
section
                                 

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

end
/- END ORIGINAL LocalMoment.HeightUniformDensity -/

/- BEGIN ORIGINAL Cycle61.Density.NaturalDictionary; sha256 de50aa268c7634c5938603479fe89da281a4abb23810ef9d947f950f5301a41f -/
section
                                    
                                       

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeDetectorZeros HeckeDetectorFamilyInclusion
open CenteredMomentNaturalRowSource
open ConcretePrimeRowBridge CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O

theorem coefficient_equality_mask (χ ψ : Character)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I) :
    ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · simpa only [hc, ite_true] using hcoeff I
  · rw [ite_eq_right hc]
    by_contra hn
    exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn).2

def FixedUnmarkedDictionary.naturalFamily {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) : Label → Character :=
  fun j => (naturalRow (D.base j) u.val u.property.1).character

theorem FixedUnmarkedDictionary.natural_coefficients {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) (j : Label) (I : Ideal O) :
    idealCoeff (D.naturalFamily u j) I =
      idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I :=
  natural_row_moment_dictionary (D.base j) u I

/-- A conductor bound for the actual natural representative, independent of scale. -/
theorem FixedUnmarkedDictionary.natural_conductor_bound {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ u : FreeRow, ∀ j,
      ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤ K * rowNorm u := by
  let K : ℝ := 1 + ∑ j, ((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)
  have hs : 0 ≤ ∑ j, ((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro u j
  have hc : ((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ) ≤ K := by
    have hh := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => (by positivity :
        0 ≤ ((D.base k).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)))
      (Finset.mem_univ j)
    dsimp [K]
    linarith
  have hb : ((D.naturalFamily u j).modulus.absNorm : ℝ) ≤
      (((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)) * rowNorm u := by
    change ((naturalRow (D.base j) u.val u.property.1).character.modulus.absNorm : ℝ) ≤
      (((D.base j).modulus.absNorm : ℝ) * (fixedConductorFactor : ℝ)) *
        ((Ideal.span {u.val}).absNorm : ℝ)
    exact_mod_cast (naturalRow (D.base j) u.val u.property.1).natural_modulus_bound
  exact hb.trans (mul_le_mul_of_nonneg_right hc (rowNorm_ge_one u |>.trans' zero_le_one))

theorem FixedUnmarkedDictionary.natural_nonprincipal {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow)
    (hu : ∀ j, ((D.data j).character ⟨u.val, u.property.1⟩).residue ≠ 1) :
    ∀ j, (D.naturalFamily u j).residue ≠ 1 := by
  intro j hp
  exact hu j ((principal_iff_of_mask _ _
    (coefficient_equality_mask _ _ (D.natural_coefficients u j))).mp hp)

theorem FixedUnmarkedDictionary.natural_maximum {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (u : FreeRow)
    (hu : ∀ j, ((D.data j).character ⟨u.val, u.property.1⟩).residue ≠ 1) (T : ℝ) :
    zeroMaximum (D.naturalFamily u) (D.natural_nonprincipal u hu) T =
      zeroMaximum (fun j => (D.data j).character ⟨u.val, u.property.1⟩) hu T :=
  zeroMaximum_eq_of_mask _ _ _ hu T
    (fun j => coefficient_equality_mask _ _ (D.natural_coefficients u j))

/-- Whole-character conjugation retains the natural modulus and reflects the zero heights. -/
theorem FixedUnmarkedDictionary.oriented_natural {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) (j : Label) (reverse : Bool) :
    let χ := if reverse then (D.naturalFamily u j).inverse else D.naturalFamily u j
    χ.modulus = (D.naturalFamily u j).modulus ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if reverse then starRingEnd ℂ (idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I)
        else idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I := by
  cases reverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨trivial, D.natural_coefficients u j⟩
  · refine ⟨rfl, ?_⟩
    intro I
    rw [idealCoeff_inverse_conj, D.natural_coefficients]

/-- Only free cores form this finite exceptional population. Their raw
sixth-power multiples are handled by convolution, never declared finite. -/
theorem FixedUnmarkedDictionary.exceptional_cores_finite {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) :
    {u : FreeRow | ∃ j, ¬initialKeep
      (D.base j) (D.fixedIdeal j) u.val}.Finite := by
  have h : (⋃ j, {u : FreeRow | ¬initialKeep (D.base j) (D.fixedIdeal j) u.val}).Finite := by
    apply Set.finite_iUnion
    intro j
    exact fixed_exceptional_free_finite (D.base j) (D.fixedIdeal j) (D.nonzero j)
      (D.proper j) (D.divides72 j) (D.dividesBase j)
  simpa only [Set.iUnion_ofPred] using h

def FixedUnmarkedDictionary.exceptionalCore {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) : Prop :=
  ∃ j, ¬initialKeep (D.base j) (D.fixedIdeal j) u.val

theorem FixedUnmarkedDictionary.regular_nonprincipal {Label : Type*}
    (D : FixedUnmarkedDictionary Label) (u : FreeRow) (hu : ¬D.exceptionalCore u) :
    ∀ j, ((D.data j).character ⟨u.val, u.property.1⟩).residue ≠ 1 := by
  intro j hp
  have hkeep : initialKeep (D.base j) (D.fixedIdeal j) u.val := by
    by_contra hn
    exact hu ⟨j, hn⟩
  have hn : (D.naturalFamily u j).residue ≠ 1 :=
    (naturalRow (D.base j) u.val u.property.1).nonprincipal u.property.1
      (D.fixedIdeal j) 1 one_ne_zero hkeep.2
  exact hn ((principal_iff_of_mask _ _
    (coefficient_equality_mask _ _ (D.natural_coefficients u j))).mpr hp)

#print axioms FixedUnmarkedDictionary.natural_conductor_bound
#print axioms FixedUnmarkedDictionary.exceptional_cores_finite
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.NaturalDictionary -/

/- BEGIN ORIGINAL Cycle61.Density.BufferedPartition; sha256 e3794eb926f6d13cbbe8a9a7fb8ab1cb6c74630fa6f703ffc8b8c9a99313fe33 -/
section
                                        

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros

theorem zeroMaximum_le_beta {Label : Type*} [Fintype Label]
    (family : Label → Character) (hn : ∀ j, (family j).residue ≠ 1)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (T : ℝ) :
    zeroMaximum family hn T ≤ HeckeZeroSupremum.beta := by
  by_cases hmax : 51/100 < zeroMaximum family hn T
  · obtain ⟨j, s, hz, ht, hs⟩ := maximum_attained family hn T hmax
    rw [← hs]
    exact HeckeZeroSupremum.zero_re_le_beta (family j) (by rw [hs]; linarith) (Or.inr (hn j)) hz
  · exact (le_of_not_gt hmax).trans hβ

theorem beta_lower_of_nonempty_bin {Label : Type*} [Fintype Label]
    (data : Label → RowData) (a b T : ℝ) (ha : (51/100 : ℝ) < a)
    (rows : Finset FreeRow) (hne : rows.Nonempty)
    (hrows : ∀ u ∈ rows, rawZeroBin data a b T ⟨u.val, u.property.1⟩) :
    (51/100 : ℝ) ≤ HeckeZeroSupremum.beta := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨hn, hlo, hhi⟩ := hrows u hu
  obtain ⟨j, s, hz, ht, hs⟩ := maximum_attained _ hn T (ha.trans_le hlo)
  have hb := HeckeZeroSupremum.zero_re_le_beta (data j |>.character ⟨u.val, u.property.1⟩)
    (by rw [hs]; linarith) (Or.inr (hn j)) hz
  linarith

def bufferCount (e : ℝ) : ℕ := ⌈(49/100 : ℝ) / e⌉₊
def bufferGridCount (e : ℝ) : ℕ := ⌈(1 : ℝ) / e⌉₊
abbrev BufferIndex (e : ℝ) := Fin (bufferCount e + 1) × Fin (bufferGridCount e + 1)
def bufferValue (e : ℝ) (p : BufferIndex e) : ℝ := 51/100 + e*p.2.val

theorem bufferCount_spec (e : ℝ) (he : 0 < e) :
    0 < bufferCount e ∧ (49/100 : ℝ) ≤ (bufferCount e : ℝ)*e := by
  have hceil : (49/100 : ℝ)/e ≤ (bufferCount e : ℝ) := Nat.le_ceil _
  have hwidth : (49/100 : ℝ) ≤ (bufferCount e : ℝ)*e := (div_le_iff₀ he).mp hceil
  refine ⟨?_, hwidth⟩
  by_contra hn
  have hz : bufferCount e = 0 := by omega
  rw [hz, Nat.cast_zero, zero_mul] at hwidth
  norm_num at hwidth

/-- The selected bin and both zero maxima are actual, and the finite grid
is chosen before the live lower boundary and height. -/
theorem actual_buffered_partition {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (e U T a : ℝ)
    (he : 0 < e) (hT : 2 < T)
    (hheight : U ≤ T)
    (hβ : HeckeZeroSupremum.beta ≤ 7/8)
    (rows : Finset FreeRow)
    (ha : 33/40 ≤ a)
    (hrows : ∀ u ∈ rows, rawZeroBin D.data a (7/8) U ⟨u.val, u.property.1⟩) :
    ∃ select : rows → BufferIndex e,
      ∀ u : rows, 1 ≤ (select u).1.val ∧
        let b := bufferValue e (select u)
        ∃ hn : ∀ j, (D.naturalFamily u.val j).residue ≠ 1,
          b ≤ 7/8 ∧ a-e < b ∧
          b ≤ zeroMaximum (D.naturalFamily u.val) hn ((3*(select u).1.val : ℕ)*T) ∧
          zeroMaximum (D.naturalFamily u.val) hn ((3*(select u).1.val : ℕ)*T) < b+e ∧
          zeroMaximum (D.naturalFamily u.val) hn (3*((select u).1.val+1 : ℕ)*T) < b+2*e := by
  have one (u : rows) : ∃ p : BufferIndex e, 1 ≤ p.1.val ∧
      let b := bufferValue e p
      ∃ hn : ∀ j, (D.naturalFamily u.val j).residue ≠ 1,
        b ≤ 7/8 ∧ a-e < b ∧
        b ≤ zeroMaximum (D.naturalFamily u.val) hn ((3*p.1.val : ℕ)*T) ∧
        zeroMaximum (D.naturalFamily u.val) hn ((3*p.1.val : ℕ)*T) < b+e ∧
        zeroMaximum (D.naturalFamily u.val) hn (3*(p.1.val+1 : ℕ)*T) < b+2*e := by
    obtain ⟨hraw, hlo, hhi⟩ := hrows u.val u.property
    let hn := D.natural_nonprincipal u.val hraw
    have hbn : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta :=
      beta_lower_of_nonempty_bin D.data a (7/8) U (by linarith) rows ⟨u.val, u.property⟩ hrows
    obtain ⟨i, k, hi, hi', hone, hcurrent, hround, hnext, hrest⟩ :=
      exists_actual_buffered_bin (D.naturalFamily u.val) hn T e hT he
        (bufferCount e) (bufferCount_spec e he).1 (bufferCount_spec e he).2
    have hki : k ≤ bufferGridCount e := by
      have hk : (k : ℝ) ≤ 1/e := (le_div_iff₀ he).mpr (by nlinarith)
      exact_mod_cast hk.trans (Nat.le_ceil (1/e))
    let p : BufferIndex e := (⟨i, by omega⟩, ⟨k, by omega⟩)
    refine ⟨p, hi, hn, ?_, ?_, ?_, ?_, ?_⟩
    · exact hcurrent.trans ((zeroMaximum_le_beta _ hn hbn _).trans hβ)
    · have hlarge : U ≤ (3*i : ℕ)*T := by
        have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
        push_cast
        nlinarith
      have hz := zeroMaximum_mono (D.naturalFamily u.val) hn hlarge
      rw [D.natural_maximum u.val hraw U] at hz
      push_cast at hz
      dsimp [bufferValue, p]
      linarith
    · simpa only [bufferValue, p, Nat.cast_mul, Nat.cast_ofNat] using hcurrent
    · simpa only [bufferValue, p, Nat.cast_mul, Nat.cast_ofNat] using hround
    · simpa only [bufferValue, p] using hnext
  choose select hselect using one
  exact ⟨select, hselect⟩

/-- Exact finite partition; no growing character dictionary is introduced. -/
theorem selected_partition_card
    (rows : Finset FreeRow) (e : ℝ) (select : rows → BufferIndex e) :
    rows.card = ∑ p : BufferIndex e,
      (rows.attach.filter (fun u => select u = p)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := rows.attach) (t := Finset.univ)
    (f := select) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Finset.card_attach] using h

#print axioms actual_buffered_partition
end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL Cycle61.Density.BufferedPartition -/

/- BEGIN ORIGINAL Cycle61.Density.Rounding; sha256 3645abed796ddd7267daf82ed5eaa27a6613020b193b01637c20a3cd8bb215ad -/
section
                                  

set_option autoImplicit false
namespace OAI.SevenEighths.LocalMoment

theorem unmarkedDensity_rounding {a b e : ℝ}
    (ha : a ≤ 7/8) (hb : b ≤ 7/8) (he : 0 ≤ e) (hab : a-e ≤ b) :
    unmarkedDensity (2*b-1) ≤ unmarkedDensity (2*a-1) + 3*e := by
  let A : ℝ := 5-2*(2*a-1)
  let B : ℝ := 5-2*(2*b-1)
  have hA : 7/2 ≤ A := by dsimp [A]; linarith
  have hB : 7/2 ≤ B := by dsimp [B]; linarith
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hprod : 49/4 ≤ A*B := by nlinarith
  have hid : unmarkedDensity (2*b-1) - unmarkedDensity (2*a-1) =
      100*(a-b)/(3*A*B) := by
    change (1-10*(2*b-1)/(3*B))-(1-10*(2*a-1)/(3*A)) = _
    field_simp [hAp.ne', hBp.ne']
    dsimp [A, B]
    ring
  have hh : unmarkedDensity (2*b-1)-unmarkedDensity (2*a-1) ≤ 3*e := by
    rw [hid]
    apply (div_le_iff₀ (by positivity : 0 < 3*A*B)).mpr
    nlinarith
  linarith

theorem unmarkedDensity_le_one {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) :
    unmarkedDensity δ ≤ 1 := by
  unfold unmarkedDensity
  have hden : 0 < 3*(5-2*δ) := by linarith
  have hq : 0 ≤ 10*δ/(3*(5-2*δ)) := div_nonneg (by linarith) hden.le
  linarith

theorem witness_height_power (U τ : ℝ) (I J : ℕ) (hU : 1 ≤ U) (hτ : 0 ≤ τ) :
    (1 + (2*Real.pi*U^(τ/2) + (3*I : ℕ)*U^τ))^J ≤
      (1+2*Real.pi+(3*I : ℕ))^J * U^((J : ℝ)*τ) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hp := Real.one_le_rpow hU hτ
  have hm := Real.rpow_le_rpow_of_exponent_le hU (show τ/2 ≤ τ by linarith)
  have hbase : 1 + (2*Real.pi*U^(τ/2) + (3*I : ℕ)*U^τ) ≤
      (1+2*Real.pi+(3*I : ℕ))*U^τ := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ ((1+2*Real.pi+(3*I : ℕ))*U^τ)^J :=
      pow_le_pow_left₀ (by positivity) hbase J
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (U^τ) J, ← Real.rpow_mul hUp.le]
      congr 2
      ring

#print axioms unmarkedDensity_rounding
end OAI.SevenEighths.LocalMoment

end
/- END ORIGINAL Cycle61.Density.Rounding -/
