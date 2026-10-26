import Candidate.Cycle63.Density.NaturalDictionary

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
