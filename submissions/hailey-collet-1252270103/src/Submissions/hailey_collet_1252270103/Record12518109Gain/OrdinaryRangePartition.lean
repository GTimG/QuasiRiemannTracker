/- Range extension of Cycle61 density wrappers, Hailey Collet, Apache-2.0.
The actual maxima count already has lower boundary 51/100; every extended
wrapper body below is checked at the literal boundary 81/100. -/
import Submissions.hailey_collet_1252270103.Cycle61.Density.BufferedPartition
import Submissions.hailey_collet_1252270103.Cycle61.Density.ActualMaximaCount
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace SevenEighths.Record12518109GainOrdinaryRange
open ProbePhysical
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbeHighRowFamily
theorem actual_buffered_partition {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (e U T a : ℝ)
    (he : 0 < e) (hT : 2 < T)
    (hheight : U ≤ T)
    (hβ : HeckeZeroSupremum.beta ≤ 7/8)
    (rows : Finset FreeRow)
    (ha : 81/100 ≤ a)
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


end SevenEighths.Record12518109GainOrdinaryRange
end
end OAI
