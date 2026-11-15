/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Linear-work continuous geometry of the checked finite chain. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.CheckedStage
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.LineNesting
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.FinitePartition

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData

theorem cast_Y (s : Stage) (r : ℚ) :
    ((s.Y r:ℚ):ℝ)=fY (s.R:ℝ) s.gain s.cut r := by
  simp only [Stage.Y,fY,fu]
  push_cast
  rfl

theorem cast_line (s : Stage) (r : ℚ) :
    ((s.line r:ℚ):ℝ)=sourceLine s.a0 s.a1 r := by
  simp only [Stage.line,fline,sourceLine,Rat.cast_sub,Rat.cast_mul]

/-- The six checked adjacent statements, in the real source geometry. -/
theorem adjacent_geometry (n : ℕ) (hn : n+1<8192) :
    ((stage (n+1)).R:ℝ)=(stage n).left ∧
    ((stage (n+1)).gain:ℝ)≤fY ((stage n).R:ℝ) (stage n).gain (stage n).cut (stage n).left ∧
    ((stage n).a1:ℝ)≤(stage (n+1)).a1 ∧
    sourceLine (stage (n+1)).a0 (stage (n+1)).a1 (stage n).R≤
      sourceLine (stage n).a0 (stage n).a1 (stage n).R ∧
    sourceLine (stage (n+1)).a0 (stage (n+1)).a1 (stage n).left+(pad:ℝ)<
      fY ((stage n).R:ℝ) (stage n).gain (stage n).cut (stage n).left ∧
    sourceLine (stage (n+1)).a0 (stage (n+1)).a1 (stage n).R+(pad:ℝ)<
      fY ((stage n).R:ℝ) (stage n).gain (stage n).cut (stage n).R := by
  obtain ⟨he,hg,hs,hb,hl,hr⟩ := adjacent_checked n hn
  refine ⟨by exact_mod_cast he,?_,by exact_mod_cast hs,?_,?_,?_⟩
  · have h : ((stage (n+1)).gain:ℝ)≤(((stage n).Y (stage n).left:ℚ):ℝ) := Rat.cast_le.mpr hg
    rw [cast_Y] at h
    exact h
  · have h : (((stage (n+1)).line (stage n).R:ℚ):ℝ)≤(((stage n).line (stage n).R:ℚ):ℝ) := Rat.cast_le.mpr hb
    simpa only [cast_line] using h
  · have h : (((stage (n+1)).line (stage n).left+pad:ℚ):ℝ)<
        (((stage n).Y (stage n).left:ℚ):ℝ) := Rat.cast_lt.mpr hl
    simpa only [Rat.cast_add,cast_line,cast_Y] using h
  · have h : (((stage (n+1)).line (stage n).R+pad:ℚ):ℝ)<
        (((stage n).Y (stage n).R:ℚ):ℝ) := Rat.cast_lt.mpr hr
    simpa only [Rat.cast_add,cast_line,cast_Y] using h

/-- A constant extension after the last stage avoids imposing conditions on
out-of-range array defaults. -/
def right (n : ℕ) : ℝ := (stage (min n 8191)).R

theorem right_eq (n : ℕ) (hn : n<8192) : right n=((stage n).R:ℝ) := by
  unfold right
  rw [Nat.min_eq_left (show n≤8191 by omega)]

theorem right_antitone : Antitone right := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n<8191
  · rw [right_eq n (by omega),right_eq (n+1) (by omega),(adjacent_geometry n (by omega)).1]
    have hb := (Stage.ok_sound (local_checked n (by omega))).1
    have hlt := hb.2.2.2.1
    exact (Rat.cast_le.mpr hlt.le)
  · unfold right
    rw [Nat.min_eq_right (show 8191≤n by omega),Nat.min_eq_right (show 8191≤n+1 by omega)]

/-- All previous outputs dominate the current line throughout their full
intervals; only adjacent certificate entries are used. -/
theorem previous_minorant (i : ℕ) (hi : i<8192) (j : ℕ) (hj : j < i)
    (x : ℝ) (hlo : ((stage j).left:ℝ)≤x) (hhi : x≤(stage j).R) :
    sourceLine (stage i).a0 (stage i).a1 x+(pad:ℝ)<
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut x := by
  have h := all_earlier_minorants 8192 right
    (fun n=>(stage n).a0) (fun n=>(stage n).a1)
    (fun n x=>fY ((stage n).R:ℝ) (stage n).gain (stage n).cut x) (pad:ℝ)
    right_antitone ?_ ?_ ?_
  · apply h i hi j hj x
    · rw [right_eq (j+1) (by omega),(adjacent_geometry j (by omega)).1]
      exact hlo
    · rw [right_eq j (by omega)]
      exact hhi
  · intro n hn x hlo hhi
    obtain ⟨he,hgain,hslope,hboundary,hL,hR⟩ := adjacent_geometry n hn
    rw [right_eq (n+1) hn,he] at hlo
    rw [right_eq n (by omega)] at hhi
    have hb := (Stage.ok_sound (local_checked n (by omega))).1
    have hlt : ((stage n).left:ℝ)<(stage n).R := by exact_mod_cast hb.2.2.2.1
    exact Qrh.TwoSlot.AnchorContinuum.source_minorant_between hlt hlo hhi hL hR
  · intro n hn
    exact (adjacent_geometry n hn).2.2.1
  · intro n hn
    rw [right_eq n (by omega)]
    exact (adjacent_geometry n hn).2.2.2.1

end Qrh.TwoSlot.AnchorZeroLoss.Certificate
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Certificate.previous_minorant
