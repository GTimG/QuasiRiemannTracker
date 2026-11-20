/- O.2 finite geometry adaptation by Hailey Collet; original Bebel proof follows. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Linear-work continuous geometry of the checked finite chain. -/
import Candidate.C092.transport.TangentExtensionCertificateHigh
import Candidate.C092.transport.TangentExtensionData
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.FinitePartition

set_option autoImplicit false
noncomputable section
namespace QRH.Cycle092.TangentExtension.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.TwoSlot.AnchorZeroLoss

def sourceLine (a b x : ℝ) : ℝ := a-b*x

theorem cast_Y (s : Stage) (r : ℚ) :
    ((s.Y r:ℚ):ℝ)=fY (s.R:ℝ) s.gain s.cut r := by
  simp only [Stage.Y,fY,fu]
  push_cast
  rfl

theorem cast_line (s : Stage) (r : ℚ) :
    ((s.line r:ℚ):ℝ)=sourceLine s.a0 s.a1 r := by
  simp only [Stage.line,fline,sourceLine,Rat.cast_sub,Rat.cast_mul]

/-- The six checked adjacent statements, in the real source geometry. -/
theorem adjacent_geometry (n : ℕ) (hn : n+1<68) :
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
def right (n : ℕ) : ℝ := (stage (min n 67)).R

theorem right_eq (n : ℕ) (hn : n<68) : right n=((stage n).R:ℝ) := by
  unfold right
  rw [Nat.min_eq_left (show n≤67 by omega)]

theorem right_antitone : Antitone right := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n<67
  · rw [right_eq n (by omega),right_eq (n+1) (by omega),(adjacent_geometry n (by omega)).1]
    have hb := (Stage.ok_sound (local_checked n (by omega))).1
    have hlt := hb.2.2.2.1
    exact (Rat.cast_le.mpr hlt.le)
  · unfold right
    rw [Nat.min_eq_right (show 67≤n by omega),Nat.min_eq_right (show 67≤n+1 by omega)]

/-- All previous outputs dominate the current line throughout their full
intervals; only adjacent certificate entries are used. -/
theorem previous_minorant (i : ℕ) (hi : i<68) (j : ℕ) (hj : j < i)
    (x : ℝ) (hlo : ((stage j).left:ℝ)≤x) (hhi : x≤(stage j).R) :
    sourceLine (stage i).a0 (stage i).a1 x+(pad:ℝ)<
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut x := by
  obtain ⟨_,_,_,_,hL,hR⟩ := adjacent_geometry j (by omega)
  have hb := (Stage.ok_sound (local_checked j (by omega))).1
  have hlt : ((stage j).left:ℝ)<(stage j).R := by exact_mod_cast hb.2.2.2.1
  have h := QRH.Cycle092.TangentExtension.source_minorant_between hlt hlo hhi hL hR
  have hi0 := congrArg (fun q : ℚ=>(q:ℝ)) (all_line ⟨i,hi⟩).1
  have hi1 := congrArg (fun q : ℚ=>(q:ℝ)) (all_line ⟨i,hi⟩).2
  have hj0 := congrArg (fun q : ℚ=>(q:ℝ)) (all_line ⟨j+1,by omega⟩).1
  have hj1 := congrArg (fun q : ℚ=>(q:ℝ)) (all_line ⟨j+1,by omega⟩).2
  dsimp only [sourceLine] at h ⊢
  rw [hi0,hi1]
  rwa [hj0,hj1] at h

end QRH.Cycle092.TangentExtension.Certificate
#print axioms QRH.Cycle092.TangentExtension.Certificate.previous_minorant
