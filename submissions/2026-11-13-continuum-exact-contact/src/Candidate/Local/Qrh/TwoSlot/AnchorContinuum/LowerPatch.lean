/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Reuse the existing checked finite stages below the continuum join. Only the
new affine comparisons are checked; the stage gates are not replayed. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.RationalSource
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteSource

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Qrh.TwoSlot.AnchorContinuum.RationalSource
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData (fY)
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract

def lowerCheck (j : ℕ) (padding : ℚ := 0) : Prop :=
  g0+padding-g1*(stage j).left < (stage j).Y (stage j).left ∧
  g0+padding-g1*(stage j).R < (stage j).Y (stage j).R
instance (j : ℕ) (padding : ℚ) : Decidable (lowerCheck j padding) := by
  unfold lowerCheck
  infer_instance

theorem lower_checked : ∀ i : Fin 113, lowerCheck (8079+i.val) := by decide +kernel

theorem join_checked : (3/4:ℚ) < (stage 8079).R := by decide +kernel

theorem lower_moments_with_pad (padding : ℚ)
    (hchecked : ∀ i : Fin 113, lowerCheck (8079+i.val) padding)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (1467/2000) (3/4) ((g0+padding:ℚ):ℝ) (g1:ℝ) := by
  intro r hlo hhi
  obtain ⟨j,hj,hrlo,hrhi⟩ := full_cover hlo (by linarith)
  have hjlo : 8079 ≤ j := by
    by_contra hn
    have hjlt : j < 8079 := by omega
    have he := (adjacent_geometry j (by omega)).1
    have ha := right_antitone (show j+1 ≤ 8079 by omega)
    rw [right_eq (j+1) (by omega),right_eq 8079 (by norm_num),he] at ha
    have hc : (3/4:ℝ) < (stage 8079).R := by
      have ht : ((3/4:ℚ):ℝ) < ((stage 8079).R:ℝ) := Rat.cast_lt.mpr join_checked
      norm_num only [Rat.cast_div,Rat.cast_ofNat] at ht
      exact ht
    linarith
  have hc := hchecked ⟨j-8079,by omega⟩
  have he : 8079+(⟨j-8079,by omega⟩ : Fin 113).val = j := by simp; omega
  rw [he] at hc
  have hl : ((g0+padding:ℚ):ℝ)-(g1:ℝ)*(stage j).left <
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut (stage j).left := by
    have hh : ((g0+padding-g1*(stage j).left:ℚ):ℝ) < (((stage j).Y (stage j).left:ℚ):ℝ) :=
      Rat.cast_lt.mpr hc.1
    simpa only [Rat.cast_sub,Rat.cast_mul,cast_Y] using hh
  have hh : ((g0+padding:ℚ):ℝ)-(g1:ℝ)*(stage j).R <
      fY ((stage j).R:ℝ) (stage j).gain (stage j).cut (stage j).R := by
    have ht : ((g0+padding-g1*(stage j).R:ℚ):ℝ) < (((stage j).Y (stage j).R:ℚ):ℝ) :=
      Rat.cast_lt.mpr hc.2
    simpa only [Rat.cast_sub,Rat.cast_mul,cast_Y] using ht
  have hb := (Stage.ok_sound (local_checked j hj)).1
  have hlt : ((stage j).left:ℝ) < (stage j).R := by exact_mod_cast hb.2.2.2.1
  have hm := source_minorant_between (pad := 0) hlt hrlo hrhi
    (show ((g0+padding:ℚ):ℝ)-(g1:ℝ)*(stage j).left+0 < _ by simpa only [line,add_zero] using hl)
    (show ((g0+padding:ℚ):ℝ)-(g1:ℝ)*(stage j).R+0 < _ by simpa only [line,add_zero] using hh)
  have hs := all_stage_outputs pr103Face hβ (Reserve.reserveParametricSource hβ)
    (Driver.pr103_parent hβ) (Reserve.base_anchor_native hβ) j hj r hrlo hrhi
  apply hs.mono le_rfl
  linarith

/-- The frozen rational source is the zero-padding instance. -/
theorem lower_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    ImprovedMoments (1467/2000) (3/4) (g0:ℝ) (g1:ℝ) := by
  simpa only [add_zero] using lower_moments_with_pad 0 lower_checked hβ

end
end Qrh.TwoSlot.AnchorContinuum.RationalSource
#print axioms Qrh.TwoSlot.AnchorContinuum.RationalSource.lower_moments
