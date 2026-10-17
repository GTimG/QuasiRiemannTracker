import Candidate.Target830.Count.Arithmetic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 0

namespace OAI.SevenEighths.Target830.Count
noncomputable section

def affineUPrime (L B p : ℝ) : ℝ :=
  -affineC L B p+(1-p)*(-2*B/L)
def affineJPrime (L δ p : ℝ) : ℝ :=
  (5/6-δ)*(-1-4/L)+δ*(-affineA L p+(1-p)*(-4/L))
def affineAntitone (L B δ p : ℝ) : ℝ :=
  affineU L B p*affineJPrime L δ p-affineUPrime L B p*affineJ L δ p

theorem affineU_hasDerivAt (L B p : ℝ) :
    HasDerivAt (affineU L B) (affineUPrime L B p) p := by
  have hp := hasDerivAt_id p
  have h1 := (hasDerivAt_const p (1:ℝ)).sub hp
  have hc := (hasDerivAt_const p (1:ℝ)).sub (((hp.const_mul 2).mul_const B).div_const L)
  convert h1.mul hc using 1 <;> (try funext z) <;>
    dsimp [affineU,affineC,affineUPrime] <;> ring

theorem affineJ_hasDerivAt (L δ p : ℝ) :
    HasDerivAt (affineJ L δ) (affineJPrime L δ p) p := by
  have hp := hasDerivAt_id p
  have h1 := (hasDerivAt_const p (1:ℝ)).sub hp
  have hd := ((hasDerivAt_const p (3:ℝ)).sub hp).sub ((hp.const_mul 4).div_const L)
  have ha := (hasDerivAt_const p (2:ℝ)).sub ((hp.const_mul 4).div_const L)
  convert (hd.const_mul (5/6-δ)).add ((h1.mul ha).const_mul δ) using 1
    <;> (try funext z) <;> dsimp [affineJ,affineD,affineA,affineJPrime] <;> ring

theorem affineR_hasDerivAt {L B δ p : ℝ} (hj : affineJ L δ p ≠ 0) :
    HasDerivAt (affineR L B δ)
      ((5/6-δ)*δ*(-affineAntitone L B δ p)/(affineJ L δ p)^2) p := by
  have hq := (affineU_hasDerivAt L B p).div (affineJ_hasDerivAt L δ p) hj
  convert (hasDerivAt_const p (1-δ)).add (hq.const_mul ((5/6-δ)*δ)) using 1
    <;> (try funext z) <;> dsimp [affineR,affineAntitone] <;> ring

theorem affineR_antitoneOn {L B δ lo : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 5/6)
    (hj : ∀ p ∈ Set.Icc lo (1/2), 0 < affineJ L δ p)
    (hm : ∀ p ∈ Set.Icc lo (1/2), 0 ≤ affineAntitone L B δ p) :
    AntitoneOn (affineR L B δ) (Set.Icc lo (1/2)) := by
  have hh : ∀ p ∈ Set.Icc lo (1/2),
      HasDerivAt (affineR L B δ)
        ((5/6-δ)*δ*(-affineAntitone L B δ p)/(affineJ L δ p)^2) p :=
    fun p hp => affineR_hasDerivAt (hj p hp).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc lo (1/2))
  · intro p hp
    exact (hh p hp).continuousAt.continuousWithinAt
  · intro p hp
    exact (hh p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hh p (interior_subset hp)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by linarith) hδ) (by linarith [hm p (interior_subset hp)])
    · exact sq_nonneg _

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.affineR_antitoneOn
