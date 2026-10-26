import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalRadius
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalRadius
noncomputable section
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRadicalBudget Filter
open CenteredMomentFirstScale

/-- One threshold pays all fixed support and presentation losses. It precedes
every character, so the conductor of a parent stays an exact term of the width.
The ambient slot count is fixed before every live mass, common allocation, row
and height. `J` includes any fixed error cost. -/
theorem fixed_final_width_constants_uniform (N : ℕ) (b J ε Mmin : ℝ)
    (hb : 0<b) (hJ : 0<J) (hε : 0<ε) (hMmin : 0<Mmin) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀M:ℝ,Mmin≤M →
      Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+Real.logb Z J+
        Real.logb Z (4*(fixedFactor:ℝ))≤ε*M := by
  let A := fixedPresentationCost*b^(2*N)*J*(4*(fixedFactor:ℝ))
  have hf := fixedPresentationCost_pos
  have hg : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  have ha : 0<A := by
    dsimp [A]
    positivity
  have ht : ∀ᶠ Z : ℝ in atTop,A≤Z^(ε*Mmin) :=
    (tendsto_rpow_atTop (mul_pos hε hMmin)).eventually (eventually_ge_atTop _)
  filter_upwards [ht,eventually_gt_atTop (1:ℝ)] with Z hA hZ
  refine ⟨hZ,?_⟩
  intro M hM
  have hh := Real.logb_le_logb_of_le hZ ha hA
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  dsimp [A] at hh
  simp (disch := positivity) only [Real.logb_mul, Real.logb_pow] at hh
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) hg.ne']
  have hm := mul_le_mul_of_nonneg_left hM hε.le
  linarith

end
end OAI.SevenEighths.Cycle63FinalRadius

end Record1252270103Bootstrap.PR67
