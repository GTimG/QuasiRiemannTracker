import Candidate.Cycle62.Physical.FinalRadius

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62FinalRadius
noncomputable section
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRadicalBudget Filter
open CenteredMomentFirstScale

/-- One threshold pays all fixed conductor, support and presentation losses.
The finite anchor family and ambient slot count are fixed before every live
mass, common allocation, row and height. `J` includes any fixed error cost. -/
theorem fixed_final_width_loss_uniform {Label : Type*} [Fintype Label]
    (η : Label→Character) (N : ℕ) (b J ε Mmin : ℝ)
    (hb : 0<b) (hJ : 0<J) (hε : 0<ε) (hMmin : 0<Mmin) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀j:Label,∀M:ℝ,Mmin≤M →
      Real.logb Z ((η j).modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+Real.logb Z J+
        Real.logb Z (4*(fixedFactor:ℝ))≤ε*M := by
  let A := fun j : Label => ((η j).modulus.absNorm:ℝ)*fixedPresentationCost*
    b^(2*N)*J*(4*(fixedFactor:ℝ))
  have ha (j:Label) : 0<A j := by
    have hn := norm_pos _ (η j).modulus_ne_bot
    have hf := fixedPresentationCost_pos
    have hg : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
    dsimp [A]
    positivity
  have ht (j:Label) : ∀ᶠ Z : ℝ in atTop,A j≤Z^(ε*Mmin) :=
    (tendsto_rpow_atTop (mul_pos hε hMmin)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_all.mpr ht,eventually_gt_atTop (1:ℝ)] with Z hA hZ
  refine ⟨hZ,?_⟩
  intro j M hM
  have hh := Real.logb_le_logb_of_le hZ (ha j) (hA j)
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  have hn := norm_pos _ (η j).modulus_ne_bot
  have hf := fixedPresentationCost_pos
  have hg : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  dsimp [A] at hh
  simp (disch := positivity) only [Real.logb_mul, Real.logb_pow] at hh
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) hg.ne']
  have hm := mul_le_mul_of_nonneg_left hM hε.le
  linarith

end
end OAI.SevenEighths.Cycle62FinalRadius
#print axioms OAI.SevenEighths.Cycle62FinalRadius.fixed_final_width_loss_uniform
