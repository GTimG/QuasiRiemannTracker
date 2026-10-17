import Candidate.Cycle63.Moment.HighSourceEnergy

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedChildCapacity
open Cycle63.Physical CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O
variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {P : HighSourceParameters} {η₀ : Character} {Z : ℝ}
variable {Dict : Type*} [Fintype Dict]

/-- The clipped total retains exactly the post-clipping cost. This identity
uses the literal source scales and residual allocation, on either rectangle. -/
theorem high_source_total_raw (D : HighSourceDatum M H P η₀ Z Dict) (hZ : 1<Z)
    (hscale : ∀i,D.source.P i=Z^(D.w i)) :
    D.total P=Real.logb Z (preVolume D.source)-
      Real.logb Z (formalReductionFactor D.projector D.allocation D.source.P)+
      sourcePostClip D.source.toSource D.second Z D.projector D.allocation := by
  let X := sourcePlainScales D.source.toSource D.second
  have hX : ∀j,0<X j := by
    intro j
    cases hs : D.second <;> fin_cases j
    · simpa [X,sourcePlainScales,hs] using D.source.X₁_pos
    · simpa [X,sourcePlainScales,hs] using D.source.X₂_pos
    · simpa [X,sourcePlainScales,hs] using D.source.Y₁_pos
    · simpa [X,sourcePlainScales,hs] using D.source.Y₂_pos
  have hprod : X 0*X 1=D.source.X₁*D.source.X₂ := by
    cases hs : D.second <;> simp [X,sourcePlainScales,hs,D.source.same_product]
  have hraw : Real.logb Z (preVolume D.source)=
      Real.logb Z (X 0)+Real.logb Z (X 1)+∑i,D.w i := by
    rw [preVolume,←hprod,Real.logb_mul (mul_pos (hX 0) (hX 1)).ne'
      (Finset.prod_pos (fun i _=>D.source.P_pos i)).ne',
      Real.logb_mul (hX 0).ne' (hX 1).ne',
      Real.logb_prod _ _ (fun i _=>(D.source.P_pos i).ne')]
    simp_rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hpre : (∑j,Real.logb Z (CenteredMomentRetainedProfile.clippedScale (X j)))=
      Real.logb Z (X 0)+Real.logb Z (X 1)+negativeTotal (fun j=>Real.logb Z (X j)) := by
    simp only [negativeTotal,Fin.sum_univ_two]
    rw [logb_clipped_scale Z _ hZ (hX 0),logb_clipped_scale Z _ hZ (hX 1)]
    linarith [max_positive_sub (Real.logb Z (X 0)),max_positive_sub (Real.logb Z (X 1))]
  unfold HighSourceDatum.total
  change (∑j,Real.logb Z (CenteredMomentRetainedProfile.clippedScale (X j)))+
    (∑i,D.w i)-clippedReduction _ (fun j=>Real.logb Z (X j)) _=_
  rw [hpre,hraw]
  unfold clippedReduction sourcePostClip
  dsimp [X]
  ring

/-- For every high-bin exponent in [0,1], division by the actual clipping
normalizer pays all clipping growth. Residual divisors can only lower the
remaining exponent, so the bound is uniform before summing their dyads. -/
theorem high_source_exponent_le_raw (D : HighSourceDatum M H P η₀ Z Dict)
    (hZ : 1<Z) (hscale : ∀i,D.source.P i=Z^(D.w i))
    (hw : ∀i,0≤D.w i) (δ : ℝ) (hδ : 0≤δ) (hδ' : δ≤1) :
    δ*D.total P-sourcePostClip D.source.toSource D.second Z D.projector D.allocation ≤
      δ*Real.logb Z (preVolume D.source) := by
  have hP : ∀i,1≤D.source.P i := by
    intro i
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i)
  have hr : 0≤Real.logb Z (formalReductionFactor D.projector D.allocation D.source.P) :=
    Real.logb_nonneg hZ (formalReduction_ge_one _ _ _ hP)
  have hc : 0≤sourcePostClip D.source.toSource D.second Z D.projector D.allocation := by
    unfold sourcePostClip negativeTotal
    exact Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  rw [high_source_total_raw D hZ hscale]
  nlinarith [mul_nonneg hδ hr,mul_nonneg (sub_nonneg.mpr hδ') hc]

end
end OAI.SevenEighths.Cycle63Moment
#print axioms OAI.SevenEighths.Cycle63Moment.high_source_total_raw
#print axioms OAI.SevenEighths.Cycle63Moment.high_source_exponent_le_raw
