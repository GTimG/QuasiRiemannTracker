import Candidate.Cycle63.Physical.InitialMass.SecondRetainedContraction

set_option autoImplicit false

/-! When the two normalized sums of a ratio fiber carry extra parts `X` and `Y` beyond the targets `E H` and `E/H`
(the rows of a second application of the transforms that are counted at the top level), the contraction bounds the
fiber by `E + (X/H + H Y)/2`: the extra parts enter linearly and the target `E` is unchanged. -/

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentLogDyadic CenteredMomentSectorLocalization

/-- Sides bounded by `E H + X` and `E/H + Y` are bounded by `E' H'` and `E'/H'` for the arithmetic mean
`E' = E + (X/H + H Y)/2` and the balance `H' = √((E H + X)/(E/H + Y))`. -/
theorem balanced_of_returns {E H X Y : ℝ} (hE : 0 < E) (hH : 0 < H) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 < Real.sqrt ((E*H + X)/(E/H + Y)) ∧
    E*H + X ≤ (E + (X/H + H*Y)/2)*Real.sqrt ((E*H + X)/(E/H + Y)) ∧
    E/H + Y ≤ (E + (X/H + H*Y)/2)/Real.sqrt ((E*H + X)/(E/H + Y)) := by
  set a := E*H + X with ha_def
  set b := E/H + Y with hb_def
  set m := E + (X/H + H*Y)/2 with hm_def
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hmab : m = (a/H + H*b)/2 := by
    rw [hm_def, ha_def, hb_def]
    field_simp
    ring
  have hm : 0 < m := by positivity
  -- The arithmetic mean of `a/H` and `H b` dominates their geometric mean `√(a b)`.
  have hsq : a*b ≤ m^2 := by
    rw [hmab]
    have h := sq_nonneg (a/H - H*b)
    have e : (a/H)*(H*b) = a*b := by field_simp
    nlinarith
  have hq : 0 < a/b := div_pos ha hb
  have hs := Real.sqrt_pos.mpr hq
  have hss : Real.sqrt (a/b)^2 = a/b := Real.sq_sqrt hq.le
  refine ⟨hs, ?_, ?_⟩
  · -- `(m √(a/b))² = m² a/b ≥ a²`.
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [mul_pow, hss]
    have : a^2 = (a*b)*(a/b) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hsq hq.le
  · -- `(m/√(a/b))² = m² b/a ≥ b²`.
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [div_pow, hss]
    rw [le_div_iff₀ hq]
    have : b^2*(a/b) = a*b := by field_simp
    rw [this]
    exact hsq

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The two normalized sums of each ratio fiber are bounded by `E H + X` and `E/H + Y`. -/
def SecondReturnBound {Label : Type*} [Fintype Label]
    (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (E H X Y : ℤ→ℝ) : Prop :=
  ∀r∈secondRatioBins (fun l=>(d l).block),∀(reflected : Bool)(t u : ℝ),
    let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val
    let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block
    let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val
    secondNormalizedSum reflected datum (secondEffectiveWeight src weight W) t u≤
      ((if reflected then E r/H r+Y r else E r*H r+X r)*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)

/-- The contraction with extra parts: each ratio fiber costs `E + (X/H + H Y)/2`. -/
theorem restricted_second_ratio_from_returns (W : 𝓢(ℝ,ℂ)) (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (E H X Y : ℤ→ℝ),
      (∀r∈secondRatioBins (fun l=>(d l).block),0<E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤X r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤Y r) →
      SecondReturnBound W degree windowDegree d w E H X Y →
      ‖∑l,w l*(d l).block.value W‖≤
        C*∑r∈secondRatioBins (fun l=>(d l).block),(E r+(X r/H r+H r*Y r)/2)/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hcon⟩ := restricted_second_ratio_from_normalized (α:=α) W A degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro Label _ d w E H X Y hE hH hX hY hret
  let E' := fun r : ℤ => E r+(X r/H r+H r*Y r)/2
  let H' := fun r : ℤ => Real.sqrt ((E r*H r+X r)/(E r/H r+Y r))
  apply hcon d w E' H'
    (fun r hr => by
      have := hE r hr; have := hH r hr; have := hX r hr; have := hY r hr
      dsimp only [E']
      positivity)
    (fun r hr => (balanced_of_returns (hE r hr) (hH r hr) (hX r hr) (hY r hr)).1)
  intro r hr reflected t u
  have hb := balanced_of_returns (hE r hr) (hH r hr) (hX r hr) (hY r hr)
  refine (hret r hr reflected t u).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  cases reflected
  · exact hb.2.1
  · exact hb.2.2

end
end OAI.SevenEighths.Cycle63InitialMass
