/- The conditions under which the second step applies to the state left by the fixed deletion of a LOW child of the
first step. Released under Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.SecondLevelFamily
import Candidate.Cycle63.Moment.LowBranch.SecondStepReturn

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open HeckeFamily CenteredMomentEnergyState

/-- The conditions under which the second step applies, the predicate `Applicable` of `SecondStepReturnAt` for the
grid of mesh `1/G` and the loss floor `lossFloor`: the arithmetic conditions `SecondStepArithmetic` on the width of
the state `s`, its plain lengths `x₁`, `x₂`, its slot length `z`, its unit `W` and the total length `length`, the
amplifier `amp` and the losses `loss` of the second step, and a presentation `Presented η₀ Z s v₁ T` of the state by
the multiplier `v₁` in the dictionary of `η₀`, with the heights of the zeros at most `T`. -/
def SecondApplicable {Bmask bΦ : ℝ} (G : ℕ) (lossFloor : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → Prop)
    (η₀ : Character) (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v₁ : O) (x₁ x₂ z W T length amp loss : ℝ) : Prop :=
  Cycle63.SecondStepArithmetic G lossFloor s.width x₁ x₂ z W length amp loss ∧ Presented η₀ Z s v₁ T

/-- The second step applies at a smaller loss floor and under a weaker presentation. -/
theorem SecondApplicable.mono {Bmask bΦ : ℝ} {G : ℕ} {lossFloor lossFloor' : ℝ}
    {Presented Presented' : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → Prop}
    (hloss : lossFloor' ≤ lossFloor) (hP : ∀ η₀ Z s v₁ T, Presented η₀ Z s v₁ T → Presented' η₀ Z s v₁ T)
    {η₀ : Character} {Z : ℝ} {s : NaturalState Z Bmask bΦ} {v₁ : O} {x₁ x₂ z W T length amp loss : ℝ}
    (h : SecondApplicable G lossFloor Presented η₀ Z s v₁ x₁ x₂ z W T length amp loss) :
    SecondApplicable G lossFloor' Presented' η₀ Z s v₁ x₁ x₂ z W T length amp loss :=
  ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, hloss.trans h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2⟩,
    hP _ _ _ _ _ h.2⟩

/-- The return of the second step for a predicate `Applicable` holds for every predicate that implies it. -/
theorem SecondStepReturnAt.mono {α : Type*} [Fintype α] {Base : Type}
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {base : Character → Base → Character} {Wslot : ℝ → ℂ} {bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B : ℝ}
    {Applicable Applicable' :
      Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (himp : ∀ η₀ Z s v₁ x₁ x₂ z W T length amp loss, Applicable' η₀ Z s v₁ x₁ x₂ z W T length amp loss →
      Applicable η₀ Z s v₁ x₁ x₂ z W T length amp loss)
    (h : SecondStepReturnAt (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B Applicable) :
    SecondStepReturnAt (α := α) M H hH base Wslot bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B Applicable' := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree, S, Kclass, C, hC, hev⟩ := h η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree, S, Kclass, C, hC, hev.mono fun Z hZ => ⟨hZ.1, ?_⟩⟩
  intro J R θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hX₁' hX₂' v₁ T W length amp loss happ
  exact hZ.2 J R θ w σ v t height hw0 hwL hlo hhi hh hv s hs hW p X₁ X₂ hX₁ hX₂ hX₁' hX₂' v₁ T W length amp loss
    (himp _ _ _ _ _ _ _ _ _ _ _ _ happ)

end
end OAI.SevenEighths.Cycle63Moment.LowBranch
