import Candidate.Cycle62.Moment.LowBranch.ChildDictionary
import Candidate.Cycle62.Physical.ClippedProjectorShell

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The literal final positive daughter aggregate, after the second common
allocation and residual squarefree allocation. No radial or row supremum. -/
def finalPositiveEnergy (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then
    ‖Cycle62.Physical.sourcePositiveRow s.toSource second L a z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0

/-- Exact identification of the final aggregate with the old moment energy.
Only the two retained plain cutoffs are clipped; the puncture and slot widths
are unchanged. The two rectangles are addressed independently. -/
theorem final_positive_energy_eq (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X := Cycle62.Physical.sourcePlainScales s.toSource second
    let X₁ := X 0/(Ideal.absNorm (selectedPlain L a 0):ℝ)
    let X₂ := X 1/(Ideal.absNorm (selectedPlain L a 1):ℝ)
    finalPositiveEnergy s second L a keep Φ K =
      energy s.η s.m s.A s.t (dilated s.W₁ (clipDilation X₁))
        (dilated s.W₂ (clipDilation X₂))
        (fun i : liveIndices L a => s.slots i)
        (fun i : liveIndices L a => s.coefficient i)
        (fun i : liveIndices L a => s.P i)
        (clippedScale X₁) (clippedScale X₂) keep Φ K := by
  rfl

/-- Exact final daughter scales, including the independent rectangle. -/
def finalPlain (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (j : Fin 2) : ℝ :=
  clippedScale (Cycle62.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain L a j):ℝ))

/-- Literal dictionary transport to a natural state. These are coefficient,
mask and scale identities, rather than an assumed analytic estimate. -/
theorem final_energy_eq_natural
    {Z Bmask bΦ ap bp : ℝ} (st : CenteredMomentEnergyState.NaturalState Z Bmask bΦ)
    (p : CenteredMomentFiniteProfileExceptional.Profiles ap bp) (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (J : Finset α)
    (pool : α → Finset (Ideal O)) (coeff : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ : ℝ) (low : O → Prop)
    (hJ : liveIndices L a = J) (hchar : s.η = st.character)
    (hmask : s.m = st.mask) (hA : s.A = 1) (ht : s.t = t)
    (hpool : ∀ j, s.slots j = pool j) (hcoeff : ∀ j I, s.coefficient j I = coeff j I)
    (hP : ∀ j, s.P j = P j)
    (hp₁ : dilated s.W₁ (clipDilation
      (Cycle62.Physical.sourcePlainScales s.toSource second 0/(Ideal.absNorm (selectedPlain L a 0):ℝ))) = p.profile 0)
    (hp₂ : dilated s.W₂ (clipDilation
      (Cycle62.Physical.sourcePlainScales s.toSource second 1/(Ideal.absNorm (selectedPlain L a 1):ℝ))) = p.profile 1)
    (hX₁ : finalPlain s second L a 0 = X₁) (hX₂ : finalPlain s second L a 1 = X₂) :
    finalPositiveEnergy s second L a (fun z => st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale =
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun j : J => pool j) (fun j : J => coeff j) (fun j : J => P j)
      X₁ X₂ (fun z => st.radial.keep z ∧ low z) st.radial.profile st.radial.scale := by
  rw [final_positive_energy_eq]
  rw [hchar,hmask,hA,ht,hp₁,hp₂]
  change energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun j : liveIndices L a => s.slots j) (fun j : liveIndices L a => s.coefficient j)
    (fun j : liveIndices L a => s.P j) (finalPlain s second L a 0) (finalPlain s second L a 1)
    (fun z => st.radial.keep z ∧ low z) st.radial.profile st.radial.scale = _
  simp_rw [hpool, funext (hcoeff _), hP]
  rw [hJ,hX₁,hX₂]

#print axioms final_energy_eq_natural
#print axioms final_positive_energy_eq
end
end OAI.SevenEighths.Cycle62Moment.LowBranch
