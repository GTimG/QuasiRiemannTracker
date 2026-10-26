/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal source coefficients, buffered maxima and physical raw slots. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.GeometryMarkedPacket
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.CommonRawWeights
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.NaturalEndpoint

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckePrimeRay HeckeFiniteDeletion HeckeDetectorZeros LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Cycle61Moment Cycle61InitialMass WeightedHigh
local notation "O" => HeckeFamily.O

theorem nonprincipal_coefficients_congr (χ ψ : Character)
    (hc : ∀I,idealCoeff χ I=idealCoeff ψ I) (hn : χ.residue≠1) : ψ.residue≠1 := by
  intro hp
  exact hn ((principal_iff_of_mask χ ψ (coefficient_equality_mask χ ψ hc)).mpr hp)

theorem maximum_coefficients_congr {Label : Type*} [Fintype Label]
    (χ ψ : Label→Character) (hc : ∀j I,idealCoeff (χ j) I=idealCoeff (ψ j) I)
    (hn : ∀j,(χ j).residue≠1) (hn' : ∀j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum χ hn T=zeroMaximum ψ hn' T :=
  zeroMaximum_eq_of_mask χ ψ hn hn' T (fun j=>coefficient_equality_mask _ _ (hc j))

theorem actual_zero_of_current_maximum {Label : Type*} [Fintype Label]
    (χ : Label→Character) (hn : ∀j,(χ j).residue≠1) (a T height : ℝ)
    (ha : 51/100<a) (hcurrent : a≤zeroMaximum χ hn T) (hheight : T≤height) :
    ∃j s,LFunction (χ j) s=0 ∧ (s≠1 ∨ (χ j).residue≠1) ∧a≤s.re ∧ |s.im|≤height := by
  obtain ⟨j,s,hzero,ht,hre⟩:=maximum_attained χ hn T (ha.trans_le hcurrent)
  exact ⟨j,s,hzero,Or.inr (hn j),hre ▸ hcurrent,ht.trans hheight⟩

variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem whole_coefficients_congr (η₀ χ ψ : Character)
    (hc : ∀I,idealCoeff χ I=idealCoeff ψ I) (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ χ j) I=
      idealCoeff (wholeSourceFamily M H hH η₀ ψ j) I := by
  cases j with
  | inl j => exact hc I
  | inr j => simp only [wholeSourceFamily,Sum.elim_inr,twistedFamily,idealCoeff_product,hc I]

/-- Both source maxima and nonprincipality transfer to the fixed dictionary
using the exact coefficient identity, with the original puncture retained. -/
theorem whole_dictionary_gates (η₀ χ ψ : Character)
    (hc : ∀I,idealCoeff χ I=idealCoeff ψ I)
    (hn : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1) :
    ∃hn' : ∀j,(wholeSourceFamily M H hH η₀ ψ j).residue≠1,
      ∀T,zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn T=
        zeroMaximum (wholeSourceFamily M H hH η₀ ψ) hn' T := by
  have hfamily:=whole_coefficients_congr M H hH η₀ χ ψ hc
  let hn':=fun j=>nonprincipal_coefficients_congr _ _ (hfamily j) (hn j)
  exact ⟨hn',fun T=>maximum_coefficients_congr _ _ hfamily hn hn' T⟩

theorem labeled_raw_slot_coefficients_congr {Slot Row : Type} [Fintype Slot] [DecidableEq Slot]
    (η₀ : Character) (W : ℝ→ℂ) (Z : ℝ) (w σ v : Slot→ℝ) (t : Row→ℝ)
    (θ : Slot→RayQuotient.Characters M H) (χ ψ : Row→Character) (l : Row)
    (hc : ∀I,idealCoeff (χ l) I=idealCoeff (ψ l) I) (s : Slot) :
    labeledRawSlot M H hH η₀ W Z w σ v t θ χ l s=
      labeledRawSlot M H hH η₀ W Z w σ v t θ ψ l s := by
  unfold labeledRawSlot naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  rw [hc I]

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.whole_dictionary_gates
#print axioms OAI.SevenEighths.Record12518109Natural.actual_zero_of_current_maximum
#print axioms OAI.SevenEighths.Record12518109Natural.labeled_raw_slot_coefficients_congr
