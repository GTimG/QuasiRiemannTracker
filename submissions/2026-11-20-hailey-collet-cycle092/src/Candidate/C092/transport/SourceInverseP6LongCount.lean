/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual amplified inverse count for the arbitrary-ray same-zero source union,
including its true fixed-inducing free-core dictionary. -/
import Candidate.C092.transport.SourceInverseP6ActualCount
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor.Unmarked

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6LongCount_cf28d77f159af72c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_source_unmarked_inverse
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η η₀ : Character) (εm : ℝ) (hεm : 0 < εm) :
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧ ∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ (Z B bΦ : ℝ) (s : NaturalState Z B bΦ),s.character=η  →  s.puncture=1  → 
    ∀ F : ∀ u : FreeRow,NaturalRow s.character u.val,
    ∀ rows : Finset FreeRow,(∀ u∈rows,((Ideal.span {u.val}).absNorm:ℝ) ≤ U)  → 
    ∀ (a ε cutoff T allowance height : ℝ) (i : ℕ),
      1/2 ≤ a  →  0 ≤ ε  →  ε ≤ 1/1000  →  1 ≤ cutoff  →  cutoff ≤ 3/2  → 
      0 ≤ height  →  2*Real.pi*allowance+(3*i:ℕ)*T ≤ height  → 
    ∀ ws : ∀ u : rows,SupportedWitness (family M H hH s η₀ (F u.val)) U a ε cutoff T allowance i,
    ∀ (label : Option (RayQuotient.Characters M H × RayQuotient.Characters M H))
      (left right : Fin (dyadicLength U)),
      (∀ u,(ws u).label=label)  →  (∀ u,(ws u).left=left)  →  (∀ u,(ws u).right=right)  → 
    let r := Real.logb U ((2:ℝ)^left.val)
    (rows.card:ℝ) ≤ (192*(1+height)*(C*(1+height)^J))*
      U^(max 1 ((1+5*r)/6)-(2*a-1)*r+2*ε+εm) := by
  let Label := Option (RayQuotient.Characters M H × RayQuotient.Characters M H)
  let D := FixedUnmarkedDictionary.ofBases (witnessBase M H hH η η₀)
  obtain ⟨J,C,hC,hev⟩ := Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor.core_unmarked_fields D
    canonicalDensityCountingSetup εm hεm hβ
  refine ⟨J,C,hC,hev.mono ?_⟩
  intro U hU
  refine ⟨hU.1,?_⟩
  intro Z B bΦ s hη hpuncture F rows hnorm a ε cutoff T allowance height i
    ha hε hε' hcut hcut' hh hfreq ws label left right hlabel hleft hright
  dsimp only
  have hUp : 0 < U := zero_lt_one.trans hU.1
  by_cases hne : rows.Nonempty
  · obtain ⟨u0,hu0⟩ := hne
    let pick : FreeRow → rows := fun u => if hu:u∈rows then ⟨u,hu⟩ else ⟨u0,hu0⟩
    have hp (u : FreeRow) (hu : u∈rows) : pick u=⟨u,hu⟩ := dif_pos hu
    let χ := fun u => family M H hH s η₀ (F (pick u).val)
    let wit := fun u => ws (pick u)
    have hcoeff : ∀ u∈rows,∀ j,∀ I:Ideal O,idealCoeff (χ u j) I=
        if (fun _ : Label => false) j then starRingEnd ℂ (idealCoeff ((D.data j).character ⟨u.val,u.property.1⟩) I)
        else idealCoeff ((D.data j).character ⟨u.val,u.property.1⟩) I := by
      intro u hu j I
      simp only [Bool.false_eq_true,ite_false]
      dsimp only [χ]
      rw [hp u hu]
      exact (union_coefficients M H hH s η η₀ hη hpuncture u (F u) j I).trans
        (LocalMoment.natural_raw_coefficients _ ⟨u.val,u.property.1⟩ I)
    have hfib : ∀ u∈rows,(wit u).label=label ∧ (wit u).left=left ∧ (wit u).right=right := by
      intro u hu
      dsimp only [wit]
      rw [hp u hu]
      exact ⟨hlabel ⟨u,hu⟩,hleft ⟨u,hu⟩,hright ⟨u,hu⟩⟩
    exact (hU.2 a ε cutoff T allowance height i ha hε hε' hcut hcut' hh hfreq rows χ
      (fun _ => false) hnorm hcoeff wit label left right hfib (C*(1+height)^J) le_rfl).1
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms actual_source_unmarked_inverse
end
end QRH.Cycle092.SourceInverseP6
