/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular source union and original slots retain their coefficients
when transported to the arbitrary fixed source dictionary. -/
import Candidate.C092.transport.SourceInverseP6Moment
import Candidate.C092.transport.FixedWitnessLabel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open CenteredMomentEnergyState ProbeHighRowFamily ConcretePrimeRowBridge
open HeckePrimeAnnular CenteredMomentCommonMaskEnergy
open Cycle61Moment
open Qrh.TwoSlot.AnchorZeroLoss.High
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6Dictionary_ac1cf025506a175a_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem union_coefficients {Z B bΦ : ℝ} (s : NaturalState Z B bΦ)
    (η η₀ : Character) (hη : s.character=η) (hpuncture : s.puncture=1)
    (u : FreeRow) (F : NaturalRow s.character u.val)
    (label : Option (RayQuotient.Characters M H × RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (family M H hH s η₀ F label) I =
      idealCoeff (naturalRow (witnessBase M H hH η η₀ label) u.val u.property.1).character I := by
  subst η
  let G := fun j : WholeSourceIndex M H => naturalRow
    (Cycle61Moment.wholeSourceBase M H hH η₀ s.character j) u.val u.property.1
  have he (j : WholeSourceIndex M H) := Cycle61Moment.whole_source_family_mask M H hH
    η₀ s.character (excluded F.character s.puncture) u.val u.property.1 F
    s.puncture s.puncture_ne_zero (fun _ => rfl) G j I
  cases label with
  | none => simpa only [family,witnessBase,hpuncture,Cycle61Moment.wholeSourceFamily,
      Sum.elim_inl,Cycle61Moment.wholeSourceBase,G,excluded_one_ideal] using he (.inl ())
  | some pair => simpa only [family,witnessBase,hpuncture,Cycle61Moment.wholeSourceFamily,
      Sum.elim_inr,Cycle61Moment.wholeSourceBase,G,excluded_one_ideal] using he (.inr pair)

theorem original_annular_slot (η η₀ : Character) (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    {Slot : Type} (U : ℝ) (θ : Slot → RayQuotient.Characters M H)
    (wr σ v : Slot → ℝ) (t : FreeRow → ℝ) (u : FreeRow) (slot : Slot)
    (hD : 0 < U^(wr slot))
    (hlarge : ((Record12518109Natural.wholeAnchorMask M H hH η₀).absNorm : ℝ) < U^(wr slot)) :
    coreSlot M H hH η η₀ W U θ wr σ v t u slot =
      naturalSlot (naturalRow η u.val u.property.1).character
        (primePool M H 2 (U^(wr slot)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ slot)) I*
          HeckePrimeAnnular.annularWeight W (U^(wr slot)) (σ slot) (t u+v slot) I) (U^(wr slot)) := by
  unfold coreSlot
  conv_lhs => rw [←Cycle61MarkedPlain.naturalSlot_annular_filter _ _ _ W hs]
  conv_rhs => rw [←Cycle61MarkedPlain.naturalSlot_annular_filter _ _ _ W hs]
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hp := (Finset.mem_filter.mp (Cycle61MarkedPlain.annularPool_subset _ _ hI)).2.1
  have hr := (Cycle61MarkedPlain.annularPool_ratio _ _ _ hI).1
  have hn : U^(wr slot) ≤ (I.absNorm : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hD).mp hr
  have hc := InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hp
    (Record12518109Natural.wholeAnchorMask_ne_zero M H hH η₀) (hlarge.trans_le hn)
  rw [NaturalRow.ideal,NaturalRow.ideal,excluded_ideal _ _
    (Record12518109Natural.wholeAnchorMask_ne_zero M H hH η₀),if_pos hc]

/-- PR67 Cycle63/Marked/NaturalSlotPhase, with its original coefficient and phase normalization. -/
theorem source_naturalSlot_phase (χ : Character) (pool : Finset (Ideal O))
    (β γ : Ideal O→ℂ) (phase : ℂ) (P : ℝ)
    (hcoeff : ∀I∈pool,β I=phase*γ I) :
    naturalSlot χ pool β P=phase*naturalSlot χ pool γ P := by
  unfold naturalSlot
  calc
    _=(Real.sqrt P:ℂ)⁻¹*(phase*∑I∈pool,idealCoeff χ I*γ I) := by
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I hI => ?_
      rw [hcoeff I hI]
      ring
    _=_:=by ring

/-- The unnormalised physical height differs from the normalized annular
height only by a common factor of absolute value one. -/
theorem source_naturalSlot_height_norm (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P σ v t : ℝ) (hP : 0<P)
    (hpool : ∀I∈pool,I≠0) :
    ‖naturalSlot χ pool (heightCoefficient (fun I=>ν I*annularWeight W P σ v I) t) P‖=
      ‖naturalSlot χ pool (fun I=>ν I*annularWeight W P σ (t+v) I) P‖ := by
  rw [source_naturalSlot_phase χ pool _ _ ((P:ℂ)^(Complex.I*t)) P
    (fun I hI=>CenteredMomentEnergySlotHeight.height_coefficient ν W P σ v t hP I (hpool I hI))]
  rw [norm_mul]
  have hp : ‖(P:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hP (Complex.I*t)
  rw [hp,one_mul]

theorem original_slot_norm (η η₀ : Character) (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    {Slot : Type} (U : ℝ) (θ : Slot → RayQuotient.Characters M H)
    (wr σ v : Slot → ℝ) (t : FreeRow → ℝ) (u : FreeRow) (slot : Slot)
    (hD : 0 < U^(wr slot))
    (hlarge : ((Record12518109Natural.wholeAnchorMask M H hH η₀).absNorm : ℝ) < U^(wr slot)) :
    ‖coreSlot M H hH η η₀ W U θ wr σ v t u slot‖ =
      ‖CenteredMomentWholeSlotDeletion.normalizedSlot η fixedBadMask 1 u.val
        (primePool M H 2 (U^(wr slot)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ slot)) I*
          HeckePrimeAnnular.annularWeight W (U^(wr slot)) (σ slot) (v slot) I)
        (t u) (U^(wr slot))‖ := by
  rw [original_annular_slot M H hH η η₀ W hs U θ wr σ v t u slot hD hlarge]
  rw [←CenteredMomentRayMaskedFloor.natural_slot_eq (naturalRow η u.val u.property.1)]
  exact (source_naturalSlot_height_norm _ _ _ W _ _ _ _ hD
    (fun I hI => (Finset.mem_filter.mp hI).2.1.ne_zero)).symm

#print axioms union_coefficients
#print axioms original_annular_slot
#print axioms original_slot_norm
end
end QRH.Cycle092.SourceInverseP6
