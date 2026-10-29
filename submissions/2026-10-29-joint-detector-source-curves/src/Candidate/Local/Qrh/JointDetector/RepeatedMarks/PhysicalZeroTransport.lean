/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint
import Submissions.hailey_collet_1252270103.Cycle61.Moment.PhysicalHighRows

namespace Qrh.JointDetector.RepeatedMarks.PhysicalZeroTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Classical BigOperators ComplexConjugate
open Set OAI OAI.SevenEighths LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical HeckeDetectorZeros
open HeckeDetectorWitnessRows HeckeFiniteDeletion
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT Cycle61Moment
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The live physical maximum maps directly to this anchor's whole source
family. No larger global-anchor dictionary is introduced. -/
theorem physical_row_to_whole_zero (η η₀ : Character) {Z bΦ : ℝ}
    (st : NaturalState Z 0 bΦ) (hchar : st.character=η) (hpuncture : st.puncture=1)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (b T : ℝ) (hb : (51/100:ℝ)<b) (u : NonzeroFrequency) (hk : st.radial.keep u.val)
    (hp : st.radial.profile (‖eisEmbedding u.val‖^2/st.radial.scale)≠0)
    (hmax : b≤Cycle61InitialMass.geometryRowMaximum M H hH st η₀ hQM hQη u.val hk T) :
    rawFrequencyNorm u≤bΦ*Z^st.rowWidth ∧
      naturalActualZeroRow (orientedFixedBase (RootedBatchConcrete.base M H hH η η₀))
        Prod.snd b T u := by
  refine ⟨?_,?_⟩
  · have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2≤bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq,eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow η u.val u.property).character 1) I := by
      intro I
      rw [hpuncture,excluded_ideal _ _ one_ne_zero,excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal,NaturalRow.ideal,hchar]
    exact physical_family_maximum_to_fixed_dictionary
      (RootedBatchConcrete.base M H hH η η₀)
      (Cycle61InitialMass.geometryRowFamily M H hH st η₀ u.val hk) (fun _=>false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal M H hH st η₀ hQM hQη u.val hk)
      (fun idx=>idx) (fun _=>1) u
      (fun idx I=>whole_source_family_mask M H hH η₀ η
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character st.puncture)
        u.val u.property (naturalRow η u.val u.property) 1 one_ne_zero hc0
        (fun idx=>naturalRow (wholeSourceBase M H hH η₀ η idx) u.val u.property) idx I)
      b T hb hmax

theorem natural_zero_to_literal_dictionary_pos {Label : Type*}
    (base : Label → Character) (reverse : Label → Bool) (a T : ℝ) (ha : 0 < a)
    (u : NonzeroElement) (hz : naturalActualZeroRow base reverse a T u) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases base).data reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  let ψ := if reverse j then ((momentData (base j)).character u).inverse else (momentData (base j)).character u
  have hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I := by
    intro I
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false, naturalRawFamily] using natural_raw_coefficients (base j) u I
    · dsimp [χ, ψ]
      simp only [hr, ite_true]
      rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj]
      dsimp only [naturalRawFamily]
      rw [natural_raw_coefficients]
  have hh := positive_zeros_eq_of_coefficients χ ψ hc (ha.trans_le hs) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- A natural-row zero transfers to its FREE core's whole zero maximum.
The core is assumed regular only to exclude the finite principal population;
the root mask is removed by the exact sixth-power Euler-hole identity. -/
theorem regular_natural_zero_to_free_maximum {Label : Type*} [Fintype Label]
    (base : Label → Character) (reverse : Label → Bool) (a T : ℝ) (ha : 51/100 < a)
    (u : NonzeroFrequency)
    (hregular : ¬(FixedUnmarkedDictionary.ofBases base).exceptionalCore (sixthFrequencyEquiv.symm u).1)
    (hz : naturalActualZeroRow base reverse a T u) :
    ∃ hn : ∀ j, (((FixedUnmarkedDictionary.ofBases base).data j).character
      ⟨(sixthFrequencyEquiv.symm u).1.val, (sixthFrequencyEquiv.symm u).1.property.1⟩).residue ≠ 1,
      a ≤ HeckeDetectorZeros.zeroMaximum
        (fun j => ((FixedUnmarkedDictionary.ofBases base).data j).character
          ⟨(sixthFrequencyEquiv.symm u).1.val, (sixthFrequencyEquiv.symm u).1.property.1⟩) hn T := by
  let D := FixedUnmarkedDictionary.ofBases base
  let p := sixthFrequencyEquiv.symm u
  have hn := D.regular_nonprincipal p.1 hregular
  refine ⟨hn, ?_⟩
  obtain ⟨j, s, hz, _hpole, hs, ht⟩ := natural_zero_to_literal_dictionary_pos base reverse a T
    (by linarith) u hz
  have hrawNonprincipal : ((D.data j).character u).residue ≠ 1 := by
    have h := amplified_nonprincipal (D.data j) ⟨p.1.val,p.1.property.1⟩ p.2 (hn j)
    have hu : amplifiedElement ⟨p.1.val,p.1.property.1⟩ p.2 = u := by
      apply Subtype.ext
      exact congrArg Subtype.val (sixthFrequencyEquiv.apply_symm_apply u)
    exact (congrArg (fun z : NonzeroElement => ((D.data j).character z).residue ≠ 1) hu).mp h
  by_cases hj : reverse j = true
  · have hz' : LFunction ((D.data j).character u) (star s) = 0 := by
      change LFunction (if reverse j then ((D.data j).character u).inverse else (D.data j).character u) s = 0 at hz
      rw [ite_eq_left hj, LFunction_inverse_conj _ hrawNonprincipal, map_eq_zero] at hz
      exact hz
    have hcore : LFunction ((D.data j).character ⟨p.1.val,p.1.property.1⟩) (star s) = 0 := by
      apply (sixthFrequency_positive_zeros (D.data j) p (hn j) (by simpa using (show 0 < s.re by linarith))).mp
      simpa only [p, Equiv.apply_symm_apply] using hz'
    have hle := HeckeDetectorZeros.zero_re_le_maximum _ hn T j
      (s := star s) (by simpa using (show 51/100 ≤ s.re by linarith)) (by simpa using ht) hcore
    simpa using hs.trans hle
  · have hz' : LFunction ((D.data j).character u) s = 0 := by
      simpa only [hj, Bool.false_eq_true, ite_false, D] using hz
    have hcore : LFunction ((D.data j).character ⟨p.1.val,p.1.property.1⟩) s = 0 := by
      apply (sixthFrequency_positive_zeros (D.data j) p (hn j) (show 0 < s.re by linarith)).mp
      simpa only [p, Equiv.apply_symm_apply] using hz'
    exact hs.trans (HeckeDetectorZeros.zero_re_le_maximum _ hn T j (by linarith) ht hcore)


/-- Return the FORWARD natural free-core family used by the concrete
source batch. Whole orientation is handled by reflecting zero heights. -/
theorem regular_natural_zero_to_free_natural_maximum {Label : Type*} [Fintype Label]
    (base : Label→Character) (reverse : Label→Bool) (a T : ℝ) (ha : (51/100:ℝ)<a)
    (u : NonzeroFrequency)
    (hregular : ¬(FixedUnmarkedDictionary.ofBases base).exceptionalCore (sixthFrequencyEquiv.symm u).1)
    (hz : naturalActualZeroRow base reverse a T u) :
    ∃ hn : ∀j,(naturalRow (base j) (sixthFrequencyEquiv.symm u).1.val
      (sixthFrequencyEquiv.symm u).1.property.1).character.residue≠1,
      a≤zeroMaximum (fun j=>(naturalRow (base j) (sixthFrequencyEquiv.symm u).1.val
        (sixthFrequencyEquiv.symm u).1.property.1).character) hn T := by
  obtain ⟨hn,hh⟩ := regular_natural_zero_to_free_maximum base reverse a T ha u hregular hz
  let D := FixedUnmarkedDictionary.ofBases base
  let core := (sixthFrequencyEquiv.symm u).1
  have hn' := D.natural_nonprincipal core hn
  refine ⟨hn',?_⟩
  change a≤zeroMaximum (D.naturalFamily core) hn' T
  rw [D.natural_maximum core hn T]
  exact hh

/-- Physical geometry, whole-family calibration, sixth-root removal and
forward source zero maximum, without a global-anchor dictionary mismatch. -/
theorem physical_row_to_free_source_maximum (η η₀ : Character) {Z bΦ : ℝ}
    (st : NaturalState Z 0 bΦ) (hchar : st.character=η) (hpuncture : st.puncture=1)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (b T : ℝ) (hb : (51/100:ℝ)<b) (u : NonzeroFrequency) (hk : st.radial.keep u.val)
    (hp : st.radial.profile (‖eisEmbedding u.val‖^2/st.radial.scale)≠0)
    (hmax : b≤Cycle61InitialMass.geometryRowMaximum M H hH st η₀ hQM hQη u.val hk T)
    (hregular : ¬(FixedUnmarkedDictionary.ofBases
      (orientedFixedBase (RootedBatchConcrete.base M H hH η η₀))).exceptionalCore
        (sixthFrequencyEquiv.symm u).1) :
    rawFrequencyNorm u≤bΦ*Z^st.rowWidth ∧
      ∃ hn : ∀j : WholeSourceIndex M H×Bool,
        (naturalRow (RootedBatchConcrete.base M H hH η η₀ j.1)
          (sixthFrequencyEquiv.symm u).1.val (sixthFrequencyEquiv.symm u).1.property.1).character.residue≠1,
        b≤zeroMaximum (fun j : WholeSourceIndex M H×Bool=>
          (naturalRow (RootedBatchConcrete.base M H hH η η₀ j.1)
            (sixthFrequencyEquiv.symm u).1.val (sixthFrequencyEquiv.symm u).1.property.1).character) hn T := by
  obtain ⟨hnorm,hzero⟩ := physical_row_to_whole_zero M H hH η η₀ st hchar hpuncture hQM hQη
    b T hb u hk hp hmax
  exact ⟨hnorm,regular_natural_zero_to_free_natural_maximum
    (orientedFixedBase (RootedBatchConcrete.base M H hH η η₀)) Prod.snd b T hb u hregular hzero⟩

end
end Qrh.JointDetector.RepeatedMarks.PhysicalZeroTransport

#print axioms Qrh.JointDetector.RepeatedMarks.PhysicalZeroTransport.physical_row_to_free_source_maximum
