/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.FineDetectorCount
import Submissions.arvi_selected_leaf.JointDetector.AdaptivePrice
import Submissions.arvi_selected_leaf.JointDetector.RefinedSupplier
import Submissions.arvi_selected_leaf.JointDetector.FineAdaptiveSupplier.High
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

/-!
# The literal natural-row joint count

The norm inlet in this module is an operator statement about actual selected
free cores and the original normalized prime slots. It is not asserted to be
proved. In particular, the completed finite detector argument does not supply
that operator estimate. Natural sixth roots enter the common slot coefficients;
the detector conductor is always the free-core conductor.
-/
namespace Qrh.JointDetector.FineNaturalCount
open FineDetectorWords FineDetectorCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The actual natural count required by the adaptive price, with the density
floor explicit. The early mesh precedes the finite slots and dictionaries. -/
def WholeJointCountOn (νMin : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 →
    δ ∈ Icc (500001/1000000 : ℝ) (3/4) → 0 ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z) →
    (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(AdaptivePrice.jointRate (2*b-1) δ+loss)

/-- The remaining analytic inlet is a selected OPERATOR estimate, not a count.
It is uniform over every actual selected core subset, every ordinary source
ideal family, and every natural root mask. Histogram/prefix selection must be
used when proving this inlet; no such analytic proof is asserted here.

The source cap is `max(P_requested,3*A)+1`, with `A=Mcap+1`. The lower core
scale and absolute early mesh are fixed before the eventual finite slot type.
-/
def ActualSelectedSlotNorm : Prop :=
  ∀ Mmin Mcap smin loss P_requested : ℝ,
    0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss → 0 ≤ P_requested →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (δ Y : ℝ) (root : HeckeInverseAmplification.NonzeroIdeal) (cores : Finset FreeRow),
    δ ∈ Icc (500001/1000000 : ℝ) (3/4) → Z^(Mmin/20) ≤ Y → Y ≤ bΦ*Z^st.rowWidth →
    (∀ u ∈ cores, rowNorm u ≤ Y ∧
      ∃ hz : st.radial.keep (rowMap (u,root)),
        st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
        Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) →
    SelectedAllSourceNormBound (cores.image Subtype.val) Y δ (C*Z^loss)
      (Z^(detectorAuxiliarySourceCap P_requested (Mcap+1)))

/-- The sixth root remains a common Euler mask in the ORIGINAL slot, for
all its source ideals. Bad-prime terms vanish by the original common mask. -/
theorem normalizedSlot_sixth_root (η : Character) (m A u : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (root : HeckeInverseAmplification.NonzeroIdeal) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t P : ℝ) :
    normalizedSlot η m A (u*(idealGenerator root.val)^6) S β t P =
      normalizedSlot η m A u S
        (fun I => (if IsCoprime I root.val then (1 : ℂ) else 0)*β I) t P := by
  unfold normalizedSlot
  rw [rowSlot_eq_weight, rowSlot_eq_weight]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hm : rowWeight η m A (u*(idealGenerator root.val)^6) t I =
      rowWeight η (m*idealGenerator root.val) A u t I := by
    change (idealCoeff η I*idealRowHom (m^6*(A*(u*(idealGenerator root.val)^6))) I)*
        (Ideal.absNorm I : ℂ)^(Complex.I*t) =
      (idealCoeff η I*idealRowHom ((m*idealGenerator root.val)^6*(A*u)) I)*
        (Ideal.absNorm I : ℂ)^(Complex.I*t)
    congr 3
    ring
  rw [hm, ← CenteredMomentSourceRectangleMask.rowWeight_ideal_mask η m A u t hmLam hm2 root.val I]
  ring

theorem naturalState_mask_divisibility {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) :
    goodLambda ∣ st.mask ∧ (2 : O) ∣ st.mask := by
  constructor
  · exact (dvd_mul_right goodLambda (2 : O)).trans (dvd_mul_right fixedBadMask (idealGenerator st.puncture))
  · exact (dvd_mul_left (2 : O) goodLambda).trans (dvd_mul_right fixedBadMask (idealGenerator st.puncture))

/-- The additional root mask is bounded even at shared core/root primes. -/
theorem sixth_root_mask_norm_le_one (root : HeckeInverseAmplification.NonzeroIdeal) (I : Ideal O) :
    ‖(if IsCoprime I root.val then (1 : ℂ) else 0)‖ ≤ 1 := by
  split_ifs <;> norm_num

/-- The admitted literal HIGH dictionary adapter only needs `b > .51`.
This version exposes that actual hypothesis, so the `.79` auxiliary zero
floor does not inherit an unnecessary `.825` wrapper restriction. -/
theorem physical_row_to_fixed_natural_zero {κ : Type} [Fintype κ]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (anchors : κ → Character) (η₀ : Character)
    {Z bΦ : ℝ} (j : κ) (st : NaturalState Z 0 bΦ)
    (hchar : st.character = anchors j) (hpuncture : st.puncture = 1)
    (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (b T : ℝ) (hb : 51/100 < b) (u : NonzeroFrequency) (hk : st.radial.keep u.val)
    (hp : st.radial.profile (‖eisEmbedding u.val‖^2/st.radial.scale) ≠ 0)
    (hmax : b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη u.val hk T) :
    rawFrequencyNorm u ≤ bΦ*Z^st.rowWidth ∧
      naturalActualZeroRow
        (orientedFixedBase (QRH.SilDensitySplit.Density.highDictionary rayM H hH anchors η₀))
        Prod.snd b T u := by
  refine ⟨?_, ?_⟩
  · have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow (anchors j) u.val u.property).character 1) I := by
      intro I
      rw [hpuncture, excluded_ideal _ _ one_ne_zero, excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal, NaturalRow.ideal, hchar]
    exact physical_family_maximum_to_fixed_dictionary
      (QRH.SilDensitySplit.Density.highDictionary rayM H hH anchors η₀)
      (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ u.val hk) (fun _ => false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk)
      (fun idx => (j,idx)) (fun _ => 1) u
      (fun idx I => whole_source_family_mask rayM H hH η₀ (anchors j)
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character st.puncture)
        u.val u.property (naturalRow (anchors j) u.val u.property) 1 one_ne_zero hc0
        (fun idx => naturalRow (wholeSourceBase rayM H hH η₀ (anchors j) idx) u.val u.property) idx I)
      b T hb hmax

/-- Positive-half-plane coefficient transport to the actual literal moment
dictionary. Only positive `a` is needed; orientations are of whole characters.
-/
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

theorem raw_sixth_remainder (u : NonzeroFrequency) :
    CenteredExceptionalCount.sixthRemainder (Ideal.span {u.val}) =
      Ideal.span {(sixthFrequencyEquiv.symm u).1.val} := by
  let p := sixthFrequencyEquiv.symm u
  let I : Ideal O := Ideal.span {u.val}
  have hI : I ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr u.property
  have hA : (Ideal.span {p.1.val} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr p.1.property.1
  have he : I = Ideal.span {p.1.val}*p.2.val^6 := by
    have h := rowMap_span p
    change Ideal.span {(sixthFrequencyEquiv p).val} = _ at h
    rw [sixthFrequencyEquiv.apply_symm_apply u] at h
    exact h
  have hu := CenteredExceptionalCount.sixth_normal_form_unique hA p.2.property
    (CenteredExceptionalCount.sixthRemainder_ne_zero I)
    (CenteredExceptionalCount.sixthQuotient_ne_zero I)
    p.1.property.2 (fun P => CenteredExceptionalCount.sixthRemainder_valuation_lt I P)
    (he.symm.trans (CenteredExceptionalCount.sixth_normal_form I hI).symm)
  exact hu.1.symm

private theorem finite_core_ideal_population (coreIdeals : Finset (Ideal O))
    (hcores : ∀ I ∈ coreIdeals, I ≠ 0) (E : Finset O) (B : ℝ) (hB : 1 ≤ B)
    (hnonzero : ∀ z ∈ E, z ≠ 0)
    (hnorm : ∀ z ∈ E, ((Ideal.span {z}).absNorm : ℝ) ≤ B)
    (hcore : ∀ z ∈ E, CenteredExceptionalCount.sixthRemainder (Ideal.span {z}) ∈ coreIdeals) :
    (E.card : ℝ) ≤ 768*(coreIdeals.card : ℝ)*B^(1/6 : ℝ) := by
  let core (z : O) := CenteredExceptionalCount.sixthRemainder (Ideal.span {z})
  have hchild (I : Ideal O) (hI : I ∈ coreIdeals) :
      ((E.filter fun z => core z = I).card : ℝ) ≤ 768*B^(1/6 : ℝ) := by
    have hnI : 1 ≤ (I.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hcores I hI))
    have h := CenteredExceptionalCount.element_count_fixed_remainder
      (E.filter fun z => core z = I) I (hcores I hI) B (by linarith)
      (fun z hz => hnonzero z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hnorm z (Finset.mem_filter.mp hz).1)
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ (by linarith : 0 < (I.absNorm : ℝ))).2
        (by nlinarith)) (by norm_num : (0 : ℝ) ≤ 1/6)) (by norm_num))
  have hcard : (E.card : ℝ) = ∑ I ∈ coreIdeals, ((E.filter fun z => core z = I).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := coreIdeals) (f := core)
      (fun z hz => hcore z hz)
    exact_mod_cast h
  calc
    _ = ∑ I ∈ coreIdeals, ((E.filter fun z => core z = I).card : ℝ) := hcard
    _ ≤ ∑ _I ∈ coreIdeals, 768*B^(1/6 : ℝ) := Finset.sum_le_sum fun I hI => hchild I hI
    _ = _ := by simp; ring

/-- The finite principal/initially-exceptional FREE cores have infinitely
many natural lifts; this proves their whole `B^(1/6)` complementary count.
-/
theorem principal_exceptional_raw_count {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) : ∃ C : ℝ, 0 < C ∧
      ∀ B : ℝ, 1 ≤ B → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ B ∧ D.exceptionalCore (sixthFrequencyEquiv.symm u).1) →
      (rows.card : ℝ) ≤ C*B^(1/6 : ℝ) := by
  have hf : {u : FreeRow | D.exceptionalCore u}.Finite := D.exceptional_cores_finite
  let coreIdeals := hf.toFinset.image (fun u => (Ideal.span {u.val} : Ideal O))
  let C := 768*(coreIdeals.card : ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B hB rows hrows
  let E := rows.image Subtype.val
  have hcard : E.card = rows.card := Finset.card_image_of_injective rows Subtype.val_injective
  have hE := finite_core_ideal_population coreIdeals
    (by intro I hI; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
        exact Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    E B hB
    (by intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz; exact u.property)
    (by intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz; exact (hrows u hu).1)
    (by intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        rw [raw_sixth_remainder]
        exact Finset.mem_image.mpr ⟨(sixthFrequencyEquiv.symm u).1,
          hf.mem_toFinset.mpr (hrows u hu).2, rfl⟩)
  rw [hcard] at hE
  exact hE.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (Real.rpow_nonneg (zero_le_one.trans hB) _))

/-- Below the old `.65` wrapper floor the selected joint/SC count is already
stronger than the inherited zero-density rate. This statement concerns the
selected amplitude range; it does not count low-amplitude rows. -/
theorem jointRate_eq_detectorRate_lower_band {ν δ : ℝ}
    (hν : ν ∈ Icc (29/50 : ℝ) (13/20)) (hδ : δ ∈ Icc (500001/1000000 : ℝ) (3/4)) :
    AdaptivePrice.jointRate ν δ = detectorRate ν δ := by
  have hνwide : ν ∈ Icc (29/50 : ℝ) (3/4) := ⟨hν.1, by linarith [hν.2]⟩
  have hk := AdaptivePrice.k_le_nu hνwide
  unfold AdaptivePrice.jointRate detectorRate
  split_ifs with hd
  · apply min_eq_right
    have he : jointCountExponent ν δ ≤ jointCountExponent ν (1/2) := by
      have heq := count_delta_difference (show (1/2 : ℝ) ≤ ν by linarith [hν.1]) hd hνwide.2
      have hδhalf : 0 ≤ δ-1/2 := by linarith [hδ.1]
      have hp : 0 ≤ 3*(1-ν)^2*(δ-1/2)/((3-ν-2*(1/2))*(3-ν-2*δ)) := by
        have hd1 := count_den_pos (show (1/2 : ℝ) ≤ ν by linarith [hν.1]) hνwide.2
        have hd2 := count_den_pos hd hνwide.2
        positivity
      linarith
    have hd1 : 0 < 2-ν := by linarith [hν.2]
    have hd2 := AdaptivePrice.k_den_pos hνwide
    have hpoly : 0 ≤ 7*ν^2-(31/2)*ν+15/2 := by
      have h := mul_nonneg (show 0 ≤ 13/20-ν by linarith [hν.2])
        (show 0 ≤ 31/2-7*(ν+13/20) by linarith [hν.2])
      nlinarith
    have hhalf : jointCountExponent ν (1/2) ≤ 1-AdaptivePrice.k ν := by
      have hehalf : jointCountExponent ν (1/2) = ((3/2)*(1-ν))/(2-ν) := by
        rw [jointCountExponent_eq]
        ring
      have hrho : 1-AdaptivePrice.k ν = (15-16*ν)/(15-6*ν) := by
        unfold AdaptivePrice.k
        apply (eq_div_iff hd2.ne').2
        rw [sub_mul, div_mul_cancel₀ _ hd2.ne']
        ring
      rw [hehalf, hrho]
      apply (div_le_div_iff₀ hd1 hd2).2
      nlinarith
    exact he.trans hhalf
  · exact (min_eq_right (by linarith : 1-δ ≤ 1-AdaptivePrice.k ν))

def freeCharacter (η : Character) (z : O) : Character :=
  if hz : z ≠ 0 then (naturalRow η z hz).character else η

def naturalCommonCoefficient (η : Character) (I : Ideal O) : ℂ :=
  idealCoeff η I*idealRowHom (fixedBadMask^6) I

theorem naturalCommonCoefficient_norm_le_one (η : Character) (I : Ideal O) :
    ‖naturalCommonCoefficient η I‖ ≤ 1 := by
  unfold naturalCommonCoefficient
  rw [norm_mul]
  exact (mul_le_mul (idealCoeff_norm_le_one η I) (idealRowHom_norm _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem freeCharacter_coefficients (η : Character) (z : O) (hz : z ≠ 0) (I : Ideal O) :
    idealCoeff (freeCharacter η z) I = naturalCommonCoefficient η I*idealRowHom z I := by
  rw [freeCharacter, dite_eq_left hz, NaturalRow.ideal, idealRowHom_argument_mul]
  unfold naturalCommonCoefficient
  ring

theorem freeCharacter_at_core (η : Character) (u : FreeRow) :
    freeCharacter η u.val = (naturalRow η u.val u.property.1).character := by
  rw [freeCharacter, dite_eq_left u.property.1]

theorem selectedNormBound_mono_anchor {E : Finset O} {Y U δ K Xmax : ℝ}
    (h : SelectedAllSourceNormBound E Y δ K Xmax) (hY : 0 ≤ Y) (hYU : Y ≤ U) (hδ : δ ≤ 1) :
    SelectedAllSourceNormBound E U δ K Xmax := by
  refine ⟨h.1, ?_⟩
  intro X S hX hXmax hnorm
  have hp : Y^(1-δ) ≤ U^(1-δ) := Real.rpow_le_rpow hY hYU (by linarith)
  have hm : Y^(1-δ)*X^δ ≤ U^(1-δ)*X^δ :=
    mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by linarith : 0 ≤ X) δ)
  exact (h.2 X S hX hXmax hnorm).trans
    (mul_le_mul_of_nonneg_left (show X+Y^(1-δ)*X^δ ≤ X+U^(1-δ)*X^δ by linarith) h.1)

/-- The regular selected FREE core count on one ambient scale. The natural
zero event includes the original root, while the detector dictionary and
its conductor do not. The only analytic input is the stated selected norm.
-/
theorem regular_core_count_on_scale (dmin dmax τ ε e κ η : ℝ) (n : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*η)
    (hε : 0 < ε) (hεsmall : ε ≤ 1/1000) (he : 0 < e) (he' : e < 1/1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η ≤ ε/2)
    (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ (n : ℝ)*e) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    1 < Z^d → 2 < Z^τ →
    ∀ {Label : Type} [Fintype Label] (base : Label → Character) (reverse : Label → Bool)
      (root : HeckeInverseAmplification.NonzeroIdeal) (F : Finset FreeRow)
      (Y Cdict b δ K Xmax T height : ℝ),
    1 ≤ Y → 1 ≤ Cdict → Cdict*Y ≤ Z^d →
    (∀ u : FreeRow, ∀ j, (((FixedUnmarkedDictionary.ofBases base).naturalFamily u j).modulus.absNorm : ℝ) ≤
      Cdict*rowNorm u) →
    b ∈ Icc ((3/4 : ℝ)+e) (7/8) → δ ∈ Icc (500001/1000000 : ℝ) (3/4) → T ≤ Z^τ →
    (∀ u ∈ F, rowNorm u ≤ Y ∧
      ¬(FixedUnmarkedDictionary.ofBases base).exceptionalCore u ∧
      naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (u,root))) →
    SelectedAllSourceNormBound (F.image Subtype.val) Y δ K Xmax → 6*(Z^d)^(3 : ℝ) ≤ Xmax →
    0 ≤ height → 2*Real.pi*(Z^d)^(τ/(2*dmax))+(3*n : ℕ)*Z^τ ≤ height →
    (F.card : ℝ) ≤ C*max 1 (((n+1 : ℕ) : ℝ)*(detectorZeroBinCount e : ℝ)*
      (Fintype.card Label : ℝ)*(dyadicLength (Z^d) : ℝ)^2*(1+height))*K*
      (Z^d)^(detectorRate (2*b-1) δ+83*ε+2*e) := by
  obtain ⟨C, Z₀, hC, hcount⟩ := whole_core_zero_count dmin dmax τ ε e κ η n
    hdmin hdmax hτ hτzero hτheight hε hεsmall he he' hκ hκ' hη hbudget hn hwidth
  refine ⟨C, Z₀, hC, ?_⟩
  intro Z hZ d hd hd' hU hZτ Label _ base reverse root F Y Cdict b δ K Xmax T height
    hY hCdict hUY hconductor hb hδ hT hF hnorm hcap hh hfreq
  let D := FixedUnmarkedDictionary.ofBases base
  let E := F.image Subtype.val
  let χ : O → Label → Character := fun z j => freeCharacter (base j) z
  have hcard : E.card = F.card := Finset.card_image_of_injective F Subtype.val_injective
  have hcore (z : E) : ∃ u ∈ F, u.val = z.val := Finset.mem_image.mp z.property
  have hχ (z : E) : ∀ j, (χ z.val j).residue ≠ 1 := by
    obtain ⟨u, hu, heq⟩ := hcore z
    have hregular := (hF u hu).2.1
    have h := D.natural_nonprincipal u (D.regular_nonprincipal u hregular)
    intro j
    change (freeCharacter (base j) z.val).residue ≠ 1
    have he : freeCharacter (base j) z.val = D.naturalFamily u j := by
      rw [← heq, freeCharacter_at_core]
      rfl
    exact (congrArg (fun ξ : Character => ξ.residue ≠ 1) he).mpr (h j)
  have hzero (z : E) : b ≤ HeckeDetectorZeros.zeroMaximum (χ z.val) (hχ z) (Z^τ) := by
    obtain ⟨u, hu, heq⟩ := hcore z
    have hr : (sixthFrequencyEquiv.symm (sixthFrequencyEquiv (u,root))).1 = u := by simp
    obtain ⟨hnp, hm⟩ := regular_natural_zero_to_free_maximum base reverse b T
      (by linarith [hb.1]) (sixthFrequencyEquiv (u,root))
      (by simpa only [Equiv.symm_apply_apply] using (hF u hu).2.1) (hF u hu).2.2
    simp only [Equiv.symm_apply_apply] at hnp hm
    have hn := D.regular_nonprincipal u (hF u hu).2.1
    have hnat : b ≤ HeckeDetectorZeros.zeroMaximum (D.naturalFamily u) (D.natural_nonprincipal u hn) T := by
      rw [D.natural_maximum u hn T]
      exact hm
    have he : χ z.val = D.naturalFamily u := by
      funext j
      dsimp [χ]
      rw [← heq, freeCharacter_at_core]
      rfl
    have hnat' : b ≤ HeckeDetectorZeros.zeroMaximum (χ z.val) (hχ z) T := by
      simpa only [he] using hnat
    exact hnat'.trans (HeckeDetectorZeros.zeroMaximum_mono (χ z.val) (hχ z) hT)
  have hcond (z : E) (j : Label) : ((χ z.val j).modulus.absNorm : ℝ) ≤ Z^d := by
    obtain ⟨u, hu, heq⟩ := hcore z
    have he : χ z.val j = D.naturalFamily u j := by
      dsimp [χ]
      rw [← heq, freeCharacter_at_core]
      rfl
    rw [he]
    exact (hconductor u j).trans ((mul_le_mul_of_nonneg_left (hF u hu).1 (by linarith)).trans hUY)
  have hnorm' : SelectedAllSourceNormBound E (Z^d) δ K Xmax :=
    selectedNormBound_mono_anchor hnorm (by linarith)
      ((show Y ≤ Cdict*Y by nlinarith).trans hUY) (by linarith [hδ.2])
  have h := hcount Z hZ d hd hd' hU hZτ E χ (fun _ => ()) hχ
    (fun (_ : Unit) j => naturalCommonCoefficient (base j))
    (by intro z hz j I; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        exact freeCharacter_coefficients (base j) u.val u.property.1 I)
    (fun _ j I => naturalCommonCoefficient_norm_le_one (base j) I)
    b δ K Xmax height hb hδ hzero hcond hnorm' hcap hh hfreq
  simpa only [hcard, Fintype.card_unit, Nat.cast_one, mul_one] using h

/-- All losses here are fixed before the finite slots and dictionaries.
`normLoss` is an ambient `Z` loss; the lower core scale converts it to a
natural-core loss. No analytic assertion is a field of this structure. -/
structure EarlyCountBudget (dmin loss : ℝ) where
  eps : ℝ
  buffer : ℝ
  normLoss : ℝ
  logLoss : ℝ
  tau : ℝ
  bins : ℕ
  eps_pos : 0 < eps
  eps_cap : eps ≤ 1/1000
  buffer_pos : 0 < buffer
  buffer_cap : buffer < 1/1000
  buffer_one : buffer ≤ 1
  normLoss_pos : 0 < normLoss
  logLoss_pos : 0 < logLoss
  tau_pos : 0 < tau
  tau_zero : tau < dmin/2
  tau_height : 4*tau < dmin*buffer
  detector_budget : 298*buffer ≤ eps/2
  bins_pos : 0 < bins
  bins_width : (49/100 : ℝ) ≤ (bins : ℝ)*buffer
  total_loss : 83*eps+2*buffer+logLoss+(tau+normLoss)/dmin ≤ loss
  constant_loss_cap : 83*eps+2*buffer+logLoss ≤ 1

theorem exists_early_count_budget (dmin loss : ℝ) (hdmin : 0 < dmin) (hloss : 0 < loss) :
    Nonempty (EarlyCountBudget dmin loss) := by
  let p := min loss 1
  have hp : 0 < p := lt_min hloss (by norm_num)
  have hp1 : p ≤ 1 := min_le_right _ _
  have hploss : p ≤ loss := min_le_left _ _
  let eps := p/1000
  let buffer := eps/2000
  let normLoss := dmin*p/1000
  let logLoss := p/1000
  let tau := min (dmin*buffer/8) (dmin*p/1000)
  let bins := ⌈(49/100 : ℝ)/buffer⌉₊+1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heb : 0 < buffer := by dsimp [buffer]; positivity
  have hebcap : buffer < 1/1000 := by dsimp [buffer, eps]; nlinarith
  have htau : 0 < tau := lt_min (by positivity) (by positivity)
  have htau1 : tau ≤ dmin*buffer/8 := min_le_left _ _
  have htau2 : tau ≤ dmin*p/1000 := min_le_right _ _
  have hconvert : (tau+normLoss)/dmin ≤ p/500 := (div_le_iff₀ hdmin).2 (by
    dsimp [normLoss]
    nlinarith)
  have hwidth : (49/100 : ℝ) ≤ (bins : ℝ)*buffer := by
    have h := (div_le_iff₀ heb).mp (Nat.le_ceil ((49/100 : ℝ)/buffer))
    dsimp [bins]
    push_cast
    nlinarith
  refine ⟨{
    eps := eps
    buffer := buffer
    normLoss := normLoss
    logLoss := logLoss
    tau := tau
    bins := bins
    eps_pos := heps
    eps_cap := ?_
    buffer_pos := heb
    buffer_cap := hebcap
    buffer_one := by linarith
    normLoss_pos := by dsimp [normLoss]; positivity
    logLoss_pos := by dsimp [logLoss]; positivity
    tau_pos := htau
    tau_zero := ?_
    tau_height := ?_
    detector_budget := ?_
    bins_pos := by dsimp [bins]; omega
    bins_width := hwidth
    total_loss := ?_
    constant_loss_cap := ?_ }⟩
  · dsimp [eps]
    linarith
  · have hb1 : buffer ≤ 1 := by linarith
    have h := mul_le_mul_of_nonneg_left hb1 hdmin.le
    nlinarith
  · nlinarith
  · dsimp [buffer]
    linarith
  · dsimp [eps, buffer, logLoss] at *
    linarith
  · dsimp [eps, buffer, logLoss]
    nlinarith

theorem detectorRate_bounds {ν δ : ℝ} (hν : ν ≤ 3/4)
    (hδ : δ ∈ Icc (500001/1000000 : ℝ) (3/4)) :
    (1/4 : ℝ) ≤ detectorRate ν δ ∧ detectorRate ν δ ≤ 1/2 := by
  unfold detectorRate
  split_ifs with hd
  · have hlo := quarter_le_count_exponent hd hν
    have hhi : jointCountExponent ν δ ≤ 1-δ := by
      rw [jointCountExponent_eq]
      apply (div_le_iff₀ (count_den_pos hd hν)).2
      have h := mul_nonneg (show 0 ≤ 1-δ by linarith [hδ.2]) (sub_nonneg.mpr hd)
      nlinarith
    exact ⟨hlo, by linarith [hδ.1]⟩
  · constructor <;> linarith [hδ.1, hδ.2]

/-- Scalar absorption of the actual finite class, Sobolev, norm and logarithmic
costs. Every bound here is a displayed scalar estimate; no count is assumed.
-/
theorem regular_count_scalar_absorption
    (dmin loss : ℝ) (budget : EarlyCountBudget dmin loss) (hdmin : 0 < dmin)
    (Z Y Cdict U C₀ A D height Clog CH Knorm R : ℝ)
    (hZ : 1 ≤ Z) (hY : 1 ≤ Y) (hZY : Z^dmin ≤ Y) (hCdict : 1 ≤ Cdict)
    (hU : U = Cdict*Y) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hh : 0 ≤ height) (hClog : 0 ≤ Clog) (hCH : 0 ≤ CH) (hKnorm : 0 ≤ Knorm)
    (hDlog : D ≤ Clog*U^budget.logLoss)
    (hheight : 1+height ≤ CH*Z^budget.tau) (hR : R ∈ Icc (0 : ℝ) (1/2)) :
    C₀*max 1 (A*D*(1+height))*(Knorm*Z^budget.normLoss)*U^(R+83*budget.eps+2*budget.buffer) ≤
      (C₀*(1+A)*Clog*CH*Knorm*Cdict^2)*Y^(R+loss) := by
  let g := R+83*budget.eps+2*budget.buffer
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hUp : 0 < U := by rw [hU]; positivity
  have hτpos := budget.tau_pos
  have hnormLossPos := budget.normLoss_pos
  have hcost : max 1 (A*D*(1+height)) ≤ (1+A)*D*(1+height) := by
    have hp : 1 ≤ D*(1+height) := one_le_mul_of_one_le_of_one_le hD (by linarith)
    apply max_le <;> nlinarith
  have hZcost : Z^(budget.tau+budget.normLoss) ≤ Y^((budget.tau+budget.normLoss)/dmin) := by
    have heq : Z^(budget.tau+budget.normLoss) =
        (Z^dmin)^((budget.tau+budget.normLoss)/dmin) := by
      rw [← Real.rpow_mul hZp.le]
      congr 1
      field_simp
    rw [heq]
    exact Real.rpow_le_rpow (by positivity) hZY (by positivity)
  have hUcost : U^(g+budget.logLoss) ≤ Cdict^2*Y^(g+budget.logLoss) := by
    rw [hU, Real.mul_rpow (by linarith) hYp.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hcap : g+budget.logLoss ≤ 2 := by dsimp [g]; linarith [budget.constant_loss_cap, hR.2]
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hCdict hcap
  have hE : g+budget.logLoss+(budget.tau+budget.normLoss)/dmin ≤ R+loss := by
    dsimp [g]
    linarith [budget.total_loss]
  calc
    _ ≤ C₀*((1+A)*(Clog*U^budget.logLoss)*(CH*Z^budget.tau))*(Knorm*Z^budget.normLoss)*U^g := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC₀
      exact hcost.trans (by
        have hmul := mul_le_mul hDlog hheight (by linarith : 0 ≤ 1+height) (by positivity)
        nlinarith)
    _ = (C₀*(1+A)*Clog*CH*Knorm)*Z^(budget.tau+budget.normLoss)*U^(g+budget.logLoss) := by
      rw [Real.rpow_add hZp budget.tau budget.normLoss,
        Real.rpow_add hUp g budget.logLoss]
      ring
    _ ≤ (C₀*(1+A)*Clog*CH*Knorm)*Y^((budget.tau+budget.normLoss)/dmin)*
        (Cdict^2*Y^(g+budget.logLoss)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hZcost (by positivity)
      · exact hUcost
      · positivity
      · positivity
    _ = (C₀*(1+A)*Clog*CH*Knorm*Cdict^2)*Y^(g+budget.logLoss+(budget.tau+budget.normLoss)/dmin) := by
      rw [Real.rpow_add hYp (g+budget.logLoss) ((budget.tau+budget.normLoss)/dmin)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY hE) (by positivity)

def countHeight {dmin loss : ℝ} (budget : EarlyCountBudget dmin loss) (A Z U : ℝ) : ℝ :=
  2*Real.pi*U^(budget.tau/(2*A))+(3*budget.bins : ℕ)*Z^budget.tau

def countHeightConstant {dmin loss : ℝ} (budget : EarlyCountBudget dmin loss) : ℝ :=
  1+2*Real.pi+(3*budget.bins : ℕ)

/-- A uniform polynomial scale adapter. Its fields are scalar bounds only. -/
structure CoreScaleData (dmin A Cdict Z Y Clog : ℝ) {loss : ℝ}
    (budget : EarlyCountBudget dmin loss) where
  d : ℝ
  lower : dmin ≤ d
  upper : d ≤ A
  scale : Z^d = Cdict*Y
  scale_gt_one : 1 < Z^d
  aux_gt_two : 2 < Z^budget.tau
  Y_ge_one : 1 ≤ Y
  source_cap : 6*(Z^d)^(3 : ℝ) ≤ Z^(3*A+1)
  log_bound : (dyadicLength (Z^d) : ℝ)^2 ≤ Clog*(Z^d)^budget.logLoss
  height_nonneg : 0 ≤ countHeight budget A Z (Z^d)
  height_bound : 1+countHeight budget A Z (Z^d) ≤ countHeightConstant budget*Z^budget.tau

/-- The common threshold is uniform over ALL live core scales. It is chosen
after the fixed dictionary constant, before the selected rows and heights. -/
theorem uniform_core_scale_data (dmin Mcap loss Cdict bΦ : ℝ)
    (budget : EarlyCountBudget dmin loss) (hdmin : 0 < dmin) (hMcap : 0 < Mcap)
    (hCdict : 1 ≤ Cdict) (hbΦ : 1 ≤ bΦ) :
    ∃ Clog : ℝ, 1 ≤ Clog ∧ ∀ᶠ Z : ℝ in atTop, 6 ≤ Z ∧
      ∀ Y : ℝ, Z^dmin ≤ Y → Y ≤ bΦ*Z^Mcap →
      Nonempty (CoreScaleData dmin (Mcap+1) Cdict Z Y Clog budget) := by
  obtain ⟨Klog, hKlog, hevent⟩ := HeckeDetectorClassBudget.dyadic_cost_eventually
    budget.logLoss budget.logLoss_pos
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hevent
  let Clog := Klog+1
  have hClog : 1 ≤ Clog := by dsimp [Clog]; linarith
  have hlarge : ∀ᶠ Z : ℝ in atTop, max U₀ 2 ≤ Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop (max U₀ 2))
  have haux : ∀ᶠ Z : ℝ in atTop, 2 < Z^budget.tau :=
    (tendsto_rpow_atTop budget.tau_pos).eventually (eventually_gt_atTop (2 : ℝ))
  refine ⟨Clog, hClog, ?_⟩
  filter_upwards [hlarge, haux, eventually_ge_atTop (max 6 (Cdict*bΦ))] with Z hlarge haux hZ
  have hZ6 : 6 ≤ Z := (le_max_left _ _).trans hZ
  have hZdict : Cdict*bΦ ≤ Z := (le_max_right _ _).trans hZ
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 < Z := by linarith
  refine ⟨hZ6, ?_⟩
  intro Y hYlower hYupper
  let U := Cdict*Y
  have hY2 : 2 ≤ Y := (le_max_right U₀ 2).trans (hlarge.trans hYlower)
  have hYp : 0 < Y := by linarith
  have hYU : Y ≤ U := by dsimp [U]; nlinarith
  have hUp : 0 < U := hYp.trans_le hYU
  have hU0 : U₀ ≤ U := (le_max_left U₀ 2).trans (hlarge.trans (hYlower.trans hYU))
  have hUupper : U ≤ Z^(Mcap+1) := by
    calc
      _ ≤ Cdict*(bΦ*Z^Mcap) := mul_le_mul_of_nonneg_left hYupper (by linarith)
      _ ≤ Z*Z^Mcap := by nlinarith [mul_le_mul_of_nonneg_right hZdict (Real.rpow_nonneg hZp.le Mcap)]
      _ = _ := by rw [Real.rpow_add hZp, Real.rpow_one]; ring
  let d := Real.logb Z U
  have hscale : Z^d = U := Real.rpow_logb hZp hZ1.ne' hUp
  have hdlow : dmin ≤ d := (Real.le_logb_iff_rpow_le hZ1 hUp).2 (hYlower.trans hYU)
  have hdhigh : d ≤ Mcap+1 := (Real.logb_le_iff_le_rpow hZ1 hUp).2 hUupper
  have hU3 : U^(3 : ℝ) ≤ Z^(3*(Mcap+1)) := by
    calc
      _ ≤ (Z^(Mcap+1))^(3 : ℝ) := Real.rpow_le_rpow hUp.le hUupper (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hZp.le]; congr 1; ring
  have hcap : 6*U^(3 : ℝ) ≤ Z^(3*(Mcap+1)+1) := by
    calc
      _ ≤ Z*Z^(3*(Mcap+1)) := mul_le_mul hZ6 hU3 (by positivity) (by linarith)
      _ = _ := by rw [Real.rpow_add hZp, Real.rpow_one]; ring
  have hlog : (dyadicLength U : ℝ)^2 ≤ Clog*U^budget.logLoss :=
    (hU₀ U hU0).trans (mul_le_mul_of_nonneg_right (by dsimp [Clog]; linarith) (by positivity))
  have hA : 0 < Mcap+1 := by linarith
  have htauPos := budget.tau_pos
  have hpower : U^(budget.tau/(2*(Mcap+1))) ≤ Z^budget.tau := by
    calc
      _ ≤ (Z^(Mcap+1))^(budget.tau/(2*(Mcap+1))) :=
        Real.rpow_le_rpow hUp.le hUupper (by positivity)
      _ = Z^(budget.tau/2) := by
        rw [← Real.rpow_mul hZp.le]
        congr 1
        field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith [budget.tau_pos])
  have hZtau : 1 ≤ Z^budget.tau := Real.one_le_rpow hZ1.le budget.tau_pos.le
  have hh : 0 ≤ countHeight budget (Mcap+1) Z U := by unfold countHeight; positivity
  have hheight : 1+countHeight budget (Mcap+1) Z U ≤ countHeightConstant budget*Z^budget.tau := by
    unfold countHeight countHeightConstant
    nlinarith [Real.pi_pos]
  exact ⟨{
    d := d
    lower := hdlow
    upper := hdhigh
    scale := hscale
    scale_gt_one := by rw [hscale]; linarith
    aux_gt_two := haux
    Y_ge_one := by linarith
    source_cap := by rw [hscale]; exact hcap
    log_bound := by rw [hscale]; exact hlog
    height_nonneg := by rw [hscale]; exact hh
    height_bound := by rw [hscale]; exact hheight }⟩

/-- Uniform all-height regular-core count from the actual selected operator
inlet. The fixed dictionary may have arbitrary finite size, but its degree and
constant are chosen before every live height and root. -/
theorem regular_core_count_eventually (dmin Mcap loss Cdict bΦ Knorm : ℝ)
    (budget : EarlyCountBudget dmin loss) (hdmin : 0 < dmin) (hdminCap : dmin ≤ Mcap)
    (hMcap : 0 < Mcap) (hCdict : 1 ≤ Cdict) (hbΦ : 1 ≤ bΦ) (hKnorm : 0 < Knorm)
    {Label : Type} [Fintype Label] (base : Label → Character) (reverse : Label → Bool)
    (hconductor : ∀ u : FreeRow, ∀ j,
      (((FixedUnmarkedDictionary.ofBases base).naturalFamily u j).modulus.absNorm : ℝ) ≤ Cdict*rowNorm u) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (Y b δ T : ℝ) (root : HeckeInverseAmplification.NonzeroIdeal) (F : Finset FreeRow),
      Z^dmin ≤ Y → Y ≤ bΦ*Z^Mcap → b ∈ Icc ((3/4 : ℝ)+budget.buffer) (7/8) →
      δ ∈ Icc (500001/1000000 : ℝ) (3/4) → 0 ≤ T →
      (∀ u ∈ F, rowNorm u ≤ Y ∧
        ¬(FixedUnmarkedDictionary.ofBases base).exceptionalCore u ∧
        naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (u,root))) →
      SelectedAllSourceNormBound (F.image Subtype.val) Y δ (Knorm*Z^budget.normLoss)
        (Z^(3*(Mcap+1)+1)) →
      (F.card : ℝ) ≤ C*(1+T)^J*Y^(detectorRate (2*b-1) δ+loss) := by
  obtain ⟨C₀, Z₀, hC₀, hcore⟩ := regular_core_count_on_scale
    dmin (Mcap+1) budget.tau budget.eps budget.buffer budget.buffer budget.buffer budget.bins
    hdmin (by linarith) budget.tau_pos budget.tau_zero budget.tau_height
    budget.eps_pos budget.eps_cap budget.buffer_pos budget.buffer_cap
    budget.buffer_pos budget.buffer_one budget.buffer_pos.le
    (by linarith [budget.detector_budget]) budget.bins_pos budget.bins_width
  obtain ⟨Clog, hClog, hscales⟩ := uniform_core_scale_data dmin Mcap loss Cdict bΦ budget
    hdmin hMcap hCdict hbΦ
  obtain ⟨J, hlarge⟩ := exists_large_height_count_degree (Mcap+1) budget.tau budget.tau_pos
  let A := ((budget.bins+1 : ℕ) : ℝ)*(detectorZeroBinCount budget.buffer : ℝ)*(Fintype.card Label : ℝ)
  let Csmall := C₀*(1+A)*Clog*(countHeightConstant budget)*Knorm*Cdict^2
  let C := Csmall+769
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCH : 0 < countHeightConstant budget := by
    unfold countHeightConstant
    positivity
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨J, C, hC, ?_⟩
  filter_upwards [hscales, eventually_ge_atTop Z₀] with Z hscale hZ₀
  have hZ6 := hscale.1
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 < Z := by linarith
  refine ⟨hZ1, ?_⟩
  intro Y b δ T root F hYlower hYupper hb hδ hT hF hnorm
  obtain ⟨data⟩ := hscale.2 Y hYlower hYupper
  have hY1 := data.Y_ge_one
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hrate := detectorRate_bounds (by linarith [hb.2] : 2*b-1 ≤ 3/4) hδ
  have hloss : 0 ≤ loss := by
    have hp : 0 ≤ 83*budget.eps+2*budget.buffer+budget.logLoss+
      (budget.tau+budget.normLoss)/dmin := by
      have h1 := budget.eps_pos
      have h2 := budget.buffer_pos
      have h3 := budget.logLoss_pos
      have h4 := budget.tau_pos
      have h5 := budget.normLoss_pos
      positivity
    exact hp.trans budget.total_loss
  have hYpow : 1 ≤ Y^(detectorRate (2*b-1) δ+loss) :=
    Real.one_le_rpow hY1 (by linarith [hrate.1])
  have hheight1 : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
  by_cases hlow : T ≤ Z^budget.tau
  · have hcount := hcore Z hZ₀ data.d data.lower data.upper data.scale_gt_one data.aux_gt_two
      base reverse root F Y Cdict b δ (Knorm*Z^budget.normLoss) (Z^(3*(Mcap+1)+1)) T
      (countHeight budget (Mcap+1) Z (Z^data.d))
      hY1 hCdict data.scale.ge hconductor hb hδ hlow hF hnorm data.source_cap
      data.height_nonneg (by rfl)
    have hbound := regular_count_scalar_absorption dmin loss budget hdmin Z Y Cdict (Z^data.d)
      C₀ A ((dyadicLength (Z^data.d) : ℝ)^2)
      (countHeight budget (Mcap+1) Z (Z^data.d)) Clog (countHeightConstant budget) Knorm
      (detectorRate (2*b-1) δ) hZ1.le hY1 hYlower hCdict data.scale hC₀.le hA
      (by
        have hd : (1 : ℝ) ≤ (dyadicLength (Z^data.d) : ℝ) := by
          unfold dyadicLength
          push_cast
          have hp : (0 : ℝ) ≤ (HeckeDetectorPartition.length (⌈2*(Z^data.d)^21⌉₊ : ℝ) : ℝ) := Nat.cast_nonneg _
          linarith
        nlinarith)
      data.height_nonneg (by linarith) hCH.le hKnorm.le data.log_bound data.height_bound
      ⟨by linarith [hrate.1], hrate.2⟩
    have hc : (F.card : ℝ) ≤ Csmall*Y^(detectorRate (2*b-1) δ+loss) := by
      apply (show (F.card : ℝ) ≤ C₀*max 1 (A*(dyadicLength (Z^data.d) : ℝ)^2*
        (1+countHeight budget (Mcap+1) Z (Z^data.d)))*(Knorm*Z^budget.normLoss)*
        (Z^data.d)^(detectorRate (2*b-1) δ+83*budget.eps+2*budget.buffer) from ?_).trans
        (by simpa only [Csmall] using hbound)
      simpa only [A, mul_assoc] using hcount
    have hmult : Csmall ≤ C*(1+T)^J := by
      have hC0 : Csmall ≤ C := by dsimp [C]; linarith
      exact hC0.trans (le_mul_of_one_le_right hC.le hheight1)
    exact hc.trans (mul_le_mul_of_nonneg_right hmult (by positivity))
  · have hEY : ∀ z ∈ F.image Subtype.val, z ≠ 0 ∧ ((Ideal.span {z}).absNorm : ℝ) ≤ Y := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨u.property.1, (hF u hu).1⟩
    have hYcap : Y ≤ Z^(Mcap+1) := by
      have hYCU : Y ≤ Cdict*Y := by nlinarith
      exact hYCU.trans (data.scale ▸ Real.rpow_le_rpow_of_exponent_le hZ1.le data.upper)
    have htrivial := hlarge Z (Mcap+1) 0 T (F.image Subtype.val)
      hZ1.le (by linarith) le_rfl (by norm_num) (le_of_not_ge hlow)
      (fun z hz => (hEY z hz).1) (fun z hz => (hEY z hz).2.trans hYcap)
    have hc : (F.card : ℝ) ≤ 768*(1+T)^J := by
      simpa only [Real.rpow_zero, mul_one, Finset.card_image_of_injective F Subtype.val_injective] using htrivial
    have h768 : (768 : ℝ) ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ 768*(1+T)^J := hc
      _ ≤ C*(1+T)^J := mul_le_mul_of_nonneg_right h768 (by positivity)
      _ ≤ C*(1+T)^J*Y^(detectorRate (2*b-1) δ+loss) :=
        le_mul_of_one_le_right (by positivity) hYpow

/-- Actual whole sixth-root population, from the selected OPERATOR bound.
`P` is allowed to depend on the natural root, so all common Euler-hole masks
and original slot selections are retained. Principal cores and small cores
are counted separately; neither is an input count assumption. -/
theorem natural_selected_count_eventually (dmin Mcap loss Cdict bΦ Knorm : ℝ)
    (budget : EarlyCountBudget dmin loss) (hdmin : 0 < dmin) (hdminCap : dmin ≤ Mcap)
    (hMcap : 0 < Mcap) (hCdict : 1 ≤ Cdict) (hbΦ : 1 ≤ bΦ) (hKnorm : 0 < Knorm)
    {Label : Type} [Fintype Label] (base : Label → Character) (reverse : Label → Bool)
    (hconductor : ∀ u : FreeRow, ∀ j,
      (((FixedUnmarkedDictionary.ofBases base).naturalFamily u j).modulus.absNorm : ℝ) ≤ Cdict*rowNorm u) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (B b δ T : ℝ) (P : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop),
      Z^(20*dmin) ≤ B → B ≤ bΦ*Z^Mcap →
      b ∈ Icc ((3/4 : ℝ)+budget.buffer) (7/8) →
      δ ∈ Icc (500001/1000000 : ℝ) (3/4) → 0 ≤ T →
      (∀ (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (F : Finset FreeRow),
        Z^dmin ≤ Y → Y ≤ B → (∀ u ∈ F, rowNorm u ≤ Y ∧ P root u) →
        SelectedAllSourceNormBound (F.image Subtype.val) Y δ (Knorm*Z^budget.normLoss)
          (Z^(3*(Mcap+1)+1))) →
      ∀ rows : Finset NonzeroFrequency,
      (∀ z ∈ rows, rawFrequencyNorm z ≤ B ∧ naturalActualZeroRow base reverse b T z ∧
        P (sixthFrequencyEquiv.symm z).2 (sixthFrequencyEquiv.symm z).1) →
      (rows.card : ℝ) ≤ C*(1+T)^J*B^(detectorRate (2*b-1) δ+loss) := by
  obtain ⟨J,Ccore,hCcore,hcores⟩ := regular_core_count_eventually dmin Mcap loss Cdict bΦ Knorm
    budget hdmin hdminCap hMcap hCdict hbΦ hKnorm base reverse hconductor
  obtain ⟨D,hD,hroots⟩ := natural_root_count_of_uniform_free_counts
  obtain ⟨Cpr,hCpr,hprincipal⟩ := principal_exceptional_raw_count (FixedUnmarkedDictionary.ofBases base)
  let C := Ccore*D+Cpr+98304
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hcores] with Z hcore
  have hZ := hcore.1
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro B b δ T P hBlower hBupper hb hδ hT hoperator rows hrows
  have hB1 : 1 ≤ B := (Real.one_le_rpow hZ.le (by linarith : 0 ≤ 20*dmin)).trans hBlower
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hloss : 0 ≤ loss := by
    have hp : 0 ≤ 83*budget.eps+2*budget.buffer+budget.logLoss+
      (budget.tau+budget.normLoss)/dmin := by
      have h1 := budget.eps_pos
      have h2 := budget.buffer_pos
      have h3 := budget.logLoss_pos
      have h4 := budget.tau_pos
      have h5 := budget.normLoss_pos
      positivity
    exact hp.trans budget.total_loss
  let R := detectorRate (2*b-1) δ+loss
  have hrateBounds : (1/4 : ℝ) ≤ detectorRate (2*b-1) δ :=
    (detectorRate_bounds (ν := 2*b-1) (δ := δ) (by linarith [hb.2]) hδ).1
  have hR : (1/4 : ℝ) ≤ R := by
    dsimp [R]
    linarith
  have hBsmall : Z^dmin ≤ B^(1/20 : ℝ) := by
    calc
      _ = (Z^(20*dmin))^(1/20 : ℝ) := by rw [← Real.rpow_mul hZp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hBlower (by norm_num)
  let Dct := FixedUnmarkedDictionary.ofBases base
  let Q : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop := fun root u =>
    rowNorm u ≤ B ∧ ¬Dct.exceptionalCore u ∧ B^(1/20 : ℝ) ≤ rowNorm u ∧
    naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (u,root)) ∧ P root u
  have hfree (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (hY : 1 ≤ Y)
      (F : Finset FreeRow) (hF : ∀ u ∈ F, rowNorm u ≤ Y ∧ Q root u) :
      (F.card : ℝ) ≤ (Ccore*(1+T)^J)*Y^R := by
    by_cases hne : F.Nonempty
    · obtain ⟨u₀,hu₀⟩ := hne
      let Ystar := min Y B
      have hFscale : ∀ u ∈ F, rowNorm u ≤ Ystar := by
        intro u hu
        exact le_min (hF u hu).1 (hF u hu).2.1
      have hsmallY : B^(1/20 : ℝ) ≤ Ystar :=
        (hF u₀ hu₀).2.2.2.1.trans (hFscale u₀ hu₀)
      have hYlower : Z^dmin ≤ Ystar := hBsmall.trans hsmallY
      have hYupper : Ystar ≤ bΦ*Z^Mcap := (min_le_right Y B).trans hBupper
      have hnorm := hoperator root Ystar F hYlower (min_le_right Y B)
        (fun u hu => ⟨hFscale u hu,(hF u hu).2.2.2.2.2⟩)
      have hc := hcore.2 Ystar b δ T root F hYlower hYupper hb hδ hT
        (fun u hu => ⟨hFscale u hu,(hF u hu).2.2.1,(hF u hu).2.2.2.2.1⟩) hnorm
      exact hc.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity [Ystar]) (min_le_left Y B) (by linarith)) (by positivity))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  let exceptional := rows.filter fun z => Dct.exceptionalCore (sixthFrequencyEquiv.symm z).1
  let regular := rows.filter fun z => ¬Dct.exceptionalCore (sixthFrequencyEquiv.symm z).1
  let small := regular.filter fun z => rowNorm (sixthFrequencyEquiv.symm z).1 < B^(1/20 : ℝ)
  let large := regular.filter fun z => ¬rowNorm (sixthFrequencyEquiv.symm z).1 < B^(1/20 : ℝ)
  have hcard : (rows.card : ℝ) = (exceptional.card : ℝ)+(small.card : ℝ)+(large.card : ℝ) := by
    have h1 := Finset.card_filter_add_card_filter_not (s := rows) (fun z => Dct.exceptionalCore (sixthFrequencyEquiv.symm z).1)
    have h2 := Finset.card_filter_add_card_filter_not (s := regular)
      (fun z => rowNorm (sixthFrequencyEquiv.symm z).1 < B^(1/20 : ℝ))
    change exceptional.card+regular.card = rows.card at h1
    change small.card+large.card = regular.card at h2
    change (rows.card : ℝ) = _
    exact_mod_cast (show rows.card = exceptional.card+small.card+large.card by
      omega)
  have hexceptional : (exceptional.card : ℝ) ≤ Cpr*B^R := by
    have hp := hprincipal B hB1 exceptional (by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      exact ⟨(hrows z hz).1,he⟩)
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) hCpr.le)
  have hsmall : (small.card : ℝ) ≤ 98304*B^R := by
    have hs := small_sixth_core_count_le_joint (small.image Subtype.val) B R hB1 hR
      (by intro z hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz; exact u.property)
      (by intro z hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
          exact (hrows u (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1).1)
      (by intro z hz; obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
          rw [raw_sixth_remainder]
          exact (Finset.mem_filter.mp hu).2.le)
    simpa only [Finset.card_image_of_injective small Subtype.val_injective] using hs
  have hlarge : (large.card : ℝ) ≤ (Ccore*(1+T)^J)*D*B^R := by
    apply hroots Q (Ccore*(1+T)^J) R (by positivity) hR hfree B hBp large
    intro z hz
    obtain ⟨hz,hbig⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz,hregular⟩ := Finset.mem_filter.mp hz
    have hrow := hrows z hz
    have hcoreNorm : rowNorm (sixthFrequencyEquiv.symm z).1 ≤ B := by
      have hn := raw_sixth_norm (sixthFrequencyEquiv.symm z)
      simp only [Equiv.apply_symm_apply] at hn
      have hroot : 1 ≤ (((sixthFrequencyEquiv.symm z).2.val.absNorm : ℝ))^6 := by
        have hp : 1 ≤ ((sixthFrequencyEquiv.symm z).2.val.absNorm : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (sixthFrequencyEquiv.symm z).2.property)
        exact one_le_pow₀ hp
      have hu := rowNorm_ge_one (sixthFrequencyEquiv.symm z).1
      nlinarith [hrow.1]
    refine ⟨hrow.1,hcoreNorm,hregular,le_of_not_gt hbig,?_,hrow.2.2⟩
    change naturalActualZeroRow base reverse b T (sixthFrequencyEquiv (sixthFrequencyEquiv.symm z))
    rw [Equiv.apply_symm_apply]
    exact hrow.2.1
  have hheight : 1 ≤ (1+T)^J := one_le_pow₀ (by linarith)
  calc
    _ = (exceptional.card : ℝ)+(small.card : ℝ)+(large.card : ℝ) := hcard
    _ ≤ Cpr*B^R+98304*B^R+(Ccore*(1+T)^J)*D*B^R := add_le_add (add_le_add hexceptional hsmall) hlarge
    _ ≤ C*(1+T)^J*B^R := by
      dsimp only [C]
      have hp : 0 ≤ B^R := by positivity
      nlinarith

/-- The literal natural joint-count contract follows from the explicit actual
selected OPERATOR inlet. This generic adapter takes the operator bound as an explicit hypothesis;
the canonical assembly supplies its concrete instance. -/
theorem wholeJointCountOn_of_actualSelectedSlotNorm (hnorm : ActualSelectedSlotNorm)
    (νMin : ℝ) (hνMin : (14/25 : ℝ) ≤ νMin) : WholeJointCountOn νMin := by
  intro Mmin Mcap smin loss hMmin hMcap hsmin hloss
  let dmin := Mmin/20
  have hdmin : 0 < dmin := by dsimp [dmin]; positivity
  have hdminCap : dmin ≤ Mcap := by dsimp [dmin]; linarith
  have hMcapPos : 0 < Mcap := hMmin.trans_le hMcap
  obtain ⟨budget⟩ := exists_early_count_budget dmin loss hdmin hloss
  obtain ⟨meshMax,hmeshMax,hoperator⟩ := hnorm Mmin Mcap smin budget.normLoss 0
    hMmin hMcap hsmin budget.normLoss_pos (by norm_num)
  refine ⟨meshMax,hmeshMax,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWsupport κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Knorm,hKnorm,hnormEvent⟩ := hoperator mesh hmesh α rayM H hH W hW hWsupport κ anchors η₀ bΦ hbΦ
  let base := orientedFixedBase (QRH.SilDensitySplit.Density.highDictionary rayM H hH anchors η₀)
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨Cdict,hCdict,hconductor⟩ := D.natural_conductor_bound
  obtain ⟨Jcore,Ccore,hCcore,hcoreEvent⟩ := natural_selected_count_eventually
    dmin Mcap loss Cdict bΦ Knorm budget hdmin hdminCap hMcapPos hCdict hbΦ hKnorm base Prod.snd hconductor
  obtain ⟨Jzero,Czero,hCzero,hzero⟩ := FineAdaptiveSupplier.high_row_count_on rayM H hH νMin hνMin anchors η₀ loss hloss
  let J := max Jcore Jzero
  let C := Ccore+Czero
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hnormEvent,hcoreEvent] with Z hnormZ hcoreZ
  have hZ := hcoreZ.1
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro j st hchar hpuncture hMlower hMupper hQM hQη T θ w σ v t height
    hw hwmesh hσ hσ' hheight hv hs b δ T' hb hb' hδ hT' rows hrows
  let B := bΦ*Z^st.rowWidth
  have hMrowCap : st.rowWidth ≤ Mcap := by
    have hw : st.rowWidth ≤ st.width := by
      dsimp [NaturalState.width]
      linarith [st.character_nonneg]
    exact hw.trans hMupper
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact one_le_mul_of_one_le_of_one_le hbΦ (Real.one_le_rpow hZ.le (hMmin.le.trans hMlower))
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hBlower : Z^(20*dmin) ≤ B := by
    have h20 : 20*dmin = Mmin := by dsimp [dmin]; ring
    rw [h20]
    exact (Real.rpow_le_rpow_of_exponent_le hZ.le hMlower).trans
      (le_mul_of_one_le_left (by positivity) hbΦ)
  have hBupper : B ≤ bΦ*Z^Mcap := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le hMrowCap) (by linarith)
  have hbbuffer : b ∈ Icc ((3/4 : ℝ)+budget.buffer) (7/8) :=
    ⟨by linarith [budget.buffer_cap],hb'⟩
  let P : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop := fun root u =>
    ∃ hz : st.radial.keep (rowMap (u,root)),
      st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
      Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))
  have hnormActual (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (F : Finset FreeRow)
      (hYlower : Z^dmin ≤ Y) (hYupper : Y ≤ B) (hF : ∀ u ∈ F, rowNorm u ≤ Y ∧ P root u) :
      SelectedAllSourceNormBound (F.image Subtype.val) Y δ (Knorm*Z^budget.normLoss)
        (Z^(3*(Mcap+1)+1)) := by
    have h := hnormZ.2 j st hchar hpuncture hMlower hMupper T θ w σ v t height
      hw hwmesh hσ hσ' hheight hv hs δ Y root F hδ hYlower hYupper hF
    have hcap : detectorAuxiliarySourceCap 0 (Mcap+1) = 3*(Mcap+1)+1 := by
      unfold detectorAuxiliarySourceCap
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 3*(Mcap+1))]
    simpa only [hcap] using h
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype,Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk,_⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hselected : ∀ z ∈ rows', rawFrequencyNorm z ≤ B ∧ naturalActualZeroRow base Prod.snd b T' z ∧
      P (sixthFrequencyEquiv.symm z).2 (sixthFrequencyEquiv.symm z).1 := by
    intro z hz
    have hzrows := Finset.mem_subtype.mp hz
    obtain ⟨hk,hp,hm,ha⟩ := hrows z.val hzrows
    have hnatural := physical_row_to_fixed_natural_zero rayM H hH anchors η₀ j st hchar hpuncture
      hQM hQη b T' (by linarith) z hk hp hm
    refine ⟨hnatural.1,hnatural.2,?_⟩
    have heq : rowMap ((sixthFrequencyEquiv.symm z).1,(sixthFrequencyEquiv.symm z).2) = z.val :=
      congrArg Subtype.val (sixthFrequencyEquiv.apply_symm_apply z)
    dsimp only [P]
    simpa only [heq] using (show ∃ hz : st.radial.keep z.val,
      st.radial.profile (‖eisEmbedding z.val‖^2/st.radial.scale) ≠ 0 ∧
      Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z.val from ⟨hk,hp,ha⟩)
  have hcount := hcoreZ.2 B b δ T' P hBlower hBupper hbbuffer hδ hT' hnormActual rows' hselected
  rw [hcard] at hcount
  have hzeroCount := hzero (by linarith : 0 < bΦ) j st hchar hpuncture hQM hQη b T' hb hb' hT' rows
    (by intro z hz; obtain ⟨hk,hp,hm,_⟩ := hrows z hz; exact ⟨hk,hp,hm⟩)
  have hheightCore : (1+T')^Jcore ≤ (1+T')^J := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have hheightZero : (1+T')^Jzero ≤ (1+T')^J := pow_le_pow_right₀ (by linarith) (le_max_right _ _)
  have hcore' : (rows.card : ℝ) ≤ C*(1+T')^J*B^(detectorRate (2*b-1) δ+loss) :=
    hcount.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (by dsimp [C]; linarith : Ccore ≤ C) hheightCore (by positivity) hC.le) (by positivity))
  have hzero' : (rows.card : ℝ) ≤ C*(1+T')^J*B^((1-AdaptivePrice.k (2*b-1))+loss) := by
    have heq : unmarkedDensity (2*b-1) = 1-AdaptivePrice.k (2*b-1) := by
      unfold unmarkedDensity AdaptivePrice.k
      congr 2
      ring
    rw [heq] at hzeroCount
    exact hzeroCount.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (by dsimp [C]; linarith : Czero ≤ C) hheightZero (by positivity) hC.le) (by positivity))
  have hrate : AdaptivePrice.jointRate (2*b-1) δ = min (1-AdaptivePrice.k (2*b-1)) (detectorRate (2*b-1) δ) := by
    unfold AdaptivePrice.jointRate detectorRate
    split_ifs <;> rfl
  rw [hrate]
  rcases le_total (1-AdaptivePrice.k (2*b-1)) (detectorRate (2*b-1) δ) with hle | hle
  · simpa only [min_eq_left hle] using hzero'
  · simpa only [min_eq_right hle] using hcore'

end
end Qrh.JointDetector.FineNaturalCount

#print axioms Qrh.JointDetector.FineNaturalCount.normalizedSlot_sixth_root
#print axioms Qrh.JointDetector.FineNaturalCount.naturalState_mask_divisibility
#print axioms Qrh.JointDetector.FineNaturalCount.physical_row_to_fixed_natural_zero
#print axioms Qrh.JointDetector.FineNaturalCount.regular_natural_zero_to_free_maximum
#print axioms Qrh.JointDetector.FineNaturalCount.principal_exceptional_raw_count
#print axioms Qrh.JointDetector.FineNaturalCount.regular_core_count_on_scale
#print axioms Qrh.JointDetector.FineNaturalCount.exists_early_count_budget
#print axioms Qrh.JointDetector.FineNaturalCount.regular_count_scalar_absorption
#print axioms Qrh.JointDetector.FineNaturalCount.uniform_core_scale_data

#print axioms Qrh.JointDetector.FineNaturalCount.regular_core_count_eventually

#print axioms Qrh.JointDetector.FineNaturalCount.natural_selected_count_eventually

#print axioms Qrh.JointDetector.FineNaturalCount.wholeJointCountOn_of_actualSelectedSlotNorm
