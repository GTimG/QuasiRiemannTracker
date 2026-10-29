/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Unmarked
import Candidate.Local.Qrh.JointDetector.RefinedSupplier
import Candidate.Local.Qrh.JointDetector.AdaptivePrice

namespace Qrh.JointDetector.RepeatedMarks.UnmarkedHigh
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentRetainedProfile
open LocalMoment HeckeDetectorZeros ProbePhysical ActualEisensteinCubic
open RefinedSupplier
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

section Count
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

theorem high_row_count {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character)
    (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {Z bΦ : ℝ}, 0 < bΦ → ∀ (j : κ) (st : NaturalState Z 0 bΦ),
      st.character = anchors j → st.puncture = 1 →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (b T' : ℝ), 79/100 ≤ b → b ≤ 7/8 → 0 ≤ T' →
      ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T') →
      (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(unmarkedDensity (2*b-1)+loss) := by
  obtain ⟨J, C, hC, hcount⟩ := Unmarked.fixed_natural_dictionary_raw_density
    (orientedFixedBase (highDictionary rayM H hH anchors η₀)) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro Z bΦ hbΦ j st hchar hu hQM hQη b T' hb hb' hT' rows hrows
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk, _⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hZ0 : 0 < Z := zero_lt_one.trans_le st.base_ge_one
  have hH0 : 0 < bΦ*Z^st.rowWidth := mul_pos hbΦ (Real.rpow_pos_of_pos hZ0 _)
  rw [← hcard]
  apply hcount Prod.snd b T' hb hb' hT' _ hH0 rows'
  intro u hu'
  have hz : u.val ∈ rows := Finset.mem_subtype.mp hu'
  obtain ⟨hk, hp, hmax⟩ := hrows u.val hz
  refine ⟨?_, ?_⟩
  · -- the frequency norm
    have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · -- the zero transfer to the fixed dictionary
    have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow (anchors j) u.val u.property).character 1) I := by
      intro I
      rw [hu, excluded_ideal _ _ one_ne_zero, excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal, NaturalRow.ideal, hchar]
    exact physical_family_maximum_to_fixed_dictionary (highDictionary rayM H hH anchors η₀)
      (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ u.val hk) (fun _ => false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk)
      (fun idx => (j, idx)) (fun _ => 1) u
      (fun idx I => whole_source_family_mask rayM H hH η₀ (anchors j)
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) u.val u.property (naturalRow (anchors j) u.val u.property) 1
        one_ne_zero hc0
        (fun idx => naturalRow (wholeSourceBase rayM H hH η₀ (anchors j) idx) u.val
          u.property) idx I)
      b T' (by linarith) hmax


theorem high_row_count_on (νMin : ℝ) (hmin : (2/5:ℝ) ≤ νMin) {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character)
    (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {Z bΦ : ℝ}, 0 < bΦ → ∀ (j : κ) (st : NaturalState Z 0 bΦ),
      st.character = anchors j → st.puncture = 1 →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (b T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 → 0 ≤ T' →
      ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T') →
      (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(unmarkedDensity (2*b-1)+loss) := by
  obtain ⟨J, C, hC, hcount⟩ := Unmarked.fixed_natural_dictionary_raw_density_floor700
    (orientedFixedBase (highDictionary rayM H hH anchors η₀)) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro Z bΦ hbΦ j st hchar hu hQM hQη b T' hb hb' hT' rows hrows
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk, _⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hZ0 : 0 < Z := zero_lt_one.trans_le st.base_ge_one
  have hH0 : 0 < bΦ*Z^st.rowWidth := mul_pos hbΦ (Real.rpow_pos_of_pos hZ0 _)
  rw [← hcard]
  apply hcount Prod.snd b T' (by linarith) hb' hT' _ hH0 rows'
  intro u hu'
  have hz : u.val ∈ rows := Finset.mem_subtype.mp hu'
  obtain ⟨hk, hp, hmax⟩ := hrows u.val hz
  refine ⟨?_, ?_⟩
  · -- the frequency norm
    have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · -- the zero transfer to the fixed dictionary
    have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow (anchors j) u.val u.property).character 1) I := by
      intro I
      rw [hu, excluded_ideal _ _ one_ne_zero, excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal, NaturalRow.ideal, hchar]
    exact physical_family_maximum_to_fixed_dictionary (highDictionary rayM H hH anchors η₀)
      (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ u.val hk) (fun _ => false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk)
      (fun idx => (j, idx)) (fun _ => 1) u
      (fun idx I => whole_source_family_mask rayM H hH η₀ (anchors j)
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) u.val u.property (naturalRow (anchors j) u.val u.property) 1
        one_ne_zero hc0
        (fun idx => naturalRow (wholeSourceBase rayM H hH η₀ (anchors j) idx) u.val
          u.property) idx I)
      b T' (by linarith) hmax

end Count

end
end Qrh.JointDetector.RepeatedMarks.UnmarkedHigh
