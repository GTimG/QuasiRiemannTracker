import Submissions.argonaut_20261008.HighFrontierTargets
import Submissions.argonaut_20261008.MomentAllowancePerturbed
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiberEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedRestrictedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate Topology
open Filter Set

namespace SevenEighths.PerturbedMomentConstruction

open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorBatch HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyCertifiedExistence
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainMarkedState CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainMomentParameters CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorPlainExceptional CenteredMomentRetainedEnergy
open ProbeDetectorPlainUnmarkedField ProbeDetectorPlainUnmarkedRestrictedField
open ProbeDetectorPlainMarkedFineField ProbeDetectorInverseRawField
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
open HighFrontierTargets PerturbedMomentAllowance
open ProbePhysical (fixedPrimeProduct_ne_zero SourceExclusions)
open InverseInitialPhysicalSlots (livePrimes livePrime_data live_tuple_injective live_tuple_admissible)
open InverseInitialRawDictionary (fixedBase)
open InverseInitialDetectorSource (baseCharacter primeProfile)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy (energy)
open InverseMoment (childLogTest)
open QuadraticInitialBound (diagonalControl diagonalControl_nonneg)
open CenteredMomentDetectorPlainProfileControl (paired_control)

local notation "O" => HeckeFamily.O

/-- The nonnegative allowance used by the `Moments.plain_marked` field. -/
def momentGamma : ℝ := gamma HeckeZeroSupremum.beta

/-- The actual terminal-energy coefficient.  It may equal `3/4`. -/
def momentKappa : ℝ := 3 / 4 + 2 * momentGamma

/-- Energy-stage error and initial character width remain independent of `momentGamma`. -/
def stageError (t : ℝ) : ℝ := t / 4
def initialDelta (t : ℝ) : ℝ := t / 4

def detectorMesh (t : ℝ) : ℝ :=
  fineMesh 2 0 1 momentKappa (stageError t)

lemma momentGamma_nonneg : 0 ≤ momentGamma := by
  simpa [momentGamma] using gamma_nonneg HeckeZeroSupremum.beta

lemma momentGamma_le_eighth : momentGamma ≤ 1 / 8 := by
  simpa [momentGamma] using gamma_le_eighth HeckeZeroSupremum.beta_le_one

lemma momentKappa_ge_three_quarters : (3 / 4 : ℝ) ≤ momentKappa := by
  simpa only [momentKappa, momentGamma, PerturbedMomentAllowance.kappaPlain] using
    kappaPlain_ge_three_quarters HeckeZeroSupremum.beta

lemma momentKappa_ge_zero_capacity :
    2 * HeckeZeroSupremum.beta - 1 ≤ momentKappa := by
  simpa [momentKappa, momentGamma, PerturbedMomentAllowance.kappaPlain] using
    kappaPlain_ge_zero_capacity HeckeZeroSupremum.beta

lemma momentKappa_pos : 0 < momentKappa := by
  linarith [momentKappa_ge_three_quarters]

lemma momentKappa_le_one : momentKappa ≤ 1 := by
  simpa [momentKappa, momentGamma, PerturbedMomentAllowance.kappaPlain] using
    kappaPlain_le_one HeckeZeroSupremum.beta_le_one

lemma beta_ge_fifty_one_hundred
    (hβ : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta) :
    (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta := by
  have hb : (51 / 100 : ℝ) < HighFrontierTargets.sigmaBoundary := by
    norm_num [HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho]
  linarith

/--
Only scalar/finite geometry used by the terminal certificate and the four moment
fields.  In particular there is no moment estimate, energy estimate, high-probe
estimate, or final nonvanishing statement in this record.
-/
structure MomentGeometry where
  t : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_small : t ≤ 1 / 100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j, ell j) = HighFrontierTargets.totalE
  slots_bounds : ∀j, 0 < ell j ∧ (7 / 8 : ℝ) * rmin ≤ ell j ∧ ell j ≤ (1 / 200 : ℝ) * t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1 / 1000
  e_pos : 0 < e
  e_small : e < 1 / 1000
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  fine_slots : ∀j, ell j ≤ detectorMesh t / 200
  height_choice : ∀J : ℝ, 0 ≤ J → ∃theta : ℝ,
    0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
    4 * theta < (1 / 200 : ℝ) * cost ∧ theta < t ∧
    2 * theta * (1 + J) ≤ t ∧ theta * (2 + 4 * eps) < t

lemma stageError_pos (G : MomentGeometry) : 0 < stageError G.t := by
  dsimp [stageError]
  exact div_pos G.t_pos (by norm_num)

lemma initialDelta_pos (G : MomentGeometry) : 0 < initialDelta G.t := by
  dsimp [initialDelta]
  exact div_pos G.t_pos (by norm_num)

lemma initialDelta_le_quarter (G : MomentGeometry) : initialDelta G.t ≤ 1 / 4 := by
  dsimp [initialDelta]
  linarith [G.t_small]

lemma stage_budget (G : MomentGeometry) :
    initialDelta G.t + stageError G.t ≤ G.t := by
  dsimp [initialDelta, stageError]
  linarith [G.t_pos]

lemma detectorMesh_pos (G : MomentGeometry) : 0 < detectorMesh G.t := by
  unfold detectorMesh
  exact
    (bounds 2 (finalSourceCap 2 0 1 (stageError G.t)) momentKappa (stageError G.t)
      (by norm_num)
      (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
      (show 0 ≤ momentKappa by linarith [momentKappa_ge_three_quarters])
      (stageError_pos G)).2.2.2.2.1

/-- Enlarging the deleted finite set preserves a `FirstTail` certificate. -/
theorem FirstTail.mono_finset {eps : ℝ} {S T : Finset (Ideal O)}
    (hST : S ⊆ T) (h : FirstTail eps S) : FirstTail eps T := by
  refine ⟨h.positive, ?_, ?_⟩
  · intro P hPT
    exact h.norm_four P (fun hPS => hPT (hST hPS))
  · let inc : {P : PrimeIdeal // P.val ∉ T} → {P : PrimeIdeal // P.val ∉ S} :=
      fun P => ⟨P.val, fun hPS => P.property (hST hPS)⟩
    have hi : Function.Injective inc := by
      intro P Q hPQ
      exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val ∉ S} => R.val) hPQ)
    apply le_trans ?_ h.small
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => firstPrimeDefectBound_nonneg eps P.val)
      (fun _ => le_rfl)
      ((firstPrimeDefectBound_summable eps h.positive).subtype _)
      ((firstPrimeDefectBound_summable eps h.positive).subtype _)

/-- A frozen old `HighData` value used only as a carrier for the public source-window record. -/
def auxiliaryHighData : Parameters.HighData 1 :=
  Classical.choice (Parameters.exists_high_data 1 (by norm_num))

/--
A real fixed source/window package for the perturbed scalar geometry.  `core` lets
us reuse the public source lemmas; `first` is the tail certificate at the actual
perturbed `e`, not at the auxiliary carrier's `e`.
-/
structure PerturbedSourceData (G : MomentGeometry) where
  core : ProbeFinalAssembly.SourceData auxiliaryHighData
  first : FirstTail (4 * G.e) core.S

namespace PerturbedSourceData

abbrev S {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.S
abbrev exclusions {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.exclusions
abbrev maximal {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.maximal
abbrev w {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.w
abbrev W {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.W
abbrev smooth {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.smooth
abbrev compact {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.compact
abbrev support {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.support
abbrev positive_support {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.positive_support
abbrev bounded {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.bounded
abbrev nonzero {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.nonzero
abbrev complex_eq {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.complex_eq
abbrev complex_nonzero {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.complex_nonzero
abbrev complex_support {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.complex_support
abbrev real {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.real
abbrev nonnegative {G : MomentGeometry} (F : PerturbedSourceData G) := F.core.nonnegative

def modulus {G : MomentGeometry} (F : PerturbedSourceData G) : Ideal O := F.core.modulus

instance {G : MomentGeometry} (F : PerturbedSourceData G) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {G : MomentGeometry} (F : PerturbedSourceData G) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

end PerturbedSourceData

/-- Actual source construction at `G.e`, with no analytic target field. -/
theorem exists_perturbed_source_data (G : MomentGeometry) :
    Nonempty (PerturbedSourceData G) := by
  obtain ⟨S₀, _, hS₀, hfirst₀, _⟩ :=
    Parameters.exists_fixed_source auxiliaryHighData.e auxiliaryHighData.e_pos ∅ (by simp)
  obtain ⟨S, hsub, hS, hfirst, hmax⟩ :=
    Parameters.exists_fixed_source G.e G.e_pos S₀ hS₀.prime
  have hfirstAux : FirstTail (4 * auxiliaryHighData.e) S :=
    FirstTail.mono_finset hsub hfirst₀
  obtain ⟨w, W, hw, hc, hs, hp, hb, hn, he, hWn, hWs, hr, hWpos⟩ :=
    Parameters.exists_fixed_probe_window
  let core : ProbeFinalAssembly.SourceData auxiliaryHighData := {
    S := S
    exclusions := hS
    maximal := hmax
    first := hfirstAux
    w := w
    W := W
    smooth := hw
    compact := hc
    support := hs
    positive_support := hp
    bounded := hb
    nonzero := hn
    complex_eq := he
    complex_nonzero := hWn
    complex_support := hWs
    real := hr
    nonnegative := hWpos }
  exact ⟨⟨core, hfirst⟩⟩

/-- Count constants at the actual perturbed moment error `G.t`. -/
theorem source_count_parameters (G : MomentGeometry) (F : PerturbedSourceData G) :
    Nonempty (CountParameters F.modulus ⊤ G.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x => (F.bounded x).2) G.t G.t_pos

/-- Positive-energy output extracted from the genuine terminal certificate. -/
def PositiveFineSourceInput (G : MomentGeometry) (F : PerturbedSourceData G)
    (mesh : ℝ) : Prop :=
  ∀bΦ : ℝ, 0 < bΦ → ∃degree : ℕ, ∃seminorms : Finset (ℕ × ℕ),
    ∀η₀ : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠU : ℝ in atTop,
      PositiveAt (α := Fin G.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
        2 (1 / 4) (9 / 4) bΦ 0 1 mesh (33 / 50) (33 / 50) 2
        (stageError G.t) momentKappa U η₀
        (sourceFixedIdeal F.core) degree seminorms C

/-- Zero-energy output extracted from the same terminal certificate. -/
def ZeroSourceInput (G : MomentGeometry) (F : PerturbedSourceData G) : Prop :=
  ∃degree : ℕ, ∃control : Finset (ℕ × ℕ), ∀η₀ : Character, ∃A : ℝ, 0 < A ∧
    ∀ᶠU : ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F.core) η₀)
        (1 / 4) (9 / 4) ProbeDetectorPlainUnmarkedField.radialSupportUpper
        0 1 2 (stageError G.t) U degree control A

/-- Genuine terminal energy certificate at the nonnegative `momentGamma`. -/
theorem terminal_certificate
    (hβ : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (G : MomentGeometry) (F : PerturbedSourceData G) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    CertifiedBand (α := Fin G.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
      2 (1 / 4) (9 / 4) bΦ 0 1 (33 / 50) (33 / 50) 2
      momentKappa (stageError G.t) (count 2 (stageError G.t)) := by
  apply CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Fin G.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ
    0 1 (33 / 50) (33 / 50) 2 momentKappa (stageError G.t)
  · norm_num
  · exact CenteredMomentDetectorPlainSlotProfile.conjugate_source_support F.core
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact momentKappa_ge_three_quarters
  · exact stageError_pos G
  · exact beta_ge_fifty_one_hundred hβ
  · exact momentKappa_ge_zero_capacity

/-- Extract the positive and zero inputs from the actual terminal certificate. -/
theorem terminal_inputs
    (hβ : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (G : MomentGeometry) (F : PerturbedSourceData G) :
    PositiveFineSourceInput G F (detectorMesh G.t) ∧ ZeroSourceInput G F := by
  have hcert (bΦ : ℝ) (hbΦ : 0 < bΦ) := terminal_certificate hβ G F bΦ hbΦ
  have hactual (bΦ : ℝ) (hbΦ : 0 < bΦ) :
      ∃degree : ℕ, ∃control : Finset (ℕ × ℕ), ∀η₀ : Character,
      ∃Czero Cpositive : ℝ, 0 < Czero ∧ 0 < Cpositive ∧ ∀ᶠU : ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F.core) η₀)
        (1 / 4) (9 / 4) bΦ 0 1 2 (stageError G.t) U degree control Czero ∧
      PositiveAt (α := Fin G.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
        2 (1 / 4) (9 / 4) bΦ 0 1 (detectorMesh G.t)
        (33 / 50) (33 / 50) 2 (stageError G.t) momentKappa
        U η₀ (sourceFixedIdeal F.core) degree control Cpositive := by
    obtain ⟨degree, control, hbound⟩ :=
      CenteredMomentEnergyCappedWidthInduction.certified_terminal
        F.modulus ⊤ le_top (fun x => conj (F.W x))
        2 (1 / 4) (9 / 4) bΦ 0 1 (33 / 50) (33 / 50) 2
        momentKappa (stageError G.t)
        (by norm_num) (by norm_num) (show 0 ≤ momentKappa by linarith [momentKappa_ge_three_quarters])
        (stageError_pos G) (hcert bΦ hbΦ)
    refine ⟨degree, control, ?_⟩
    intro η₀
    obtain ⟨Cz, Cp, hCz, hCp, hbound⟩ := hbound η₀ (sourceFixedIdeal F.core)
      (sourceFixedIdeal_le_modulus F.core)
      (source_fixed_gates F.core η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F.core) η₀)
      (source_fixed_gates F.core η₀).2.2.2
    exact ⟨Cz, Cp, hCz, hCp, hbound.mono (fun U h => ⟨h.2.1, h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree, control, h⟩ := hactual bΦ hbΦ
    refine ⟨degree, control, ?_⟩
    intro η₀
    obtain ⟨Cz, Cp, hCz, hCp, h⟩ := h η₀
    exact ⟨Cp, hCp, h.mono (fun U hU => hU.2)⟩
  · obtain ⟨degree, control, h⟩ :=
      hactual ProbeDetectorPlainUnmarkedField.radialSupportUpper
        ProbeDetectorPlainUnmarkedField.radialSupportUpper_spec.1
    refine ⟨degree, control, ?_⟩
    intro η₀
    obtain ⟨Cz, Cp, hCz, hCp, h⟩ := h η₀
    exact ⟨Cz, hCz, h.mono (fun U hU => hU.1)⟩

/-! ### Scalar moment-parameter lemmas, with `t` decoupled from `momentGamma`. -/

lemma source_base_gt_one (G : MomentGeometry) (Z d : ℝ)
    (hZ : 1 < Z) (hd : (1 / 200 : ℝ) ≤ d) : 1 < Z ^ d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (G : MomentGeometry) :
    1 / 2 + 75 * G.ε ≤ (23 / 40 : ℝ) := by
  linarith [G.epsilon_small]

lemma original_width_bounds (G : MomentGeometry) (d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (s : Fin G.N) :
    0 < G.ell s / d ∧ G.ell s / d ≤ G.t := by
  have hdpos : 0 < d := by linarith
  refine ⟨div_pos (G.slots_bounds s).1 hdpos, (div_le_iff₀ hdpos).mpr ?_⟩
  have hs : G.ell s ≤ (1 / 200 : ℝ) * G.t := (G.slots_bounds s).2.2
  nlinarith [G.t_pos]

lemma actual_fiber_lengths (G : MomentGeometry)
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label : Type*}
    {U a tstar T heightAllowance : ℝ} {i : ℕ}
    (F : Fiber M H Label (Fin G.N) U a G.ε tstar T heightAllowance i)
    (hU : 1 < U) :
    0 ≤ F.m ∧ F.m ≤ 1 / 2 + 75 * G.ε ∧ F.m ≤ 23 / 40 ∧
    1 ≤ U ^ F.m ∧ U ^ F.m ≤ U ∧ length U (U ^ F.m) = F.m := by
  have hm := F.lengths hU
  have hcap := hm.2.2.1.trans (witness_length_cap G)
  refine ⟨hm.2.2.2.2, hm.2.2.1, hcap,
    Real.one_le_rpow hU.le hm.2.2.2.2, ?_, ?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m ≤ 1 by linarith)
  · exact CenteredMomentDetectorPlainMarkedState.plain_length_eq F hU

lemma width_bands (G : MomentGeometry) (m : ℝ) (hm : m ≤ 23 / 40) :
    1 ≤ 1 + initialDelta G.t ∧ 1 + initialDelta G.t ≤ 2 ∧
    1 ≤ max 1 (2 * m) + initialDelta G.t ∧
      max 1 (2 * m) + initialDelta G.t ≤ 2 := by
  have hδ : 0 < initialDelta G.t := initialDelta_pos G
  have hd : initialDelta G.t ≤ 1 / 4 := initialDelta_le_quarter G
  have hmax : max 1 (2 * m) ≤ 23 / 20 := max_le (by norm_num) (by linarith)
  have hlo := le_max_left (1 : ℝ) (2 * m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma marked_state_admission (G : MomentGeometry)
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label : Type*}
    {U a tstar T heightAllowance : ℝ} {i : ℕ}
    (F : Fiber M H Label (Fin G.N) U a G.ε tstar T heightAllowance i)
    (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ, ℂ)) (bΦ : ℝ) (hU : 1 < U)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm : ℝ) ≤ U ^ (initialDelta G.t))
    (selected : Finset (Fin G.N))
    (hcap : 2 * F.m + 6 * momentKappa * (∑s∈selected, F.widths s) ≤ 1) :
    let s := initialState η Q Φ bΦ U (initialDelta G.t) hU.le
      (initialDelta_pos G).le hs hp hη
    s.character = η ∧ s.fixedModulus = Q ∧ s.puncture = 1 ∧
    s.radial.profile = Φ ∧ s.radial.scale = U ∧ s.radial.keep = initialKeep η Q ∧
    s.width = 1 + initialDelta G.t ∧ 1 ≤ s.width ∧ s.width ≤ 2 ∧
    1 ≤ U ^ F.m ∧ U ^ F.m ≤ U ∧
    length U (U ^ F.m) + length U (U ^ F.m) +
      6 * momentKappa * (∑s : selected, F.widths s.val) ≤ s.width := by
  dsimp only
  have hf := actual_fiber_lengths G F hU
  have hw := width_bands G F.m hf.2.2.1
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hw.1, hw.2.1,
    hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
  exact CenteredMomentDetectorPlainMarkedState.marked_capacity F hU selected
    momentKappa (initialDelta G.t) (initialDelta_pos G).le hcap

lemma unmarked_state_admission (G : MomentGeometry)
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label : Type*}
    {U a tstar T heightAllowance : ℝ} {i : ℕ}
    (F : Fiber M H Label (Fin G.N) U a G.ε tstar T heightAllowance i)
    (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ, ℂ)) (bΦ : ℝ) (hU : 1 < U)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm : ℝ) ≤ U ^ (initialDelta G.t)) :
    let s := CenteredMomentDetectorPlainUnmarkedState.state F η Q Φ bΦ
      (initialDelta G.t) hU.le (initialDelta_pos G).le hs hp hη
    s.character = η ∧ s.fixedModulus = Q ∧ s.puncture = 1 ∧
    s.radial.profile = Φ ∧ s.radial.scale = U ∧ s.radial.keep = initialKeep η Q ∧
    s.width = max 1 (2 * F.m) + initialDelta G.t ∧ 1 ≤ s.width ∧ s.width ≤ 2 ∧
    1 ≤ U ^ F.m ∧ U ^ F.m ≤ U ∧ 2 * length U (U ^ F.m) ≤ s.width := by
  dsimp only
  have hf := actual_fiber_lengths G F hU
  have hw := width_bands G F.m hf.2.2.1
  have he :
      (CenteredMomentDetectorPlainUnmarkedState.state F η Q Φ bΦ
        (initialDelta G.t) hU.le (initialDelta_pos G).le hs hp hη).width =
        max 1 (2 * F.m) + initialDelta G.t :=
    CenteredMomentDetectorPlainUnmarkedState.padded_width _ _
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, he, ?_, ?_,
    hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
  · rw [he]
    exact hw.2.2.1
  · rw [he]
    exact hw.2.2.2
  · rw [he, hf.2.2.2.2.2]
    exact (le_max_right 1 (2 * F.m)).trans
      (le_add_of_nonneg_right (initialDelta_pos G).le)

lemma source_label_fixed_allowance (G : MomentGeometry) (F : PerturbedSourceData G)
    (η : Character) :
    ∀ᶠZ : ℝ in atTop, 1 < Z ∧
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ, (1 / 200 : ℝ) ≤ d →
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm : ℝ)
        ≤ (Z ^ d) ^ (initialDelta G.t) :=
  source_label_modulus_eventually F.core η (initialDelta G.t) (initialDelta_pos G)

lemma final_exponent_budget (G : MomentGeometry) (base : ℝ) :
    base + initialDelta G.t + stageError G.t ≤ base + G.t := by
  linarith [stage_budget G]

/-! ### Actual prime geometry for the perturbed slot family. -/

theorem sourceMoment_fiber_prime_geometry_eventually
    (G : MomentGeometry) (F : PerturbedSourceData G)
    (η : Character) (εg : ℝ) (hεg : 0 < εg) :
    ∀ᶠZ : ℝ in atTop, 1 ≤ Z ∧ ∀d : ℝ, (1 / 200 : ℝ) ≤ d →
      ∀(a ε tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a ε tstar T allowance i),
      B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
      B.profile = (fun _ x => (F.w x : ℂ)) → B.upper = (fun _ => 2) →
      B.widths = (fun s => G.ell s / d) → (∀s, (B.external s).re = 17 / 50) →
      ∀bin j J K, ∀hne : (B.fiberRows bin j J K).Nonempty,
      let f := B.fiber bin j J K hne
      (∀s t, s ≠ t → Disjoint
        (livePrimes F.modulus ⊤ (f.profile s) (f.upper s) ((Z ^ d) ^ (f.widths s)))
        (livePrimes F.modulus ⊤ (f.profile t) (f.upper t) ((Z ^ d) ^ (f.widths t)))) ∧
      ∀selected : Finset (Fin G.N),
        (∀s : selected, 1 ≤ 2 * (Z ^ d) ^ (f.widths s)) ∧
        (∏s : selected, 2 * (Z ^ d) ^ (f.widths s)) ≤
          (Z ^ d) ^ ((∑s : selected, f.widths s) + εg) ∧
        ∀p : selected → Ideal O,
        p ∈ Fintype.piFinset (fun s : selected =>
          livePrimes F.modulus ⊤ (f.profile s) (f.upper s) ((Z ^ d) ^ (f.widths s))) →
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s, p s) ∧
        (∀s : selected, ((p s).absNorm : ℝ) ≤ 2 * (Z ^ d) ^ (f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s, p s)‖ = 1 ∧
        ‖star (∏s : selected, primeProfile (f.profile s.val) ((Z ^ d) ^ (f.widths s.val))
          (f.external s.val) (p s)) /
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s, p s)‖ ≤ 1 := by
  filter_upwards [
    ProbeHighRowFamily.sourceMoment_separation_eventually G.ell G.slots_injective,
    ProbeHighRowFamily.sourceMoment_capacity_eventually G.ell
      (fun s => (G.slots_bounds s).1.le) εg hεg,
    ProbeHighRowFamily.sourceMoment_fiber_large_eventually
      F.modulus ⊤ le_top F.S F.exclusions.prime η
      G.ell (fun s => (G.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1, ?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
    bin j J K hne
  have hprofile : B.profile = (fun _ => (F.W : ℝ → ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0 < d := by linarith
  have hu : 0 < Z ^ d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths
    bin j J K hne
  dsimp only
  change (∀s t, s ≠ t → Disjoint
      (livePrimes F.modulus ⊤ (B.profile s) (B.upper s) ((Z ^ d) ^ (B.widths s)))
      (livePrimes F.modulus ⊤ (B.profile t) (B.upper t) ((Z ^ d) ^ (B.widths t)))) ∧ _
  refine ⟨?_, ?_⟩
  · intro s t hst
    rw [hprofile, hupper, hwidths]
    exact ProbeHighRowFamily.sourceMoment_live_disjoint F.modulus ⊤ F.core
      (fun s => G.ell s / d) (Z ^ d) hu s t (hs s t hst)
  · intro selected
    change (∀s : selected, 1 ≤ 2 * (Z ^ d) ^ (B.widths s)) ∧
      (∏s : selected, 2 * (Z ^ d) ^ (B.widths s)) ≤
        (Z ^ d) ^ ((∑s : selected, B.widths s) + εg) ∧ _
    refine ⟨?_, ?_, ?_⟩
    · rw [hwidths]
      exact fun s => hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p ∈ Fintype.piFinset (fun s : selected =>
          livePrimes F.modulus ⊤ F.W 2 ((Z ^ d) ^ (G.ell s / d))) := by
        change p ∈ Fintype.piFinset (fun s : selected =>
          livePrimes F.modulus ⊤ (B.profile s) (B.upper s) ((Z ^ d) ^ (B.widths s))) at hp
        simpa only [hprofile, hupper, hwidths] using hp
      have hl' : ∀s : selected,
          ((baseCharacter (B.data j)).modulus.absNorm : ℝ) <
            1 * (Z ^ d) ^ (G.ell s / d) := by
        intro s
        have hh := hl s
        change ((baseCharacter (B.data j)).modulus.absNorm : ℝ) <
          1 * (Z ^ d) ^ (B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t : selected, s ≠ t →
          2 * (Z ^ d) ^ (G.ell s / d) < 1 * (Z ^ d) ^ (G.ell t / d) ∨
          2 * (Z ^ d) ^ (G.ell t / d) < 1 * (Z ^ d) ^ (G.ell s / d) := by
        intro s t hst
        exact hs s t (fun he => hst (Subtype.ext he))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact live_tuple_injective F.modulus ⊤ (fun _ => F.W) (fun _ => 1) (fun _ => 2)
          (fun s : selected => G.ell s / d) (Z ^ d) hu
          (fun _ => F.complex_support) hs' p
          (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible F.modulus ⊤ (B.data j) (fun _ => F.W)
          (fun _ => 1) (fun _ => 2) (fun s : selected => G.ell s / d)
          (Z ^ d) hu (fun _ => F.complex_support) hl' hs' p
          (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm : ℝ) ≤ 2 * (Z ^ d) ^ (B.widths s)
        rw [hwidths]
        exact (livePrime_data F.modulus ⊤ F.W 1 2 ((Z ^ d) ^ (G.ell s / d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s)
          (Fintype.mem_piFinset.mp
            (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact ProbeHighRowFamily.sourceMoment_live_denominator F.modulus ⊤ F.core
          (B.data j) (Z ^ d) (fun s : selected => G.ell s / d) hu hl' p
          (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s : selected,
            primeProfile (B.profile s) ((Z ^ d) ^ (B.widths s))
              (B.external s) (p s)) /
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s : selected, p s)‖ ≤ 1
        rw [hprofile, hwidths]
        exact ProbeHighRowFamily.sourceMoment_live_quotient_norm F.modulus ⊤ F.core
          (B.data j) (Z ^ d) (fun s : selected => G.ell s / d)
          (fun s : selected => B.external s) hu (fun s => hz s) hl' p
          (by simpa only [Fintype.mem_piFinset] using hp')

/-! ### Retained plain energy with the actual perturbed slots. -/

theorem source_fibers_eventually_retained (G : MomentGeometry)
    (F : PerturbedSourceData G) (η : Character) :
    ∀ᶠZ : ℝ in atTop, ∀rows : Finset FreeRow,
      (∀u∈rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
      ∀(d a ε tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a ε tstar T allowance i), B.rows ⊆ rows →
      ∀bin label J K, ∀hne : (B.fiberRows bin label J K).Nonempty,
      let η₀ := sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal F.core) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional F.core η₀)) = ∅ := by
  filter_upwards [eventually_source_no_exceptional F.core η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk : ∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal F.core) η₀) u.val := by
    intro u hu
    apply (source_keep_iff F.core η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber, HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber, Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu, hex⟩ := Finset.mem_filter.mp hu
  exact ((source_keep_iff F.core η₀ u).mp (hk u hu)) hex

theorem source_batch_plain_retained (G : MomentGeometry)
    (F : PerturbedSourceData G) (η : Character) :
    ∀ᶠZ : ℝ in atTop, 1 < Z ∧ ∀rows : Finset FreeRow,
      (∀u∈rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
      ∀d : ℝ, d ≠ 0 → ∀(a ε tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a ε tstar T allowance i), B.rows ⊆ rows →
      B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
      B.profile = (fun _ x => (F.w x : ℂ)) →
      B.widths = (fun s => G.ell s / d) →
      ∀bin label J K, ∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin G.N), ∀j k : ℕ, ∀σ t : ℝ,
      let f := B.fiber bin label J K hne
      let η₀ := sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∑u∈f.rows, ‖polynomial (f.family u f.label) false
        ((logProfile^[j]) positiveAnnular) ((Z ^ d) ^ f.m) σ t *
        polynomial (f.family u f.label) false ((logProfile^[k]) positiveAnnular)
          ((Z ^ d) ^ f.m) σ t * f.physicalProduct selected u‖ ^ 2) ≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal F.core) η₀))
          f η₀ selected j k σ t radialMajorant := by
  filter_upwards [source_fibers_eventually_retained G F η,
    eventually_source_slots_coprime F.modulus ⊤ le_top F.S F.exclusions.prime η
      G.ell (fun s => (G.slots_bounds s).1) 1 (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with Z hret hcop hZ
  refine ⟨hZ, ?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t f η₀
  have hU : 0 < Z ^ d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF : f.rowData = momentData η₀ := by
    change B.data label = momentData η₀
    rw [hdata, sourceMomentData_base]
  have hMm : F.modulus ≤ Ideal.span {rowMaskElement} :=
    source_product_le_rowMask F.S F.exclusions.bad
  have hη : ∀s∈selected, ∀I∈primePool F.modulus ⊤ (f.upper s)
      ((Z ^ d) ^ (f.widths s)),
      f.profile s ((I.absNorm : ℝ) / ((Z ^ d) ^ (f.widths s))) ≠ 0 →
        IsCoprime I η₀.modulus := by
    intro s hs I hI hn
    change I ∈ primePool F.modulus ⊤ (B.upper s) ((Z ^ d) ^ (B.widths s)) at hI
    change B.profile s ((I.absNorm : ℝ) / ((Z ^ d) ^ (B.widths s))) ≠ 0 at hn
    rw [hwidth] at hI
    rw [hwidth, hprofile] at hn
    exact hcop label s d hd (fun x => (F.w x : ℂ)) (B.upper s)
      (by
        intro x hx
        have hn' : F.w x ≠ 0 := by simpa using hx
        exact (F.support hn').1.le) I hI hn
  rw [fiber_plain_energy_eq f η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg
    radialMajorant_one f η₀ selected j k σ t hU
    (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

/-! ### Initial marked state and inverse-marked field. -/

theorem source_batch_marked_initial (G : MomentGeometry)
    (F : PerturbedSourceData G) :
    ∃bΦ : ℝ, 0 < bΦ ∧ ∀η : Character, ∀δ : ℝ, 0 < δ →
      ∀ᶠZ : ℝ in atTop, 1 < Z ∧ ∀rows : Finset FreeRow,
      (∀u∈rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
      ∀d : ℝ, (1 / 200 : ℝ) ≤ d → ∀(a ε tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a ε tstar T allowance i), B.rows ⊆ rows →
      B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
      B.profile = (fun _ x => (F.w x : ℂ)) → B.widths = (fun s => G.ell s / d) →
      (∀s, B.upper s = 2) → (∀s, (B.external s).re = 17 / 50) →
      ∀bin label J K, ∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin G.N), selected ⊆ B.slots →
      let f := B.fiber bin label J K hne
      2 * f.m + 6 * momentKappa * (∑s∈selected, f.widths s) ≤ 1 →
      let η₀ := sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ∃state : NaturalState (Z ^ d) 0 bΦ,
        state.character = η₀ ∧
        state.fixedModulus = internalQ (sourceFixedIdeal F.core) η₀ ∧
        state.puncture = 1 ∧ state.radial.profile = radialMajorant ∧
        state.radial.scale = Z ^ d ∧
        state.radial.keep = initialKeep η₀ (internalQ (sourceFixedIdeal F.core) η₀) ∧
        state.width = 1 + δ ∧
        length (Z ^ d) ((Z ^ d) ^ f.m) + length (Z ^ d) ((Z ^ d) ^ f.m) +
          6 * momentKappa * (∑s : selected, f.widths s.val) ≤ state.width ∧
        (∀s : selected, 0 < f.widths s.val ∧ f.widths s.val ≤ f.mesh) ∧
        ∀j k : ℕ, ∀σ t : ℝ,
        (∑u∈f.rows, ‖polynomial (f.family u f.label) false
          ((logProfile^[j]) positiveAnnular) ((Z ^ d) ^ f.m) σ t *
          polynomial (f.family u f.label) false ((logProfile^[k]) positiveAnnular)
            ((Z ^ d) ^ f.m) σ t * f.physicalProduct selected u‖ ^ 2) ≤
          energy state.character state.mask 1 0
            ((detectorProfiles f.reverse j k σ t).profile 0)
            ((detectorProfiles f.reverse j k σ t).profile 1)
            (fun s : selected => CenteredMomentPrimeSlot.primePool
              F.modulus ⊤ 2 ((Z ^ d) ^ (f.widths s.val)))
            (fun (s : selected) I => idealCoeff η₀.inverse I *
              HeckePrimeAnnular.annularWeight (fun x => conj (F.W x))
                ((Z ^ d) ^ (f.widths s.val)) (33 / 50)
                (-(f.external s.val).im) I)
            (fun s : selected => (Z ^ d) ^ (f.widths s.val))
            ((Z ^ d) ^ f.m) ((Z ^ d) ^ f.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ, hbΦ, hs⟩ := radialMajorant_support_bound
  refine ⟨bΦ, hbΦ, ?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually F.core η δ hδ,
    source_batch_plain_retained G F η] with Z hz hr
  refine ⟨hz.1, ?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    hupper hreal bin label J K hne selected hselected f hcap η₀
  have hdpos : 0 < d := by linarith
  have hU : 1 < Z ^ d := Real.one_lt_rpow hz.1 hdpos
  have hη : (η₀.modulus.absNorm : ℝ) ≤ (Z ^ d) ^ δ := hz.2 label d hd
  let state := initialState η₀ (internalQ (sourceFixedIdeal F.core) η₀)
    radialMajorant bΦ (Z ^ d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact CenteredMomentDetectorPlainMarkedState.marked_capacity
      f hU selected momentKappa δ hδ.le hcap
  · intro s
    exact ⟨f.widths_pos s.val (hselected s.property),
      f.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb := hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB
      hdata hprofile hwidth bin label J K hne selected j k σ t
    have hprof : ∀s x, f.profile s x = F.W x := by
      intro s x
      change B.profile s x = F.W x
      rw [hprofile, F.complex_eq]
    have he := CenteredMomentDetectorPlainMarkedState.retained_eq_initial_energy
      F.core f hprof hupper η₀ (internalQ (sourceFixedIdeal F.core) η₀)
      selected (fun s _ => hreal s) radialMajorant bΦ δ hU.le hδ.le hs
      radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

theorem source_batch_inverse_marked (G : MomentGeometry)
    (F : PerturbedSourceData G) :
    ∃J : ℕ, ∀η : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
    1 < Z ∧ ∀d : ℝ, (1 / 200 : ℝ) ≤ d →
    ∀(a ε tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a ε tstar T allowance i),
      B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
      B.profile = (fun _ x => (F.w x : ℂ)) → B.upper = (fun _ => 2) →
      B.widths = (fun s => G.ell s / d) → (∀s, (B.external s).re = 17 / 50) →
    ∀bin label left right, ∀hne : (B.fiberRows bin label left right).Nonempty,
    ∀height : ℝ, 0 ≤ height →
    let f := B.fiber bin label left right hne
    ∀selected : Finset (Fin G.N), selected ⊆ f.slots →
      f.r + 2 * (∑s∈selected, f.widths s) < 1 →
      2 * f.r + 8 * (∑s∈selected, f.widths s) < 3 →
    ∀n : ℕ, n ≤ 2 → ∀s∈Set.Icc (0 : ℝ) 1, ∀t∈Set.Icc (-height) height,
      (∑u∈f.rows, ‖polynomial (f.family u f.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) f.inverseProfile)
        ((Z ^ d) ^ f.r) s t * f.physicalProduct selected u‖ ^ 2) ≤
        (C * (1 + height) ^ J) * (Z ^ d) ^ (1 + G.t) := by
  obtain ⟨Jref, hreference⟩ := fiber_reference_energy F.core referenceWindow
    (1 / 18) (13 / 4) (by norm_num) (by norm_num)
    (fun x hx => referenceWindow_support (subset_tsupport _ hx))
    (referenceWindow.smooth ⊤) G.t G.t_pos G.N
  obtain ⟨J, Cfourier, hCfourier, hfourier⟩ :=
    DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨J, ?_⟩
  intro η
  let data := sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η
  choose C U₀ hC hU₀ hb using fun label => hreference (data label)
  let Csum : ℝ := 1 + ∑label, C label
  have hCsum : 0 < Csum := by
    have hh := Finset.sum_nonneg (fun label (_ : label ∈ Finset.univ) => (hC label).le)
    dsimp [Csum]
    linarith
  have hClabel (label) : C label ≤ Csum := by
    have hh := Finset.single_le_sum
      (fun label (_ : label ∈ Finset.univ) => (hC label).le) (Finset.mem_univ label)
    dsimp [Csum]
    linarith
  have hscale : ∀ᶠZ : ℝ in atTop, ∀label, ∀d : ℝ,
      (1 / 200 : ℝ) ≤ d → U₀ label ≤ Z ^ d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold
      (1 / 200) (U₀ label) (by norm_num)
  refine ⟨Cfourier * Csum, mul_pos hCfourier hCsum, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), hscale,
    deleted_large_eventually data G.ell (fun s => (G.slots_bounds s).1),
    sourceMoment_fiber_prime_geometry_eventually G F η G.t G.t_pos]
    with Z hZ hscale hlarge hgeom
  refine ⟨hZ, ?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
    bin label left right hne height hheight f selected hselected hfirst hsecond
    n hn s hs t ht
  have hd0 : 0 < d := by linarith
  have hUone : 1 < Z ^ d := Real.one_lt_rpow hZ hd0
  have hUp : 0 < Z ^ d := zero_lt_one.trans hUone
  have hprofile : B.profile = (fun _ => (F.W : ℝ → ℂ)) := by
    rw [hprofile0]
    funext j x
    exact (F.complex_eq x).symm
  have hfd : f.rowData = data label := by
    change B.data label = data label
    rw [hdata]
  have hfp (j) : f.profile j = F.W := by
    change B.profile j = F.W
    rw [hprofile]
  have hfu (j) : f.upper j = 2 := by
    change B.upper j = 2
    rw [hupper]
  have hfw (j) : f.widths j = G.ell j / d := by
    change B.widths j = _
    rw [hwidths]
  have hfe (j) : (f.external j).re ≤ 1 := by
    change (B.external j).re ≤ 1
    rw [hz j]
    norm_num
  have hdis : ((Finset.univ : Finset selected) : Set selected).PairwiseDisjoint
      (fiberLists f selected) := by
    intro j hj k hk hjk
    exact (hgeom.2 d hd a ε tstar T allowance i B hdata hprofile0 hupper
      hwidths hz bin label left right hne).1 j k
      (fun he => hjk (Subtype.ext he))
  have hlargeF : ∀j∈selected,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm : ℝ) <
        (Z ^ d) ^ (f.widths j) := by
    intro j hj
    rw [hfw]
    exact hlarge.2 d hd0 label j
  have hr : 0 ≤ f.r :=
    Real.logb_nonneg hUone (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have href (v : ℝ) :
      (∑u∈f.rows, ‖polynomial (f.family u f.label) true
        (childLogTest referenceWindow v) ((Z ^ d) ^ f.r) 0 0 *
        f.physicalProduct selected u‖ ^ 2) ≤
      (Csum * (Z ^ d) ^ (1 + G.t)) * (1 + ‖v‖) ^ (2 * Jref) := by
    have hh := hb label (Z ^ d) (hscale label d hd) F.modulus ⊤ f selected hfd
      (by simpa using Finset.card_le_univ selected) (fun j _ => hfp j)
      (fun j _ => hfu j) (fun j hj => (f.widths_pos j (hselected hj)).le)
      (fun j _ => hfe j) hdis hlargeF hr hfirst hsecond v
    rw [(show 2 * Jref = Jref * 2 by omega), pow_mul]
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hClabel label)
      (Real.rpow_nonneg hUp.le _)
  have hh := hfourier f selected hUp (Csum * (Z ^ d) ^ (1 + G.t))
    (by positivity) href n hn s hs height t hheight ht
  convert hh using 1 <;> ring

/-! ### Plain marked field, preserving the coefficient `6`. -/

theorem source_batch_plain_marked_fine (G : MomentGeometry)
    (F : PerturbedSourceData G) (mesh : ℝ) (hmesh : 0 < mesh)
    (hfine : ∀j, G.ell j ≤ mesh / 200)
    (henergy : PositiveFineSourceInput G F mesh) :
    ∃J : ℕ, ∀η : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
    1 < Z ∧ ∀rows : Finset FreeRow,
    (∀u∈rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
    ∀d : ℝ, (1 / 200 : ℝ) ≤ d → ∀(a tstar T allowance : ℝ) (i : ℕ)
    (B : Batch F.modulus ⊤
      (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
      (Z ^ d) a G.ε tstar T allowance i), B.rows ⊆ rows →
    B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
    B.profile = (fun _ x => (F.w x : ℂ)) →
    B.widths = (fun s => G.ell s / d) →
    (∀s, B.upper s = 2) → (∀s, (B.external s).re = 17 / 50) →
    ∀bin label left right, ∀hne : (B.fiberRows bin label left right).Nonempty,
    ∀height : ℝ, 0 ≤ height → (∀s, |(B.external s).im| ≤ height) →
    let f := B.fiber bin label left right hne
    ∀selected : Finset (Fin G.N), selected ⊆ f.slots →
      2 * f.m + 6 * momentKappa * (∑s∈selected, f.widths s) ≤ 1 →
    ∀j k : ℕ, j + k ≤ 2 → ∀σ∈Set.Icc (0 : ℝ) 1,
    ∀t∈Set.Icc (-height) height,
      (∑u∈f.rows, ‖polynomial (f.family u f.label) false
        ((logProfile^[j]) positiveAnnular) ((Z ^ d) ^ f.m) σ t *
        polynomial (f.family u f.label) false ((logProfile^[k]) positiveAnnular)
          ((Z ^ d) ^ f.m) σ t * f.physicalProduct selected u‖ ^ 2) ≤
        (C * (1 + height) ^ J) * (Z ^ d) ^ (1 + G.t) := by
  obtain ⟨bΦ, hbΦ, hsource⟩ := source_batch_marked_initial G F
  obtain ⟨degree, seminorms, henergy⟩ := henergy bΦ hbΦ
  obtain ⟨J, Cprofile, hCprofile, hprofile⟩ :=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J + degree, ?_⟩
  intro η
  let data := sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η
  choose C hC hbound using fun label => henergy (data label)
  choose U₀ hU₀ using fun label => Filter.eventually_atTop.mp (hbound label)
  let Csum : ℝ := 1 + ∑label, C label
  have hCsum : 0 < Csum := by
    have h := Finset.sum_nonneg (fun label (_ : label ∈ Finset.univ) => (hC label).le)
    dsimp [Csum]
    linarith
  have hClabel (label) : C label ≤ Csum := by
    have h := Finset.single_le_sum
      (fun label (_ : label ∈ Finset.univ) => (hC label).le) (Finset.mem_univ label)
    dsimp [Csum]
    linarith
  have hscale : ∀ᶠZ : ℝ in atTop, ∀label, ∀d : ℝ,
      (1 / 200 : ℝ) ≤ d → U₀ label ≤ Z ^ d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold
      (1 / 200) (U₀ label) (by norm_num)
  let Cfinal := Csum * (1 + diagonalControl radialMajorant) * Cprofile
  have hdiag : 0 ≤ diagonalControl radialMajorant := diagonalControl_nonneg _
  refine ⟨Cfinal, by dsimp [Cfinal]; positivity, ?_⟩
  filter_upwards [hsource η (initialDelta G.t) (initialDelta_pos G), hscale]
    with Z hs hscale
  refine ⟨hs.1, ?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth
    hupper hreal bin label left right hne height hheight hexternal f
    selected hselected hcap j k hjk σ hσ t ht
  have hU : 1 < Z ^ d := source_base_gt_one G Z d hs.1 hd
  obtain ⟨state, hchar, hQ, hpuncture, hΦ, hK, hkeep, hwidthstate,
    hcapacity, hwidths, hrow⟩ :=
    hs.2 rows hrows d hd a G.ε tstar T allowance i B hB hdata hprof hwidth
      hupper hreal bin label left right hne selected hselected hcap
  have hf := actual_fiber_lengths G f hU
  have hstate : state.width ≤ 2 := by
    rw [hwidthstate]
    exact (width_bands G f.m hf.2.2.1).2.1
  have hw (s : selected) : 0 ≤ f.widths s.val := (hwidths s).1.le
  have hwcap (s : selected) : f.widths s.val ≤ mesh := by
    change B.widths s.val ≤ mesh
    rw [hwidth]
    have hdpos : 0 < d := by linarith
    apply (div_le_iff₀ hdpos).mpr
    have hm : mesh * (1 / 200 : ℝ) ≤ mesh * d :=
      mul_le_mul_of_nonneg_left hd hmesh.le
    have hslt := hfine s.val
    nlinarith
  have hpos := hU₀ label (Z ^ d) (hscale label d hd) selected (fun _ => 1)
    (fun s => f.widths s.val) (fun _ => (33 / 50 : ℝ))
    (fun s => -(f.external s.val).im) 0 height hw hwcap
    (fun _ => le_rfl) (fun _ => le_rfl) hheight
    (fun s => by
      change |-(B.external s.val).im| ≤ height
      simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (detectorProfiles f.reverse j k σ t)
    ((Z ^ d) ^ f.m) ((Z ^ d) ^ f.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1) hcapacity
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq
    F.modulus ⊤ le_top state.character (data label)
    (fun (_ : selected) => 1) state.mask 1
    ((detectorProfiles f.reverse j k σ t).profile 0)
    ((detectorProfiles f.reverse j k σ t).profile 1)
    (fun _ => 2) (fun s : selected => (Z ^ d) ^ (f.widths s.val))
    (fun s I => HeckePrimeAnnular.annularWeight (fun x => conj (F.W x))
      ((Z ^ d) ^ (f.widths s.val)) (33 / 50) (-(f.external s.val).im) I)
    0 ((Z ^ d) ^ f.m) ((Z ^ d) ^ f.m)
    state.radial.keep state.radial.profile state.radial.scale
  have hnorm := hprofile degree f.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp : 0 ≤ (detectorProfiles f.reverse j k σ t).control seminorms ^ 2 :=
    sq_nonneg _
  have hexp : state.width + stageError G.t ≤ 1 + G.t := by
    rw [hwidthstate]
    linarith [stage_budget G]
  calc
    _ ≤ _ := hrow j k σ t
    _ ≤ C label * diagonalControl state.radial.profile *
        (detectorProfiles f.reverse j k σ t).control seminorms ^ 2 *
        (1 + |(0 : ℝ)| + height) ^ degree *
        (Z ^ d) ^ (state.width + stageError G.t) := by
      exact heq.le.trans hpos
    _ ≤ (Cfinal * (1 + height) ^ (J + degree)) *
        (Z ^ d) ^ (1 + G.t) := by
      rw [hΦ]
      have hpow := Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _ = (C label * diagonalControl radialMajorant) *
          ((detectorProfiles f.reverse j k σ t).control seminorms ^ 2 *
            (1 + |(0 : ℝ)| + height) ^ degree) *
          (Z ^ d) ^ (state.width + stageError G.t) := by ring
        _ ≤ (Csum * (1 + diagonalControl radialMajorant)) *
          (Cprofile * (1 + height) ^ (J + degree)) *
          (Z ^ d) ^ (1 + G.t) := by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
            (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _ = _ := by dsimp [Cfinal]; ring


/-! ### Plain unmarked field. -/

theorem retained_unmarked_bound (G : MomentGeometry)
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label : Type*}
    {U a tstar T heightAllowance : ℝ} {i : ℕ}
    (f : Fiber M H Label (Fin G.N) U a G.ε tstar T heightAllowance i)
    (η : Character) (Q : Ideal O) (hU : 1 < U)
    (hη : (η.modulus.absNorm : ℝ) ≤ U ^ (initialDelta G.t))
    (degree : ℕ) (control : Finset (ℕ × ℕ)) (A : ℝ)
    (hzero : ZeroAt Q (1 / 4) (9 / 4)
      ProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2
      (stageError G.t) U degree control A)
    (j k : ℕ) (σ t : ℝ) :
    retainedSourceEnergy (initialKeep η Q) f η ∅ j k σ t radialMajorant ≤
      A * diagonalControl radialMajorant *
        (detectorProfiles f.reverse j k σ t).control control ^ 2 *
        U ^ (max 1 (2 * f.m) + initialDelta G.t + stageError G.t) := by
  let s := CenteredMomentDetectorPlainUnmarkedState.state f η Q radialMajorant
    ProbeDetectorPlainUnmarkedField.radialSupportUpper (initialDelta G.t) hU.le
    (initialDelta_pos G).le ProbeDetectorPlainUnmarkedField.radialSupportUpper_spec.2
    radialMajorant_nonneg hη
  have hs := unmarked_state_admission G f η Q radialMajorant
    ProbeDetectorPlainUnmarkedField.radialSupportUpper hU
    ProbeDetectorPlainUnmarkedField.radialSupportUpper_spec.2
    radialMajorant_nonneg hη
  have hwidth : s.width = max 1 (2 * f.m) + initialDelta G.t :=
    hs.2.2.2.2.2.2.1
  have hband : s.width ≤ 2 := hs.2.2.2.2.2.2.2.2.1
  have hscale : 1 ≤ U ^ f.m ∧ U ^ f.m ≤ U :=
    ⟨hs.2.2.2.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz := hzero s rfl hband (detectorProfiles f.reverse j k σ t)
    0 (U ^ f.m) (U ^ f.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  rw [CenteredMomentDetectorPlainUnmarkedState.actual_source_eq f η Q radialMajorant
    ProbeDetectorPlainUnmarkedField.radialSupportUpper (initialDelta G.t) hU.le
    (initialDelta_pos G).le ProbeDetectorPlainUnmarkedField.radialSupportUpper_spec.2
    radialMajorant_nonneg hη j k σ t]
  have hrad : s.radial.profile = radialMajorant := rfl
  simpa only [hwidth, hrad, norm_zero, add_zero, one_pow, mul_one] using hz

theorem source_batch_plain_unmarked (G : MomentGeometry)
    (F : PerturbedSourceData G) (henergy : ZeroSourceInput G F) :
    ∃Jheight : ℕ, ∀η : Character, ∃C : ℝ, 0 < C ∧
    ∀ᶠZ : ℝ in atTop, 1 < Z ∧ ∀rows : Finset FreeRow,
      (∀u∈rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
      ∀d : ℝ, (1 / 200 : ℝ) ≤ d → ∀(a tstar T heightAllowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a G.ε tstar T heightAllowance i), B.rows ⊆ rows →
      B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
      B.profile = (fun _ x => (F.w x : ℂ)) →
      B.widths = (fun s => G.ell s / d) →
      ∀bin label left right, ∀hne : (B.fiberRows bin label left right).Nonempty,
      ∀height : ℝ, 0 ≤ height → ∀j k : ℕ, j + k ≤ 2 →
      ∀σ∈Set.Icc (0 : ℝ) 1, ∀t∈Set.Icc (-height) height,
      let f := B.fiber bin label left right hne
      let value := ∑u∈f.rows, ‖polynomial (f.family u f.label) false
        ((logProfile^[j]) positiveAnnular) ((Z ^ d) ^ f.m) σ t *
        polynomial (f.family u f.label) false ((logProfile^[k]) positiveAnnular)
          ((Z ^ d) ^ f.m) σ t‖ ^ 2
      value ≤ C * (1 + height) ^ Jheight *
        (Z ^ d) ^ (max 1 (2 * f.m) + G.t) ∧
      value ≤ C * (1 + height) ^ Jheight *
        max (Z ^ d) (((Z ^ d) ^ f.m) ^ 2) * (Z ^ d) ^ G.t := by
  obtain ⟨degree, control, henergy⟩ := henergy
  obtain ⟨Jheight, Cp, hCp, hprofiles⟩ := paired_control control
  refine ⟨Jheight, ?_⟩
  intro η
  letI : Fintype (Sum Bool (RayQuotient.Characters F.modulus ⊤)) := Fintype.ofFinite _
  let η₀ := fun label =>
    sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  let Q := fun label => internalQ (sourceFixedIdeal F.core) (η₀ label)
  choose A hA hzero using fun label => henergy (η₀ label)
  let Amax : ℝ := 1 + ∑label, A label
  have hsum : 0 ≤ ∑label, A label :=
    Finset.sum_nonneg (fun j _ => (hA j).le)
  have hAmax : 0 < Amax := by
    dsimp [Amax]
    linarith
  have hA_bound (label) : A label ≤ Amax := by
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => (hA j).le) (Finset.mem_univ label)
    dsimp [Amax]
    linarith
  let C := Amax * (1 + diagonalControl radialMajorant) * Cp
  have hdiag : 0 ≤ diagonalControl radialMajorant := diagonalControl_nonneg _
  have hC : 0 < C := mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label) :
      A label * diagonalControl radialMajorant * Cp ≤ C := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales : ∀ᶠZ : ℝ in atTop, ∀label, ∀d : ℝ,
      (1 / 200 : ℝ) ≤ d →
      ZeroAt (Q label) (1 / 4) (9 / 4)
        ProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2
        (stageError G.t) (Z ^ d) degree control (A label) := by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold
      (1 / 200) U₀ (by norm_num)] with Z hz
    intro d hd
    exact hU₀ (Z ^ d) (hz d hd)
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_batch_plain_retained G F η,
    source_label_fixed_allowance G F η, hscales] with Z hret hmod hscales
  refine ⟨hret.1, ?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht f value
  have hU : 1 < Z ^ d := source_base_gt_one G Z d hret.1 hd
  have hnorm : ‖t‖ ≤ height := by
    simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp :
      (detectorProfiles f.reverse j k σ t).control control ^ 2 ≤
        Cp * (1 + height) ^ Jheight := by
    apply (hprofiles f.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare :
      value ≤ retainedSourceEnergy (initialKeep (η₀ label) (Q label))
        f (η₀ label) ∅ j k σ t radialMajorant := by
    simpa only [Fiber.physicalProduct, Finset.prod_empty, mul_one] using
      hret.2 rows hrows d (by linarith) a G.ε tstar T heightAllowance i B hB
        hdata hprofile hwidth bin label left right hne ∅ j k σ t
  have hb := retained_unmarked_bound G f (η₀ label) (Q label) hU
    (hmod.2 label d hd) degree control (A label) (hscales label d hd) j k σ t
  have hpow :
      (Z ^ d) ^ (max 1 (2 * f.m) + initialDelta G.t + stageError G.t) ≤
        (Z ^ d) ^ (max 1 (2 * f.m) + G.t) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget G _)
  have hfinal :
      value ≤ C * (1 + height) ^ Jheight *
        (Z ^ d) ^ (max 1 (2 * f.m) + G.t) := by
    apply hcompare.trans (hb.trans ?_)
    calc
      _ ≤ (A label * diagonalControl radialMajorant *
          (Cp * (1 + height) ^ Jheight)) *
          (Z ^ d) ^ (max 1 (2 * f.m) + G.t) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp
            (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _ = (A label * diagonalControl radialMajorant * Cp) *
          (1 + height) ^ Jheight *
          (Z ^ d) ^ (max 1 (2 * f.m) + G.t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal, ?_⟩
  simpa only [ProbeDetectorPlainUnmarkedField.unmarked_power_eq _ _ _ hU.le,
    mul_assoc] using hfinal

/-! ### Inverse raw plus inverse marked fields. -/

private lemma raw_mono (data : RowData) (W : ℝ → ℂ) (c κ A B : ℝ)
    (hAB : A ≤ B) (h : RawMoment data W c κ A) : RawMoment data W c κ B := by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem source_batch_inverse_fields (G : MomentGeometry)
    (F : PerturbedSourceData G) (counts : CountParameters F.modulus ⊤ G.t) :
    ∃J : ℕ, ∀η : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
    1 < Z ∧ ∀d : ℝ, (1 / 200 : ℝ) ≤ d →
    ∀(a ε tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin G.N)
        (Z ^ d) a ε tstar T allowance i),
      B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
      B.profile = (fun _ x => (F.w x : ℂ)) → B.upper = (fun _ => 2) →
      B.widths = (fun s => G.ell s / d) →
      (∀s, (B.external s).re = 17 / 50) →
    ∀bin label left right, ∀hne : (B.fiberRows bin label left right).Nonempty,
    ∀height : ℝ, 0 ≤ height →
    let f := B.fiber bin label left right hne
    (∀n : ℕ, n ≤ 2 → ∀s∈Set.Icc (0 : ℝ) 1,
      ∀t∈Set.Icc (-height) height,
      let W := twistProfile (logTest (orientedProfile f.reverse f.inverseProfile) n) s t
      RawMoment f.rowData W
        (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
        (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
        (C * (1 + height) ^ J) ∧
      RawMoment f.rowData (scaleProfile W)
        (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
        (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
        (C * (1 + height) ^ J)) ∧
    (∀selected : Finset (Fin G.N), selected ⊆ f.slots →
      f.r + 2 * (∑s∈selected, f.widths s) < 1 →
      2 * f.r + 8 * (∑s∈selected, f.widths s) < 3 →
      ∀n : ℕ, n ≤ 2 → ∀s∈Set.Icc (0 : ℝ) 1,
      ∀t∈Set.Icc (-height) height,
      (∑u∈f.rows, ‖polynomial (f.family u f.label) true
        ((logProfile^[n]) f.inverseProfile) ((Z ^ d) ^ f.r) s t *
        f.physicalProduct selected u‖ ^ 2) ≤
        (C * (1 + height) ^ J) * (Z ^ d) ^ (1 + G.t)) := by
  obtain ⟨Jr, hr⟩ := ProbeDetectorInverseRawField.source_batch_inverse_raw
    F.modulus ⊤ le_top F.S F.exclusions.prime G.t counts
  obtain ⟨Jm, hm⟩ := source_batch_inverse_marked G F
  refine ⟨Jr + Jm, ?_⟩
  intro η
  obtain ⟨Cr, hCr, hr⟩ := hr η
  obtain ⟨Cm, hCm, hm⟩ := hm η
  refine ⟨Cr + Cm, add_pos hCr hCm, ?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight f
  have hU : 0 < Z ^ d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale : 1 ≤ 1 + height := by linarith
  have hraw :
      Cr * (1 + height) ^ Jr ≤
        (Cr + Cm) * (1 + height) ^ (Jr + Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked :
      Cm * (1 + height) ^ Jm ≤
        (Cr + Cm) * (1 + height) ^ (Jr + Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh := hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono _ _ _ _ _ _ hraw hh.1,
      raw_mono _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh := hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper
      hwidths hex bin label left right hne height hheight selected hselected
      hfirst hsecond n hn s hs t ht
    exact hh.trans
      (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

/-! ### Assembly of all four `Moments` fields into `SourceMomentsAt`. -/

lemma SourceMomentBoundAt.mono_constant
    {N : ℕ} {M : Ideal O} [NeZero M] [Finite (O ⧸ M)]
    {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {S : Finset (Ideal O)} {hS : SourceExclusions S}
    {hmax : ∀P∈S, P.IsMaximal} {ell : Fin N → ℝ} {W : Fin N → ℝ → ℝ}
    {dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM : ℝ}
    {counts : CountParameters M H epsilonM} {η : Character}
    {Z theta C D height : ℝ}
    (hZ : 0 ≤ Z)
    (h : SourceMomentBoundAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM
      counts η Z theta C height)
    (hCD : C ≤ D) :
    SourceMomentBoundAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM
      counts η Z theta D height := by
  intro rows d a hd hdmax ha hamax hrows i z hz hzim
  exact ProbeFinalAssembly.sourceMomentsAt_mono_constant M H hH S hS.prime η
    rows ell (fun j y => (W j y : ℂ)) Z d a epsilon theta dmax b
    slotMesh binWidth i z gamma
    (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
    (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
    C D height epsilonM hZ hCD
    (h rows d a hd hdmax ha hamax hrows i z hz hzim)

theorem source_moments (G : MomentGeometry) (F : PerturbedSourceData G)
    (counts : CountParameters F.modulus ⊤ G.t)
    (hpositive : PositiveFineSourceInput G F (detectorMesh G.t))
    (hzero : ZeroSourceInput G F) :
    HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
      G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
      momentGamma G.t counts := by
  obtain ⟨Ji, hi⟩ := source_batch_inverse_fields G F counts
  obtain ⟨Jm, hm⟩ := source_batch_plain_marked_fine G F
    (detectorMesh G.t) (detectorMesh_pos G) G.fine_slots hpositive
  obtain ⟨Ju, hu⟩ := source_batch_plain_unmarked G F hzero
  refine ⟨(Ji + Jm + Ju : ℕ), by positivity, ?_⟩
  intro η
  obtain ⟨Ci, hCi, hi⟩ := hi η
  obtain ⟨Cm, hCm, hm⟩ := hm η
  obtain ⟨Cu, hCu, hu⟩ := hu η
  refine ⟨Ci + Cm + Cu, by positivity, ?_⟩
  intro theta htheta htheta1
  filter_upwards [hi, hm, hu] with Z hi hm hu
  have hZ : 0 < Z := zero_lt_one.trans hi.1
  let height : ℝ := Z ^ (2 * theta)
  have hh : 0 ≤ height := Real.rpow_nonneg hZ.le _
  have hbase : 1 ≤ 1 + height := by linarith
  have hCi' :
      Ci * (1 + height) ^ Ji ≤
        (Ci + Cm + Cu) * (1 + height) ^ (Ji + Jm + Ju) := by
    apply mul_le_mul (by linarith)
      (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm' :
      Cm * (1 + height) ^ Jm ≤
        (Ci + Cm + Cu) * (1 + height) ^ (Ji + Jm + Ju) := by
    apply mul_le_mul (by linarith)
      (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu' :
      Cu * (1 + height) ^ Ju ≤
        (Ci + Cm + Cu) * (1 + height) ^ (Ji + Jm + Ju) := by
    apply mul_le_mul (by linarith)
      (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim
  intro q B hB hdata hreverse hslots hwidth hprofile hupper hexternal
    hslotMesh hbinWidth hfamily bin label left right hne
  have hrows' : ∀u∈rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u :=
    fun u hu => (hrows u hu).2.1
  have hext : ∀s, (B.external s).re = 17 / 50 := by
    intro s
    rw [hexternal]
    exact hz
  have hheight : ∀s, |(B.external s).im| ≤ height := by
    intro s
    rw [hexternal]
    exact hzim
  have hinv := hi.2 d hd a G.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked := hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s => by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked := hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU : 0 ≤ Z ^ d := Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨ProbeFinalAssembly.rawMoment_mono_constant
      (hinv.1 n hn σ hσ t ht).1 hCi',
      ProbeFinalAssembly.rawMoment_mono_constant
        (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

/-- Terminal certificate through all four moment fields, with no assumed moment input. -/
theorem high_joint_moments
    (hβ : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (G : MomentGeometry) (F : PerturbedSourceData G)
    (counts : CountParameters F.modulus ⊤ G.t) :
    HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
      G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
      momentGamma G.t counts := by
  obtain ⟨hpositive, hzero⟩ := terminal_inputs hβ G F
  exact source_moments G F counts hpositive hzero

/-- Construct the actual fixed source, count constants, terminal certificate, and all four moments. -/
theorem exists_source_counts_and_moments
    (hβ : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    (G : MomentGeometry) :
    ∃F : PerturbedSourceData G, ∃counts : CountParameters F.modulus ⊤ G.t,
      HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
        G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
        momentGamma G.t counts := by
  obtain ⟨F⟩ := exists_perturbed_source_data G
  obtain ⟨counts⟩ := source_count_parameters G F
  exact ⟨F, counts, high_joint_moments hβ G F counts⟩

/-- Choose height only after the target-independent polynomial degree `J`. -/
theorem chosen_height
    (G : MomentGeometry) (F : PerturbedSourceData G)
    (counts : CountParameters F.modulus ⊤ G.t)
    (hmom : HighJointMomentOutputAt F.modulus ⊤ le_top F.S F.exclusions
      F.maximal G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε
      G.t G.t G.t momentGamma G.t counts) :
    ∃theta : ℝ, 0 < theta ∧ theta < (1 / 200 : ℝ) / 2 ∧
      4 * theta < (1 / 200 : ℝ) * G.cost ∧ theta < G.t ∧
      2 * theta ≤ G.t ∧ theta * (2 + 4 * G.eps) < G.t ∧
      ∀η : Character, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBoundAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
          G.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 G.ε G.t G.t G.t
          momentGamma G.t counts η Z theta (C * Z ^ G.t) (Z ^ (2 * theta)) := by
  obtain ⟨J, hJ, hbound⟩ := hmom
  obtain ⟨theta, htheta, hthetad, hthetacost, hthetat, hthetaJ, hthetaeps⟩ :=
    G.height_choice J hJ
  have htheta1 : theta ≤ 1 := by linarith
  refine ⟨theta, htheta, hthetad, hthetacost, hthetat,
    by nlinarith, hthetaeps, ?_⟩
  intro η
  obtain ⟨C, hC, hbound⟩ := hbound η
  refine ⟨C * 2 ^ J, by positivity, ?_⟩
  filter_upwards [hbound theta htheta htheta1,
    eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  exact SourceMomentBoundAt.mono_constant (by linarith) hb
    (ProbeFinalAssembly.polynomial_height_absorption C Z theta J G.t
      hC.le hZ htheta.le hJ hthetaJ)

end SevenEighths.PerturbedMomentConstruction

end

end OAI
