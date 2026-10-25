/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
 Actual selected-envelope count for our seventeen windows.
Two explicit outstanding analytic inputs: UniformUnitFaceSource fullSourceFace,
and beta<=incumbent. Neither is proved or replaced by a moment/count assumption.
The common-moment assembly follows PR69 PhysicalDirect.SourceMoments, using
the SAME genuine all-cutoff inverse/plain fields as Cycle25.ActualMoments.
The latter's packaged SourceMomentBound fixes the old cutoff and therefore
cannot itself be transported to a different selected-cutoff Batch.
-/
import Candidate.SilPrior.FourthPower.ReturnOldCount
import Candidate.SilPrior.FourthPower.ReturnSourceFaces
import Candidate.SilPrior.FourthPower.ReturnEnvelopeBridge
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.CountParameters
import Submissions.hailey_collet_1252270103.Record12518109Count.PhysicalDirect.InverseFields
import Mathlib.Order.Filter.Finite
import Mathlib.Data.List.OfFn
import Candidate.SilPrior.FourthPower.ReturnCountParameters

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Candidate.SilPrior.FourthPower.ReturnActualCount
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFixedAmplitudeCount ProbeHighRowFamily ProbePhysical
open Cycle25ProbeFinalAssembly Cycle25ProbeDetectorPlainMarkedFineField
open Cycle25ProbeDetectorPlainUnmarkedField ProbeFinalAssembly
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
open ReturnWindows ReturnSourceFaces ReturnOldCount ReturnEnvelopeBridge
open QRH.Record12518109Count QRH.Record12518109Existence
local instance : QRH.Record1252270103Return.CountScheme := countScheme

abbrev SavedParameters {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) :=
  QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.CountParameters F.modulus ⊤ D.t

/-- Both amplifier pairs and their actual count theorem are saved at once. -/
theorem exists_saved_parameters {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) :
    Nonempty (SavedParameters F) :=
  Candidate.SilPrior.FourthPower.ReturnCountParameters.exists_count_parameters
    F.modulus ⊤ le_top F.S F.w F.smooth F.compact F.positive_support
    (fun x => (F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x => (F.bounded x).2) D.t D.t_pos

/-- Three actual moment inputs on ONE fiber, uniformly for every cutoff and height.
The two natural inputs keep their different kappa values and saved amplifiers. -/
def CommonMoments {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (counts : SavedParameters F) (η : Character) (Z C : ℝ) (J : ℕ) : Prop :=
  ∀ (rows : Finset FreeRow), (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ d : ℝ, d0 ≤ d → ∀ (a tstar T allowance : ℝ) (i : ℕ)
      (B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T allowance i),
    B.rows ⊆ rows → B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
    B.profile = (fun _ x => (F.w x : ℂ)) → B.widths = (fun s => D.ell s/d) →
    (∀ s, B.upper s = 2) → (∀ s, (B.external s).re = 17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → (∀ s, |(B.external s).im| ≤ height) →
      Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne)
        contraryKappa counts.co counts.κo (C*(1+height)^J) height D.t ∧
      Cycle25DetectorRawFiber.Moments (B.fiber bin label left right hne)
        naturalKappa counts.ca counts.κa (C*(1+height)^J) height D.t ∧
      ∀ wi : Fin 17, AffineMarkedMoment (B.fiber bin label left right hne)
        (admittedWindow wi).face (C*(1+height)^J) height D.t

/-- Internal assembly from actual affine source transport. The final theorem
below supplies these affine inputs from the literal full source. -/
theorem common_moments_of_affine {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (counts : SavedParameters F)
    (hβ : theta < HeckeZeroSupremum.beta) (hinc : HeckeZeroSupremum.beta ≤ incumbent)
    (hfine : ∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200)
    (haffine : ∀ wi : Fin 17, WeightedAffineFineInput F (admittedWindow wi).face) :
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ CommonMoments F counts η Z C J := by
  obtain ⟨hk, hkhi, hbeta⟩ := contrary_gates hβ
  have hκnatural : 2*HeckeZeroSupremum.beta-1 ≤ naturalKappa := by
    dsimp only [naturalKappa]
    linarith
  have hpositive := terminal_plain_input F contraryKappa hk hkhi hbeta le_rfl
  have hpositive0 := terminal_plain_input F naturalKappa natural_kappa_bounds.1
    natural_kappa_bounds.2 hbeta hκnatural
  have hzero := terminal_zero_input F contraryKappa hk hkhi hbeta le_rfl
  obtain ⟨Ji, hi⟩ :=
    QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields
      F.modulus ⊤ le_top F counts.co counts.κo counts.co_pos counts.κo_pos
  obtain ⟨Ja, ha⟩ :=
    QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields
      F.modulus ⊤ le_top F counts.ca counts.κa counts.ca_pos counts.κa_pos
  obtain ⟨Jm, hm⟩ := weighted_source_batch_plain_marked_fine F contraryKappa
    (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine hpositive
  obtain ⟨Jm0, hm0⟩ := weighted_source_batch_plain_marked_fine F naturalKappa
    (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine hpositive0
  obtain ⟨Ju, hu⟩ :=
    Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  intro η
  obtain ⟨Ci, hCi, hi⟩ := hi η
  obtain ⟨Ca, hCa, ha⟩ := ha η
  obtain ⟨Cm, hCm, hm⟩ := hm η
  obtain ⟨Cm0, hCm0, hm0⟩ := hm0 η
  obtain ⟨Cu, hCu, hu⟩ := hu η
  choose Jr Cr hCr hr using (fun wi : Fin 17 => haffine wi η)
  let Jsum : ℕ := Ji+Ja+Jm+Jm0+Ju+∑ wi, Jr wi
  let Csum : ℝ := Ci+Ca+Cm+Cm0+Cu+1+∑ wi, Cr wi
  have hCrSum : 0 ≤ ∑ wi, Cr wi := Finset.sum_nonneg (fun wi _ => (hCr wi).le)
  have hCsum : 0 < Csum := by dsimp [Csum]; linarith
  have hCr_le (wi : Fin 17) : Cr wi ≤ Csum := by
    have hs := Finset.single_le_sum (fun w _ => (hCr w).le) (Finset.mem_univ wi)
    dsimp [Csum]; linarith
  have hJr_le (wi : Fin 17) : Jr wi ≤ Jsum := by
    have hs := Finset.single_le_sum (fun w _ => Nat.zero_le (Jr w)) (Finset.mem_univ wi)
    dsimp [Jsum]; omega
  have hrAll := Filter.eventually_all.mpr hr
  refine ⟨Jsum, Csum, hCsum, ?_⟩
  filter_upwards [hi, ha, hm, hm0, hu, hrAll] with Z hi ha hm hm0 hu hr
  refine ⟨hi.1, ?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth hupper hext
    bin label left right hne height hh hheight
  have hZ : 0 < Z := zero_lt_one.trans hi.1
  have hbase : 1 ≤ 1+height := by linarith
  have promote (K : ℝ) (j : ℕ) (hK : K ≤ Csum) (hj : j ≤ Jsum) :
      K*(1+height)^j ≤ Csum*(1+height)^Jsum :=
    mul_le_mul hK (pow_le_pow_right₀ hbase hj) (by positivity) hCsum.le
  have hCi' := promote Ci Ji (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCa' := promote Ca Ja (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCm' := promote Cm Jm (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCm0' := promote Cm0 Jm0 (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCu' := promote Cu Ju (by dsimp [Csum]; linarith) (by dsimp [Jsum]; omega)
  have hCr' (wi : Fin 17) := promote (Cr wi) (Jr wi) (hCr_le wi) (hJr_le wi)
  have hupperEq : B.upper = (fun _ => 2) := funext hupper
  have hinv := hi.2 d hd a D.ε tstar T allowance i B hdata hprofile hupperEq hwidth hext
    bin label left right hne height hh
  have hinvA := ha.2 d hd a D.ε tstar T allowance i B hdata hprofile hupperEq hwidth hext
    bin label left right hne height hh
  have hmarked := hm.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    hupper hext bin label left right hne height hh hheight
  have hmarked0 := hm0.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    hupper hext bin label left right hne height hh hheight
  have hunmarked := hu.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU : 0 ≤ Z^d := Real.rpow_nonneg hZ.le _
  refine ⟨?_, ?_, ?_⟩
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hkhi
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
          rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
      · intro selected hselected hfirst hsecond n hn σ hσ t ht
        exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    · intro selected hselected hcap j k hjk σ hσ t ht
      exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne)
      natural_kappa_bounds.2
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinvA.1 n hn σ hσ t ht).1 hCa',
          rawMoment_mono_constant (hinvA.1 n hn σ hσ t ht).2 hCa'⟩
      · intro selected hselected hfirst hsecond n hn σ hσ t ht
        exact (hinvA.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right hCa' (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    · intro selected hselected hcap j k hjk σ hσ t ht
      exact (hmarked0 selected hselected hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCm0' (Real.rpow_nonneg hU _))
  · intro wi
    have hraw := (hr wi).2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
      hupper hext bin label left right hne height hh hheight
    intro hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht
    exact (hraw hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right (hCr' wi) (Real.rpow_nonneg hU _))

/-- Actual cardinality bound on the selected-cutoff Batch. It uses the exact
variable-kappa finite envelope whose target slice is certified in ReturnFinite. -/
def SelectedCountBound {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (counts : SavedParameters F) (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀ (rows : Finset FreeRow), (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ (d a : ℝ), d0 ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 →
    ∀ i : ℕ,
    2*Real.pi*((Z^d)^(τ/(2*(7/8 : ℝ))))+(3*i : ℕ)*Z^τ ≤ height →
    ∀ (q : ℝ)
      (B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε
        (QRH.Record1252270103Return.GenericCount.selectedCutoff contraryKappa (2*a-1) (q/(2*a-1)))
        (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i),
    B.rows ⊆ rows → B.data = sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
    B.profile = (fun _ x => (F.w x : ℂ)) → B.widths = (fun s => D.ell s/d) →
    (∀ s, B.upper s = 2) → (∀ s, (B.external s).re = 17/50) →
    (∀ s, |(B.external s).im| ≤ height) →
    B.rows.Nonempty →
    (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (physical F.modulus ⊤ (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external
        (Z^d)) u = q) →
    (B.rows.card : ℝ) ≤
      (Fintype.card (Sum Bool (RayQuotient.Characters F.modulus ⊤)) : ℝ)*
      (dyadicLength (Z^d) : ℝ)^2*
      max (fiberConstant C height counts.Ko) (fiberConstant C height counts.Ka)*
      (Fintype.card B.Bin : ℝ)*
      (Z^d)^(variableEnvelope contraryKappa (2*a-1) (q/(2*a-1))+
        159*D.ε+D.t+B.mesh+7*D.t)

section
attribute [local irreducible] OAI.SevenEighths.HeckePrimeAmplitudeBins.labels

theorem selected_count_of_affine {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (hβ : theta < HeckeZeroSupremum.beta)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent)
    (hε : D.ε ≤ 1/10000000)
    (hfine : ∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200)
    (haffine : ∀ wi : Fin 17, WeightedAffineFineInput F (admittedWindow wi).face) :
    ∃ counts : SavedParameters F, ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        SelectedCountBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨counts⟩ := exists_saved_parameters F
  obtain ⟨hk, hkhi, _⟩ := contrary_gates hβ
  have hmom := common_moments_of_affine F counts hβ hinc hfine haffine
  refine ⟨counts, ?_⟩
  intro η
  obtain ⟨J, C, hC, hmom⟩ := hmom η
  refine ⟨J, C, hC, ?_⟩
  intro τ _hτ _hτhi
  have hd0 : (0 : ℝ) < d0 := by norm_num [d0]
  filter_upwards [hmom, eventually_all_rpow_ge counts.counted d0 hd0,
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) d0 hd0] with Z hm hc hU
  intro rows hrows d a hd _hdhi ha hahi i hfreq q B
    hsub hdata hprofile hwidth hupper hext hheight hne hq
  have hZ : 0 < Z := zero_lt_one.trans hm.1
  have hh : 0 ≤ Z^(2*τ) := Real.rpow_nonneg hZ.le _
  have hδ : 0 < 2*a-1 := by linarith
  have hδhi : 2*a-1 ≤ 3/4 := by linarith
  have hqrange := batch_mean_bounds B hne (by linarith) q hq
  have hp : q/(2*a-1) ∈ Icc 0 (1/2) :=
    ⟨div_nonneg hqrange.1 hδ.le, (div_le_iff₀ hδ).2 (by linarith [hqrange.2])⟩
  have hthree := hm.2 rows hrows d hd a _ _ _ i B hsub hdata hprofile hwidth hupper hext
  have hcard := hc d hd contraryKappa a D.ε (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ))))
    D.t (C*(1+Z^(2*τ))^J) (Z^(2*τ)) q i (hU d hd) ha hδhi
    D.epsilon_pos.le hε hk hkhi D.t_pos (by linarith [D.t_small])
    (by positivity) hh hfreq B hne hq
    (fun bin label left right hne => (hthree bin label left right hne _ hh hheight).1)
    (fun bin label left right hne => (hthree bin label left right hne _ hh hheight).2.1)
    (by
      intro w hw bin label left right hne
      have hw' : w ∈ List.ofFn admittedWindow := hw
      obtain ⟨wi, hwi⟩ := (List.mem_ofFn' admittedWindow w).mp hw'
      subst w
      exact (hthree bin label left right hne _ hh hheight).2.2 wi)
  change (B.rows.card : ℝ) ≤ _* (Z^d)^(upstreamEnvelope contraryKappa
    (2*a-1) (q/(2*a-1))+159*D.ε+D.t+B.mesh+7*D.t) at hcard
  conv at hcard =>
    rhs
    arg 2
    arg 2
    rw [upstreamEnvelope_eq_variable hk ⟨hδ.le, hδhi⟩ hp]
  simpa only [← Nat.card_eq_fintype_card] using hcard

end

/-- Main adapter. The source and incumbent are precisely the two remaining
analytic dependencies. Mesh is chosen before slots/source data; the two saved
amplifier pairs precede eta, and all height constants precede moving batches.
This is NOT an unconditional endpoint theorem. -/
theorem selected_count_from_full_source
    (hsource : UniformUnitFaceSource fullSourceFace)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent)
    (hβ : theta < HeckeZeroSupremum.beta) {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ D : Cycle25.Weighted.MomentData, ∀ F : WeightedSourceData D,
      D.t = ε → (∀ j, D.ell j ≤ mesh/200) → D.ε ≤ 1/10000000 →
      ∃ counts : SavedParameters F, ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
          SelectedCountBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨rawMesh, hrawMesh, hraw⟩ := all_detector_inputs_of_full_source hsource hε
  let mesh : ℝ := min rawMesh (Cycle25.sourceMesh ε)
  have hmesh : 0 < mesh := lt_min hrawMesh (Cycle25.sourceMesh_pos hε)
  refine ⟨mesh, hmesh, ?_⟩
  intro D F ht hf hsmall
  have hfraw : ∀ j, D.ell j ≤ rawMesh/200 := by
    intro j
    exact (hf j).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfnatural : ∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200 := by
    intro j
    rw [ht]
    exact (hf j).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  exact selected_count_of_affine F hβ hinc hsmall hfnatural (hraw D F ht hfraw)

end
end Candidate.SilPrior.FourthPower.ReturnActualCount
