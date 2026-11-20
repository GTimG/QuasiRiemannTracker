/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual original inverse/ordinary count moments and coupled affine moment on
one source Batch fiber. Adapted from the credited Collet/Gao source-field
assembly, with the Q coupled source proved here and no saved count scheme. -/
import Candidate.C092.transport.DirectCountUnmarked
import Candidate.C092.transport.DirectCountSource
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.ActualMoments
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open ProbeFinalAssembly
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField

/-- All moments consumed by the original piecewise count, supplied on the
literal original source dictionary and the identical supported-zero fiber. -/
theorem q_actual_count_fields
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ → ℝ, (∀ t, 0 < t → 0 < mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
    (∀ j, D.ell j ≤ mesh D.t/200) →
    (∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200) →
    ∀ κplain : ℝ, 7/10 ≤ κplain → κplain ≤ 3/4 →
    2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∀ c κinverse : ℝ, 0 < c → 0 < κinverse →
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a tstar T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a D.ε tstar T allowance i),
    B.rows ⊆ rows → B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.widths=(fun s => D.ell s/d) →
    B.upper=(fun _ => 2) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → (∀ s, |(B.external s).im| ≤ height) →
    let F := B.fiber bin label left right hne
    Cycle25DetectorRawFiber.Moments F κplain c κinverse (C*(1+height)^J) height D.t ∧
    AffineMarkedMoment F countFace (C*(1+height)^J) height D.t := by
  obtain ⟨mesh,hm,hAffine⟩ := q_count_mesh hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfineA hfine κ hk hk1 hkβ c κi hc hκi η
  obtain ⟨Ji,hi⟩ := QRH.Record12518109Count.PhysicalDirect.InverseFields.weighted_source_batch_inverse_fields
    S.modulus ⊤ le_top S c κi hc hκi
  obtain ⟨Jm,hm⟩ := weighted_source_batch_plain_marked_fine S κ (Cycle25.sourceMesh D.t)
    (Cycle25.sourceMesh_pos D.t_pos) hfine (terminal_plain_input S κ hk hk1 hβ hkβ)
  obtain ⟨Ju,hu⟩ := Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked
    D S (terminal_zero_input S κ hk hk1 hβ hkβ)
  obtain ⟨Ci,hCi,hi⟩ := hi η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  obtain ⟨Cu,hCu,hu⟩ := hu η
  obtain ⟨Ja,Ca,hCa,ha⟩ := hAffine D S hfineA η
  let J := Ji+Jm+Ju+Ja
  let C := Ci+Cm+Cu+Ca+1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hi,hm,hu,ha] with Z hi hm hu ha
  refine ⟨ha.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label left right hne height hh him
  dsimp only
  let F := B.fiber bin label left right hne
  have hU : 0 ≤ Z^d := Real.rpow_nonneg (zero_lt_one.trans ha.1).le _
  have hbase : 1 ≤ 1+height := by linarith
  have promote (c : ℝ) (j : ℕ) (hc : c ≤ C) (hj : j ≤ J) :
      c*(1+height)^j ≤ C*(1+height)^J :=
    mul_le_mul hc (pow_le_pow_right₀ hbase hj) (by positivity) hC.le
  have pi := promote Ci Ji (by dsimp [C]; linarith) (by dsimp [J]; omega)
  have pm := promote Cm Jm (by dsimp [C]; linarith) (by dsimp [J]; omega)
  have pu := promote Cu Ju (by dsimp [C]; linarith) (by dsimp [J]; omega)
  have pa := promote Ca Ja (by dsimp [C]; linarith) (by dsimp [J]; omega)
  have hinv := hi.2 d hd a D.ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hh
  have hmarked := hm.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    (fun s => congrFun hupper s) hreal bin label left right hne height hh him
  have hunmarked := hu.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have haffine := ha.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    (fun s => congrFun hupper s) hreal bin label left right hne height hh him
  constructor
  · apply Cycle25DetectorRawFiber.Moments.of_fields F hk1
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 pi,
          rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 pi⟩
      · intro selected hsel hfirst hsecond n hn σ hσ t ht
        exact (hinv.2 selected hsel hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right pi (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right pu (Real.rpow_nonneg hU _))
    · intro selected hsel hcap j k hjk σ hσ t ht
      exact (hmarked selected hsel hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right pm (Real.rpow_nonneg hU _))
  · intro hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht
    exact (haffine hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right pa (Real.rpow_nonneg hU _))
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.q_actual_count_fields
