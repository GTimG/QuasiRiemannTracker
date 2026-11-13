/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseClippedUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseUniformSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorInverseFiberCount
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountSource

/-!
# Interface.FiberBridge

From the anchor contracts towards the count.

* `detector_inverse_of_rect`: the inverse contract (reference profile) gives the detector-profile
  form of HC `actual_inverse_marked_energy` (all `n ≤ 2` log-derivatives, orientations, heights
  `σ, t`) with the native gates replaced by the rectangle. Port of HC's proof
  (`moving_finite_energy` + profile identity).
* The consumer-side fiber hypotheses are in `Interface/FiberImproved.lean`; the fiber transport
  is in `Interface/Bridge.lean`.
* Ordinary: `countFace` (per-factor cap `1/2`, consumed by `AffineMarkedMoment`), and
  `ordinaryRect_affine_input` through HC `detector_affine_of_unit`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Interface.FiberBridge
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-! ## Detector-profile form at row radius one -/

/-- The inverse contract implies the detector-profile moment used by fibers:
all log-derivatives `n ≤ 2`, both orientations, real part `σ ∈ [0,1]`, height `|t| ≤ height`,
with the rectangle in place of the native gates. The degree depends on the row data. -/
theorem detector_inverse_of_rect {fam : SlotClass → Prop} {ρ : AnchorRect} {mesh ε : ℝ}
    (hs : InverseRectSource fam ρ mesh ε) (cls : SlotClass) (hcls : fam cls) (K : ℕ) :
    ∀ data : RowData, ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
    ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ), 0 ≤ hv →
      cls ι data L ell β Z hv →
      (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) → (∀ i, ∀ P ∈ L i, Prime P) →
      (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
      (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
      (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
    ∀ r : ℝ, ρ.Admissible r (∑ i, ell i) 1 →
    ∀ rows : Finset HeckeInverseAmplification.NonzeroElement,
      (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z) →
    ∀ (tstar : ℝ) (reverse : Bool) (n : ℕ), n ≤ 2 → ∀ σ ∈ Icc (0 : ℝ) 1,
    ∀ height t : ℝ, 0 ≤ height → hv ≤ height → t ∈ Icc (-height) height →
      (∑ u ∈ rows, ‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest Z tstar r))) (Z^r) σ t *
          (∏ i, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2) ≤
        (C*(1+height)^degree)*Z^(1+ε) := by
  intro data
  obtain ⟨J,C,Z₀,hC,hZ₀,hb⟩ := hs K cls hcls
    (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ) (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx => DetectorDictionaryInverseClippedUniform.referenceWindow_support
      (subset_tsupport _ hx))
    (DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤) data
  obtain ⟨degree,Cf,hCf,hfourier⟩ :=
    DetectorDictionaryInverseMarkedUniform.moving_finite_energy J
  refine ⟨degree + 2*J,Cf*C,Z₀,mul_pos hCf hC,hZ₀,?_⟩
  intro Z hZ ι _ _ hK L ell β hv hv0 hc hell hmesh hp hratio hβ hlarge r hadm rows hrows
    tstar reverse n hn σ hσ height t hh hvh ht
  have hZp : 0 < Z := by linarith
  let mark := fun u : HeckeInverseAmplification.NonzeroElement =>
    ∏ i, directSlot u.val (L i) (β i) (Z^(ell i))
  -- the slot-height part of the height factor is a constant at fixed `hv`
  have href (v : ℝ) :
      (∑ u ∈ rows, ‖polynomial (data.character u) true
        (InverseMoment.childLogTest
          (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ) v)
        (Z^r) 0 0 * mark u‖^2) ≤ (C*Z^(1+ε)*(1+hv)^(2*J))*(1+‖v‖)^(2*J) := by
    have h := hb Z hZ hK L ell β hv hv0 hc hell hmesh hp hratio hβ hlarge 1 le_rfl le_rfl r hadm
      rows (fun u hu => by simpa using hrows u hu) v
    refine h.trans ?_
    have hCZ : 0 ≤ C*Z^(1+ε) := by positivity
    calc C*Z^(1+ε)*((1+‖v‖+hv)^J)^2 ≤ C*Z^(1+ε)*((1+hv)^(2*J)*(1+‖v‖)^(2*J)) :=
          mul_le_mul_of_nonneg_left (heightFactor_split v hv0 J) hCZ
      _ = (C*Z^(1+ε)*(1+hv)^(2*J))*(1+‖v‖)^(2*J) := by ring
  have hb' := hfourier rows data.character mark (Z^r) (C*Z^(1+ε)*(1+hv)^(2*J))
    (Real.rpow_pos_of_pos hZp _) (by positivity) href false reverse n hn Z hZp tstar r σ hσ t
  have hprofile :
      (DetectorDictionaryInverseUniform.inverseSourceSchwartz false reverse n Z tstar r σ t :
        ℝ → ℂ) =
      HeckeInverseAmplification.twistProfile ((HeckeDetectorRowwisePolynomial.logProfile^[n])
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest Z tstar r))) σ t := by
    funext x
    simpa only [Bool.false_eq_true,ite_false,
      DetectorDictionaryInverseMarkedUniform.logTest_eq_iterate] using
      DetectorDictionaryInverseUniform.inverseSourceSchwartz_apply false reverse n Z tstar r σ t x
  simp only [hprofile,HeckeInverseAmplification.polynomial_twistProfile] at hb'
  apply hb'.trans
  have ht' : ‖t‖ ≤ height := by
    simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  have hvh' : (1+hv)^(2*J) ≤ (1+height)^(2*J) := by gcongr
  calc
    Cf*(C*Z^(1+ε)*(1+hv)^(2*J))*(1+‖t‖)^degree ≤
        Cf*(C*Z^(1+ε)*(1+height)^(2*J))*(1+height)^degree := by gcongr
    _ = _ := by ring

/-! ## Ordinary side -/

/-- The rectangle as an `AffineMarkedMoment` face (per-factor width `≤ 1/2`, as required by HC
`detector_affine_of_unit`): `2m ≤ Pmax`, `S ≤ Smax`. -/
def countFace (ρ : AnchorRect) : QRH.Record12518109Source.SourceFace :=
  ⟨ρ.Pmax, 0, 0, 1/2, 0, ρ.Smax⟩

theorem ordinaryFace_restricts_countFace {ρ : AnchorRect} (h : 1/2 ≤ ρ.Pmax) :
    ρ.ordinaryFace.Restricts (countFace ρ) := by
  constructor <;>
    simp only [AnchorRect.ordinaryFace,QRH.Record1252270103Source.globalFace,countFace] <;>
    linarith

/-- The ordinary contract supplies HC's batch-level affine moment input on the
rectangle face, through `detector_affine_of_unit` (existing transport). -/
theorem ordinaryRect_affine_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ρ : AnchorRect}
    (hP : 1/2 ≤ ρ.Pmax) (mesh : ℝ) (hmesh : 0 < mesh) (hfine : ∀ j, D.ell j ≤ mesh/200)
    (hsrc : QRH.Record12518109Existence.UnitFaceSource ρ.ordinaryFace mesh D.t) :
    QRH.Record12518109Count.WeightedAffineFineInput S (countFace ρ) :=
  QRH.Record1252270103Return.detector_affine_of_unit S (countFace ρ)
    (by simp only [countFace]; exact le_rfl) mesh hmesh hfine
    (unitFaceSource_restrict (ordinaryFace_restricts_countFace hP) hsrc)

theorem OrdinaryRectSource.affine_input {ρ : AnchorRect} (hs : OrdinaryRectSource ρ)
    (hP : 1/2 ≤ ρ.Pmax) (t : ℝ) (ht : 0 < t) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ {D : Cycle25.Weighted.MomentData}, D.t = t →
      (∀ j, D.ell j ≤ mesh/200) → ∀ S : Cycle25ProbeFinalAssembly.WeightedSourceData D,
        QRH.Record12518109Count.WeightedAffineFineInput S (countFace ρ) := by
  obtain ⟨mesh,hmesh,hsrc⟩ := hs t ht
  refine ⟨mesh,hmesh,fun {D} hD hfine S => ?_⟩
  subst hD
  exact ordinaryRect_affine_input S hP mesh hmesh hfine hsrc

end
end Qrh.MarkedAnchor.Interface.FiberBridge

#print axioms Qrh.MarkedAnchor.Interface.FiberBridge.detector_inverse_of_rect
#print axioms Qrh.MarkedAnchor.Interface.FiberBridge.ordinaryRect_affine_input
