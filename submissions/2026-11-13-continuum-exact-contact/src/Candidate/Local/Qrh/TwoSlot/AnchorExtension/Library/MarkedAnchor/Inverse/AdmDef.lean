/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Oracle
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPeriod
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialCommonProfile

/-!
# Inverse.AdmDef — the image slot filter (definitions only)

`imageAdm fam mesh`, `imageAdm' mesh cls`, monotonicity in the mesh and the ratio facts read off
by the selection. Split from `AdmImage` (which proves the covering and the oracle chain) so that the
selection assembly does not depend on the chain.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- The canonical slot data that are dictionary images of `fam`-slot vectors of mesh `≤ mesh`.
No disjointness of the pools `L i` is required (they may overlap). The slot height bound `hv` is
the last argument of the filter (the oracle quantifies `∀ hv, 0 ≤ hv →` before it); the class
membership is at that height, and the row height `t` of the log-phase twist is bounded by the same
height, `|t| ≤ hv`. -/
def imageAdm (fam : SlotClass → Prop) (mesh : ℝ) : SlotAdm :=
  fun q D σ _ slots lists H a Z hv =>
    ∃ (cls : SlotClass) (_ : fam cls) (data : RowData) (L : σ → Finset (Ideal O))
      (ell : σ → ℝ) (β : σ → Ideal O → ℂ) (J : Finset σ) (t : ℝ),
      cls σ data L ell β Z hv ∧ (∀ i, 0 ≤ ell i) ∧ (∀ i, ell i ≤ mesh) ∧
      (∀ i, ∀ P ∈ L i, Prime P) ∧
      (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) ∧
      (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) ∧
      (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) ∧
      deletedPeriod (basePeriod data) = q ∧
      (∀ i, i ∈ slots ↔ i ∉ J) ∧
      (∀ i (P : PoolIdx q D), P ∈ lists i ↔ P.val ∈ L i) ∧
      (∀ i, H i = 2*Z^(ell i)) ∧
      (∀ i (P : PoolIdx q D), a i P = star (β i P.val / idealCoeff (deletedBase data) P.val) *
        FourierBridge.logPhase (-t)
          (Real.log (InverseInitialCommonProfile.slotRatio Z ell i P.val))) ∧
      |t| ≤ hv

/-- A slot class is monotone in its height bound. -/
def HeightMono (cls : SlotClass) : Prop :=
  ∀ (ι : Type) (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (Z hv hv' : ℝ), hv ≤ hv' → cls ι data L ell β Z hv → cls ι data L ell β Z hv'

/-- The canonical classes are monotone in the height (`canonicalSlotsRay_mono_height`). -/
theorem canonicalFamily_heightMono (cls : SlotClass) (h : canonicalFamily cls) :
    HeightMono cls := by
  obtain ⟨W, _, _, rayM, _, G, hH, rfl⟩ := h
  intro ι data L ell β Z hv hv' hle hc
  exact canonicalSlotsRay_mono_height W (33/50) rayM G hH ι data L ell β Z hv hv' hle hc

theorem imageAdm_mono (fam : SlotClass → Prop) :
    ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      imageAdm fam mesh' q D σ slots lists H a Z hv →
        imageAdm fam mesh q D σ slots lists H a Z hv := by
  intro mesh mesh' hle q D σ _ slots lists H a Z hv h
  obtain ⟨cls,hcls,data,L,ell,β,J,t,hc,hell,hm,hrest⟩ := h
  exact ⟨cls,hcls,data,L,ell,β,J,t,hc,hell,fun i => (hm i).trans hle,hrest⟩

/-- What the selection step reads off the filter: slot scale `H i = 2 Z^(ell i)` with
`ell i ≤ mesh`, and the two-sided ratio `H i / 2 ≤ N P ≤ H i` on the lists. -/
theorem imageAdm_ratio {fam : SlotClass → Prop} {mesh : ℝ} {q D : ℕ} {σ : Type}
    [DecidableEq σ] {slots : Finset σ} {lists : σ → Finset (PoolIdx q D)} {H : σ → ℝ}
    {a : σ → PoolIdx q D → ℂ} {Z hv : ℝ} (hZ : 1 ≤ Z)
    (h : imageAdm fam mesh q D σ slots lists H a Z hv) :
    (∀ i, 2 ≤ H i ∧ H i ≤ 2*Z^mesh) ∧
    (∀ i, ∀ P ∈ lists i, H i/2 ≤ (P.val.absNorm : ℝ) ∧ (P.val.absNorm : ℝ) ≤ H i) := by
  obtain ⟨_,_,_,L,ell,_,_,_,_,hell,hm,_,hratio,_,_,_,_,hlists,hH,_⟩ := h
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  refine ⟨fun i => ⟨?_,?_⟩,fun i P hP => ?_⟩
  · rw [hH i]; have := Real.one_le_rpow hZ (hell i); linarith
  · rw [hH i]; have := Real.rpow_le_rpow_of_exponent_le hZ (hm i); linarith
  · have hr := hratio i P.val ((hlists i P).mp hP)
    have hpos := Real.rpow_pos_of_pos hZ0 (ell i)
    rw [hH i]
    obtain ⟨h1,h2⟩ := hr
    rw [le_div_iff₀ hpos] at h1
    rw [div_le_iff₀ hpos] at h2
    constructor <;> linarith

/-- The image filter of ONE slot class: dictionary images of `cls`-slot vectors of mesh `≤ mesh`. -/
def imageAdm' (mesh : ℝ) (cls : SlotClass) : SlotAdm := imageAdm (· = cls) mesh

theorem imageAdm'_mono :
    ∀ mesh mesh', mesh' ≤ mesh → ∀ cls q D σ [DecidableEq σ] slots lists H a Z hv,
      imageAdm' mesh' cls q D σ slots lists H a Z hv →
        imageAdm' mesh cls q D σ slots lists H a Z hv :=
  fun mesh mesh' hle cls => imageAdm_mono (· = cls) mesh mesh' hle

theorem imageAdm'_ratio {mesh : ℝ} {cls : SlotClass} {q D : ℕ} {σ : Type}
    [DecidableEq σ] {slots : Finset σ} {lists : σ → Finset (PoolIdx q D)} {H : σ → ℝ}
    {a : σ → PoolIdx q D → ℂ} {Z hv : ℝ} (hZ : 1 ≤ Z)
    (h : imageAdm' mesh cls q D σ slots lists H a Z hv) :
    (∀ i, 2 ≤ H i ∧ H i ≤ 2*Z^mesh) ∧
    (∀ i, ∀ P ∈ lists i, H i/2 ≤ (P.val.absNorm : ℝ) ∧ (P.val.absNorm : ℝ) ≤ H i) :=
  imageAdm_ratio hZ h

end
end Qrh.MarkedAnchor.Inverse
