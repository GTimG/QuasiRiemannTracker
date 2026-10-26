/- Copyright (c) 2026 Sil. Apache-2.0.
upper-cap restriction of the actual uniform initial-energy source.
The global source is an explicit, still-to-be-proved analytic input. This file
only transports it, without asserting its existence or any endpoint bound.
The transport pattern follows PR69 InitialMoment/SourceInlet/CountSource,
with a new admissibility proof because the slope inequality is reversed.
Not imported into src and not Lean checked. -/
import Candidate.FourthPower.ReturnWindows
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountSource

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnSourceFaces
noncomputable section
open scoped Classical BigOperators ContDiff
open ReturnCountData ReturnFinite ReturnWindows
open OAI OAI.SevenEighths HeckeFamily Filter
open QRH.Record12518109Source QRH.Record12518109Existence

local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The sole new analytic source which the main construction must actually prove. -/
def fullSourceFace : SourceFace :=
  QRH.Record1252270103Return.globalFace sourceB sourceSlope sourceCap

/-- The actual broad source consumed by an improved detector branch. -/
def branchSourceFace (b : ImprovedBranch) : SourceFace :=
  QRH.Record1252270103Return.broadFace b.face.intercept b.face.slope b.face.cap

/-- Homogeneous upper-cap inclusion. This uses our checked domain theorem;
it does not invoke SourceFace.Restricts, whose slope direction is unsuitable. -/
theorem branch_admissible (b : ImprovedBranch) {m₁ m₂ s M : ℝ}
    (hM : 0 ≤ M) (ha : (branchSourceFace b).Admissible m₁ m₂ s M) :
    fullSourceFace.Admissible m₁ m₂ s M := by
  change 0*M ≤ m₁ ∧ m₁ ≤ (1/2)*M ∧ 0*M ≤ m₂ ∧ m₂ ≤ (1/2)*M ∧
    0*M ≤ s ∧ s ≤ b.face.cap*M ∧ m₁+m₂+b.face.slope*s ≤ b.face.intercept*M at ha
  rcases ha with ⟨h₁,h₁',h₂,h₂',hs,hs',hb⟩
  change 0*M ≤ m₁ ∧ m₁ ≤ sourceB*M ∧ 0*M ≤ m₂ ∧ m₂ ≤ sourceB*M ∧
    0*M ≤ s ∧ s ≤ sourceCap*M ∧ m₁+m₂+sourceSlope*s ≤ sourceB*M
  have hplain : (1/2)*M ≤ sourceB*M :=
    mul_le_mul_of_nonneg_right (by norm_num [sourceB]) hM
  refine ⟨h₁,h₁'.trans hplain,h₂,h₂'.trans hplain,hs,?_⟩
  by_cases hzero : M=0
  · subst M
    norm_num at h₁ h₁' h₂ h₂' hs hs'
    have hm₁ : m₁=0 := by linarith
    have hm₂ : m₂=0 := by linarith
    have hslot : s=0 := by linarith
    norm_num [hm₁,hm₂,hslot]
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    have hs0 : 0 ≤ s := by simpa using hs
    have hcap : s/M ≤ b.face.cap := (div_le_iff₀ hMp).2 hs'
    have hbudget : (m₁+m₂)/M+b.face.slope*(s/M) ≤ b.face.intercept := by
      rw [←mul_div_assoc,←add_div]
      exact (div_le_iff₀ hMp).2 hb
    obtain ⟨hc,hb'⟩ := Face.source_domain (improved_face_included b)
      (div_nonneg hs0 hM) hcap hbudget
    refine ⟨(div_le_iff₀ hMp).1 hc,?_⟩
    rw [←mul_div_assoc,←add_div] at hb'
    exact (div_le_iff₀ hMp).1 hb'

/-- Literal InitialAffineAt transfer, retaining every profile, character,
coefficient, initialKeep, height, threshold and normalizing factor. -/
theorem initial_source_to_branch
    {α : Type} [Fintype α] [DecidableEq α]
    (b : ImprovedBranch) (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (bslot a z bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ)
    (controls : Finset (ℕ×ℕ)) (C : ℝ) (hMmin : 0 ≤ Mmin)
    (hsource : InitialAffineAt (α:=α) rayM H hH fullSourceFace W
      bslot a z bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree controls C) :
    InitialAffineAt (α:=α) rayM H hH (branchSourceFace b) W
      bslot a z bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree controls C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos profiles X₁ X₂ hX₁ hX₂ hadm
  exact hsource T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos profiles X₁ X₂ hX₁ hX₂
    (branch_admissible b (hMmin.trans hMlo) hadm)

/-- The common mesh and epsilon are unchanged; no extra uniformity is assumed. -/
theorem unit_source_to_branch (b : ImprovedBranch) {mesh ε : ℝ}
    (hsource : UnitFaceSource fullSourceFace mesh ε) :
    UnitFaceSource (branchSourceFace b) mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hs⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ
    η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,hs.mono ?_⟩
  intro Z hZ
  exact initial_source_to_branch b rayM H hH W 2 (1/4) (9/4) bΦ mesh
    (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C (by norm_num) hZ

theorem uniform_source_to_branch (b : ImprovedBranch)
    (hsource : UniformUnitFaceSource fullSourceFace) :
    UniformUnitFaceSource (branchSourceFace b) := by
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := hsource ε hε
  exact ⟨mesh,hm,unit_source_to_branch b hs⟩

/-- The same mesh simultaneously supplies all weakened branches, hence the
six used branches and all seventeen windows. The source remains an input. -/
theorem all_branch_sources_common_mesh
    (hsource : UniformUnitFaceSource fullSourceFace) {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ b : ImprovedBranch, UnitFaceSource (branchSourceFace b) mesh ε := by
  obtain ⟨mesh,hm,hs⟩ := hsource ε hε
  exact ⟨mesh,hm,fun b => unit_source_to_branch b hs⟩

theorem admittedWindow_face_eq (i : Fin 17) :
    (admittedWindow i).face = branchSourceFace (window i).branch := rfl

theorem all_window_sources_common_mesh
    (hsource : UniformUnitFaceSource fullSourceFace) {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ i : Fin 17, UnitFaceSource (admittedWindow i).face mesh ε := by
  obtain ⟨mesh,hm,hs⟩ := all_branch_sources_common_mesh hsource hε
  exact ⟨mesh,hm,fun i => hs (window i).branch⟩

/-- Actual upstream detector inputs for the six branches/17 windows. A literal
uniform ordinary source, still required from the analytic source block, is the
only source premise; no count or final-bound assumption is introduced. -/
theorem all_detector_inputs_of_full_source
    (hsource : UniformUnitFaceSource fullSourceFace) {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧
      ∀ D : Cycle25.Weighted.MomentData,
      ∀ F : Cycle25ProbeFinalAssembly.WeightedSourceData D, D.t=ε →
      (∀ j,D.ell j ≤ mesh/200) →
      ∀ i : Fin 17,
        QRH.Record12518109Count.WeightedAffineFineInput F (admittedWindow i).face := by
  obtain ⟨mesh,hm,hs⟩ := all_window_sources_common_mesh hsource hε
  refine ⟨mesh,hm,?_⟩
  intro D F ht hf i
  apply QRH.Record1252270103Return.detector_affine_of_unit
    F (admittedWindow i).face (by rfl) mesh hm hf
  rw [ht]
  exact hs i

/- Incumbent integration: the two exact C30 global source domains are strict
subdomains of the new full source. No C30 endpoint or graph import is needed
for these comparisons; their literal values are from C30/ReturnConstants and
IntermediateCount/Scheme. These statements do not assert the full source. -/
def intermediateCountFace : Face :=
  ⟨482045093689/500000000000, 3198839752287/1000000000000,
    54998999999/1000000000000⟩
def intermediatePhysicalFace : Face :=
  ⟨96934050457/100000000000, 3328741896069/1000000000000,
    54998999999/1000000000000⟩

theorem intermediate_count_included : intermediateCountFace.Included := by
  norm_num [Face.Included, intermediateCountFace, sourceB, sourceSlope, sourceCap]

theorem intermediate_physical_included : intermediatePhysicalFace.Included := by
  norm_num [Face.Included, intermediatePhysicalFace, sourceB, sourceSlope, sourceCap]

/-- Exact homogeneous inclusion for global faces, including both individual
ordinary lengths. The upper slot cap pays the reversed slope inequality. -/
theorem global_admissible_of_included {f : Face} (hf : f.Included)
    {m₁ m₂ s M : ℝ} (hM : 0 ≤ M)
    (ha : (QRH.Record1252270103Return.globalFace f.intercept f.slope f.cap).Admissible m₁ m₂ s M) : fullSourceFace.Admissible m₁ m₂ s M := by
  change 0*M ≤ m₁ ∧ m₁ ≤ f.intercept*M ∧ 0*M ≤ m₂ ∧ m₂ ≤ f.intercept*M ∧
    0*M ≤ s ∧ s ≤ f.cap*M ∧ m₁+m₂+f.slope*s ≤ f.intercept*M at ha
  rcases ha with ⟨h₁,h₁',h₂,h₂',hs,hs',hb⟩
  rcases hf with ⟨hc0,hc,hL0,hL,hB⟩
  have hgap : 0 ≤ sourceSlope-f.slope := sub_nonneg.mpr hL
  have hprod : 0 ≤ (sourceSlope-f.slope)*f.cap := mul_nonneg hgap hc0
  have hB0 : f.intercept ≤ sourceB := by linarith
  have hplain := mul_le_mul_of_nonneg_right hB0 hM
  have hcap := mul_le_mul_of_nonneg_right hc hM
  have hslope := mul_le_mul_of_nonneg_left hs' hgap
  have hbudget := mul_le_mul_of_nonneg_right hB hM
  change 0*M ≤ m₁ ∧ m₁ ≤ sourceB*M ∧ 0*M ≤ m₂ ∧ m₂ ≤ sourceB*M ∧
    0*M ≤ s ∧ s ≤ sourceCap*M ∧ m₁+m₂+sourceSlope*s ≤ sourceB*M
  exact ⟨h₁,h₁'.trans hplain,h₂,h₂'.trans hplain,hs,hs'.trans hcap,by nlinarith⟩

/-- Keeps the same mesh, loss, controls, constant and eventual threshold.
The construction is just admissibility transport of the actual initial energy. -/
theorem unit_source_to_global {f : Face} (hf : f.Included) {mesh ε : ℝ}
    (hsource : UnitFaceSource fullSourceFace mesh ε) :
    UnitFaceSource (QRH.Record1252270103Return.globalFace f.intercept f.slope f.cap)
      mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hs⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ
    η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,hs.mono ?_⟩
  intro Z hZ
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos profiles X₁ X₂ hX₁ hX₂ hadm
  exact hZ T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos profiles X₁ X₂ hX₁ hX₂
    (global_admissible_of_included hf (by linarith) hadm)

/-- The genuine C30 suppliers, with literal numbers so this small adapter
imports no old endpoint. A later adapter identifies these by definitional
reduction with IntermediateCount.countGlobal and physicalGlobal. -/
theorem intermediate_sources_of_full_source
    (hsource : UniformUnitFaceSource fullSourceFace) :
    UniformUnitFaceSource (QRH.Record1252270103Return.globalFace
      (482045093689/500000000000) (3198839752287/1000000000000)
      (54998999999/1000000000000)) ∧
    UniformUnitFaceSource (QRH.Record1252270103Return.globalFace
      (96934050457/100000000000) (3328741896069/1000000000000)
      (54998999999/1000000000000)) := by
  constructor
  · intro ε hε
    obtain ⟨mesh,hm,hs⟩ := hsource ε hε
    exact ⟨mesh,hm,unit_source_to_global intermediate_count_included hs⟩
  · intro ε hε
    obtain ⟨mesh,hm,hs⟩ := hsource ε hε
    exact ⟨mesh,hm,unit_source_to_global intermediate_physical_included hs⟩

end
end Candidate.FourthPower.ReturnSourceFaces
