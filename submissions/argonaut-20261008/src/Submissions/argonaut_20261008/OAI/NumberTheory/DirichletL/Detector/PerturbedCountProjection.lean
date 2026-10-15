import Submissions.argonaut_20261008.PerturbedCountBridge
import Submissions.argonaut_20261008.PerturbedMomentConstruction

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set

namespace SevenEighths.PerturbedCountProjection

open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open SevenEighths.ProbeFinalAssembly SevenEighths.ProbeHighRowFamily
open SevenEighths.PerturbedCountBridge
open SevenEighths.PerturbedMomentConstruction

local notation "O" => HeckeFamily.O

/-!
# The wide-count package projected to the official count interface

`WideCountParameters` and `CountParameters` have the same four numerical
constants.  The sole difference relevant here is that the former proves the
balanced branch for `Delta <= 9/40`, whereas the latter asks only for
`Delta <= 1/8`.  This file performs that restriction directly.  In particular,
no second classical choice of the four constants is made.
-/

/-- Restrict the wide balanced theorem to the official `1/8` range. -/
def WideCountParameters.toCountParameters
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    CountParameters M H epsilonM where
  cB := counts.cB
  kB := counts.kB
  cH := counts.cH
  kH := counts.kH
  cB_pos := counts.cB_pos
  cB_one := counts.cB_one
  kB_pos := counts.kB_pos
  cH_pos := counts.cH_pos
  cH_one := counts.cH_one
  kH_pos := counts.kH_pos
  balanced := by
    obtain ⟨K0, hK0, hwide⟩ := counts.balanced
    refine ⟨K0, hK0, ?_⟩
    filter_upwards [hwide] with U hU
    intro a epsilon T allowance Delta nu C height q i hU1 ha hbalanced
      hepsilon hepsilon1 hDelta hDelta1 hnu hC hheight hfreq
      Label Slot instLabel B hnonempty hmean hmom
    have hDeltaWide : Delta ≤ (9 / 40 : ℝ) :=
      hDelta1.trans (by norm_num)
    exact hU a epsilon T allowance Delta nu C height q i hU1 ha hbalanced
      hepsilon hepsilon1 hDelta hDeltaWide hnu hC hheight hfreq
      B hnonempty hmean hmom
  high := counts.high

/-- Transparent name bridge: the field name resolves to this same projection. -/
abbrev _root_.OAI.SevenEighths.PerturbedCountBridge.WideCountParameters.toCountParameters
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    CountParameters M H epsilonM :=
  OAI.SevenEighths.PerturbedCountProjection.WideCountParameters.toCountParameters counts

@[simp] theorem WideCountParameters.toCountParameters_cB
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    counts.toCountParameters.cB = counts.cB := rfl

@[simp] theorem WideCountParameters.toCountParameters_kB
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    counts.toCountParameters.kB = counts.kB := rfl

@[simp] theorem WideCountParameters.toCountParameters_cH
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    counts.toCountParameters.cH = counts.cH := rfl

@[simp] theorem WideCountParameters.toCountParameters_kH
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    counts.toCountParameters.kH = counts.kH := rfl

/-- All four constants are definitionally retained by the projection. -/
theorem WideCountParameters.toCountParameters_constants
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {epsilonM : ℝ}
    (counts : WideCountParameters M H epsilonM) :
    counts.toCountParameters.cB = counts.cB ∧
      counts.toCountParameters.kB = counts.kB ∧
      counts.toCountParameters.cH = counts.cH ∧
      counts.toCountParameters.kH = counts.kH :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Construct the wide package directly from the actual perturbed source.  This is
the only count choice used below; the official package is obtained by
`toCountParameters` from this same value.
-/
theorem source_wide_count_parameters
    (G : MomentGeometry) (F : PerturbedSourceData G) :
    Nonempty (WideCountParameters F.modulus ⊤ G.t) := by
  exact exists_wide_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth
    F.compact F.positive_support (fun y => (F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num)
    F.support (fun y => (F.bounded y).2) G.t G.t_pos

/-- A single wide package together with its official projection. -/
structure SameCountPackage (G : MomentGeometry) (F : PerturbedSourceData G) where
  wide : WideCountParameters F.modulus ⊤ G.t
  old : CountParameters F.modulus ⊤ G.t
  old_eq : old = wide.toCountParameters

/-- Construct the same-constant pair without a second choice. -/
theorem exists_same_count_package
    (G : MomentGeometry) (F : PerturbedSourceData G) :
    Nonempty (SameCountPackage G F) := by
  obtain ⟨wide⟩ := source_wide_count_parameters G F
  exact ⟨⟨wide, wide.toCountParameters, rfl⟩⟩

namespace SameCountPackage

@[simp] theorem cB
    {G : MomentGeometry} {F : PerturbedSourceData G}
    (P : SameCountPackage G F) : P.old.cB = P.wide.cB := by
  rw [P.old_eq]
  rfl

@[simp] theorem kB
    {G : MomentGeometry} {F : PerturbedSourceData G}
    (P : SameCountPackage G F) : P.old.kB = P.wide.kB := by
  rw [P.old_eq]
  rfl

@[simp] theorem cH
    {G : MomentGeometry} {F : PerturbedSourceData G}
    (P : SameCountPackage G F) : P.old.cH = P.wide.cH := by
  rw [P.old_eq]
  rfl

@[simp] theorem kH
    {G : MomentGeometry} {F : PerturbedSourceData G}
    (P : SameCountPackage G F) : P.old.kH = P.wide.kH := by
  rw [P.old_eq]
  rfl

end SameCountPackage

end SevenEighths.PerturbedCountProjection

end

end OAI
