/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Parameterized version of Sil's PR137 consumer-side fiber contracts.
Original definitions copyright (c) 2026 Sil, Apache-2.0, adapted from
Hailey Collet's fiber predicates over the OpenAI baseline (Apache-2.0).
The line is explicit: stronger source data cannot silently use old constants. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.FiberImproved

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine
noncomputable section
open scoped Classical BigOperators
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily Cycle25ProbeFinalAssembly ProbeFinalAssembly
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
open Qrh.MarkedAnchor.Interface (anchorLeft anchorTop)

structure Line where
  g0 : ℝ
  g1 : ℝ
  slope_nonneg : 0 ≤ g1
  slope_le : g1 ≤ 1/2

def markCap (line : Line) (w : ℝ) : ℝ := (1-w)/2+line.g0-line.g1*w
variable {line : Line}

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The improved inverse marked moment on one fiber: free width `F.r ∈ [anchorLeft, anchorTop]`,
selected slots of total width at most `markCap line F.r - ν`. -/
def ImprovedInverseMoment (line : Line) (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (ν C height εm : ℝ) : Prop :=
  anchorLeft ≤ F.r → F.r ≤ anchorTop →
  ∀ selected : Finset Slot, selected ⊆ F.slots →
    (∑ s∈selected, F.widths s) ≤ markCap line F.r-ν →
    ∀ n : ℕ, n ≤ 2 → ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

/-- The improved ordinary two-factor moment on one fiber: doubled width `2 F.m ∈ [anchorLeft,
anchorTop]`, selected slots of total width at most `markCap line (2 F.m) - ν`. -/
def ImprovedOrdinaryMoment (line : Line) (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (ν C height εm : ℝ) : Prop :=
  anchorLeft ≤ 2*F.m → 2*F.m ≤ anchorTop →
  ∀ selected : Finset Slot, selected ⊆ F.slots →
    (∑ s∈selected, F.widths s) ≤ markCap line (2*F.m)-ν →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        (U^F.m) s t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        (U^F.m) s t*F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

/-- Both improved fiber moments (slack `ν`, constant `C`, height bound `height`, error `εm`). -/
structure ImprovedMoments (line : Line) (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (ν C height εm : ℝ) : Prop where
  inverse : ImprovedInverseMoment line F ν C height εm
  ordinary : ImprovedOrdinaryMoment line F ν C height εm

theorem ImprovedMoments.mono_constant {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {ν C C' height εm : ℝ} (h : ImprovedMoments line F ν C height εm) (hU : 0 ≤ U) (hC : C ≤ C') :
    ImprovedMoments line F ν C' height εm := by
  have hp : 0 ≤ U^(1+εm) := Real.rpow_nonneg hU _
  refine ⟨?_,?_⟩
  · intro h1 h2 sel hsel hw n hn s hs t ht
    exact (h.inverse h1 h2 sel hsel hw n hn s hs t ht).trans (mul_le_mul_of_nonneg_right hC hp)
  · intro h1 h2 sel hsel hw j k hjk s hs t ht
    exact (h.ordinary h1 h2 sel hsel hw j k hjk s hs t ht).trans (mul_le_mul_of_nonneg_right hC hp)

/-- The improved fiber moments on every fiber of every source batch of one weighted source `S`
(the analogue of `WeightedAffineFineInput S f`): for each character `η` the constants `J, C` precede
the scale `Z`; then every batch at a row scale `Z^d`, `d ≥ 1/200`, with the source dictionary, all
fibers and all heights satisfy `ImprovedMoments` with slack and error `D.t`. -/
def ImprovedFineInput (line : Line) {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D) : Prop :=
  ∀η : Character, ∃J : ℕ, ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop,
    1 < Z ∧ ∀rows : Finset FreeRow, (∀u∈rows, Z^(1/100:ℝ) ≤ rowNorm u) →
    ∀d : ℝ, (1/200:ℝ) ≤ d → ∀(a tstar T allowance : ℝ) (i : ℕ)
    (B : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i), B.rows ⊆ rows →
    B.data = sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile = (fun _ x => (S.w x:ℂ)) → B.widths = (fun s => D.ell s/d) →
    (∀s, B.upper s = 2) → (∀s, (B.external s).re = 17/50) →
    ∀bin label left right, ∀hne : (B.fiberRows bin label left right).Nonempty,
    ∀height : ℝ, 0 ≤ height → (∀s, |(B.external s).im| ≤ height) →
    ImprovedMoments line (B.fiber bin label left right hne) D.t (C*(1+height)^J) height D.t

/-- **The improved fiber moments consumed by the improved count windows.** For every error `ε > 0`
there is a mesh such that every weighted source whose moment data have error `D.t = ε` and slot
lengths `D.ell j ≤ mesh/200` satisfies `ImprovedFineInput`. -/
def ImprovedFiberMoments (line : Line) : Prop :=
  ∀ε : ℝ, 0 < ε → ∃mesh : ℝ, 0 < mesh ∧
    ∀{D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D),
      D.t = ε → (∀j, D.ell j ≤ mesh/200) → ImprovedFineInput line S

namespace Return
/-- A source line remains inside the physical selected-slot capacity. These
bounds are verified once for a supplied line, independently of its moments. -/
class CapacityBounds (line : Line) : Prop where
  bounds : ∀ w : ℝ, anchorLeft ≤ w → w ≤ anchorTop →
    (1/10000000:ℝ) < markCap line w ∧ markCap line w ≤ 7/37
end Return

end
end Qrh.TwoSlot.AnchorZeroLoss.Affine
