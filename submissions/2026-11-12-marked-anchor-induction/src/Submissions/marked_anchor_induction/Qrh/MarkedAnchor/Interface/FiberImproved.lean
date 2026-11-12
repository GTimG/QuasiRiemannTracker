/- Copyright (c) 2026 Sil. Apache-2.0.
The consumer-side fiber moments of the improved count windows. Modelled on Hailey Collet's fiber
predicates `Cycle25DetectorRawFiber.Moments`/`BaseMoments`, `AffineMarkedMoment` and
`WeightedAffineFineInput` (Apache-2.0) over the OpenAI baseline `HeckeDetectorRawFiber.Fiber`. -/
import Submissions.hailey_collet_1252270103.Record12518109Count.InitialTransport

/-!
# Interface.FiberImproved

The improved count windows of the return (`MarkedAnchor/Return/*`) consume exactly two new moment
estimates on a detector fiber `F` (rows of norm `≤ U`, all lengths are exponents relative to `U`,
i.e. the row radius is normalized to `1` as in `Cycle25DetectorRawFiber.Moments`), both on the anchor
interval `[anchorLeft, anchorTop] = [1467/2000, 311/400]` and below the affine mark capacity
`markCap w = (1-w)/2 + g0 - g1 w` of the line `(g0, g1) = (552429/10^7, 7227847/10^8)`:

* `ImprovedInverseMoment F ν C height εm`: the inverse polynomial at the fiber's free width `F.r`,
  `anchorLeft ≤ F.r ≤ anchorTop`, times any selected physical slot product of total width
  `≤ markCap F.r - ν` (the native gates `r + 2S < 1, 2r + 8S < 3` are replaced by this);
* `ImprovedOrdinaryMoment F ν C height εm`: the ordinary two-factor product at the fiber's plain
  length `F.m` (doubled width `w = 2 F.m`, `anchorLeft ≤ w ≤ anchorTop`) times any selected slot
  product of total width `≤ markCap w - ν`.

Each is the literal second moment over `F.rows` with all log-derivatives `n ≤ 2` (resp. `j + k ≤ 2`),
real parts `s ∈ [0,1]` and heights `|t| ≤ height`, bounded by `C U^(1+εm)` (the shape of the native
fields of `Moments`). Only these restricted ranges are used by the count.

`ImprovedFineInput S` is the uniform version on the batches of one weighted source (the analogue of
`WeightedAffineFineInput`): constants before the scale, polynomial in the height, error `D.t` and slot
slack `ν = D.t`. `ImprovedFiberMoments` quantifies it as the native ordinary source is quantified after
transport: for each error `ε > 0` a mesh is chosen first, and then every weighted source whose data
have error `ε` and slot lengths below `mesh/200` qualifies.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Interface
noncomputable section

open scoped Classical BigOperators
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily Cycle25ProbeFinalAssembly ProbeFinalAssembly
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource

/-- The left end `1467/2000` of the anchor interval. -/
def anchorLeft : ℝ := 1467/2000
/-- The top `311/400` of the anchor interval. -/
def anchorTop : ℝ := 311/400
/-- The constant of the line of the anchor gain used by the count. -/
def lineG0 : ℝ := 552429/10000000
/-- The slope of the line of the anchor gain used by the count. -/
def lineG1 : ℝ := 7227847/100000000
/-- The affine mark capacity at width `w`: `(1-w)/2 + g0 - g1 w`. -/
def markCap (w : ℝ) : ℝ := (1-w)/2+lineG0-lineG1*w

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The improved inverse marked moment on one fiber: free width `F.r ∈ [anchorLeft, anchorTop]`,
selected slots of total width at most `markCap F.r - ν`. -/
def ImprovedInverseMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (ν C height εm : ℝ) : Prop :=
  anchorLeft ≤ F.r → F.r ≤ anchorTop →
  ∀ selected : Finset Slot, selected ⊆ F.slots →
    (∑ s∈selected, F.widths s) ≤ markCap F.r-ν →
    ∀ n : ℕ, n ≤ 2 → ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

/-- The improved ordinary two-factor moment on one fiber: doubled width `2 F.m ∈ [anchorLeft,
anchorTop]`, selected slots of total width at most `markCap (2 F.m) - ν`. -/
def ImprovedOrdinaryMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (ν C height εm : ℝ) : Prop :=
  anchorLeft ≤ 2*F.m → 2*F.m ≤ anchorTop →
  ∀ selected : Finset Slot, selected ⊆ F.slots →
    (∑ s∈selected, F.widths s) ≤ markCap (2*F.m)-ν →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        (U^F.m) s t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        (U^F.m) s t*F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

/-- Both improved fiber moments (slack `ν`, constant `C`, height bound `height`, error `εm`). -/
structure ImprovedMoments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (ν C height εm : ℝ) : Prop where
  inverse : ImprovedInverseMoment F ν C height εm
  ordinary : ImprovedOrdinaryMoment F ν C height εm

theorem ImprovedMoments.mono_constant {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {ν C C' height εm : ℝ} (h : ImprovedMoments F ν C height εm) (hU : 0 ≤ U) (hC : C ≤ C') :
    ImprovedMoments F ν C' height εm := by
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
def ImprovedFineInput {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D) : Prop :=
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
    ImprovedMoments (B.fiber bin label left right hne) D.t (C*(1+height)^J) height D.t

/-- **The improved fiber moments consumed by the improved count windows.** For every error `ε > 0`
there is a mesh such that every weighted source whose moment data have error `D.t = ε` and slot
lengths `D.ell j ≤ mesh/200` satisfies `ImprovedFineInput`. -/
def ImprovedFiberMoments : Prop :=
  ∀ε : ℝ, 0 < ε → ∃mesh : ℝ, 0 < mesh ∧
    ∀{D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D),
      D.t = ε → (∀j, D.ell j ≤ mesh/200) → ImprovedFineInput S

end
end Qrh.MarkedAnchor.Interface
