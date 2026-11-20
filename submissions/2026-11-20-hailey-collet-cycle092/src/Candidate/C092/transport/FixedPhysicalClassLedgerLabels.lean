/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M2, label assembly, part 6: the class objects of one residual split and the root data.

For a residual FP source `s` on `Fin N` (frame source `rs`), the base `ψ = childCharacter P.base ξ`,
and a dyad vector `n`:
* `classLabel n l : BlockLabel` — the label `(p, U)` with its exceptional family
  (`exists_exceptional_family`), rows restricted to the row annulus `N(z) < 2^{n₁}`;
* `frameData g n χ k : LabelData` — the frame label of `(label, t₂)` on the column `g l`
  (`g = p.1` or `p.2`), raised dyad `topDyad(Z^{2a-k+mesh}, N(A₂))`, prefactor `1`;
* `RootLabelData`: every datum the root (WP-K2 / WP-M) must supply for one split, with the
  per-field lemmas proving the hypotheses of `class_label_bound` from it. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerClasses

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace QRH.Cycle092.FixedPhysicalClassLedger
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondEnergySplit CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentRestrictedEnergy RayFourExpansion
open CenteredMomentSecondWholeKernel CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondActiveDyadic CenteredMomentMobiusRegroup CenteredMomentSecondExceptionalFamily
open CenteredMomentChildRows CenteredMomentFirstPhysicalSource CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O


open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
/-- The class rows of a label. -/
def classRows (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (R : ℝ) (S : Finset Id)
    (l : Lab S) (n : Fin 4 → ℤ) : Finset O :=
  (partRows true ψ χ₀ Q m l.1.val.1 l.1.val.2 l.2 R).filter
    (fun z => normValue z < dyadicScale (n 1))

/-- **The `BlockLabel` of a label in the class `n`.** -/
def classLabel (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (Kc R : ℝ) (S : Finset Id)
    (n : Fin 4 → ℤ) (l : Lab S) : BlockLabel ψ χ₀ Q m S where
  C := l.1.val.1
  D := l.1.val.2
  hC := (lab_data S l).1
  hD := (lab_data S l).2.1
  hCD := (lab_data S l).2.2
  U := l.2
  R := R
  rows := classRows ψ χ₀ Q m R S l n
  ρ := fun _ => Real.log (secondEffectiveScale l.1.val.1 l.1.val.2
      (commonFrequencyGenerator l.1.val.1 l.1.val.2 * nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2)
        Kc / dyadicScale (n 0))
  x := fun z => Real.log (normValue z / dyadicScale (n 1))
  τ := famτ ψ S l
  hτ := (famSpec ψ S l).height_eq
  hrows := by
    intro z hz
    have hz1 := (Finset.mem_filter.mp hz).1
    exact ⟨sourceRows_nonzero _ _ _ _ z (Finset.mem_filter.mp hz1).1,
      by simpa only [ite_true] using (Finset.mem_filter.mp hz1).2⟩

theorem classBlock_eq (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter) (Q : Id)
    (m : O) (t Kc R : ℝ) (l : Lab S) (n : Fin 4 → ℤ) :
    classBlock S β ψ χ₀ Q m t Kc R l n =
      labelBlock ψ t S β (classLabel ψ χ₀ Q m Kc R S n l).C (classLabel ψ χ₀ Q m Kc R S n l).D
        (classLabel ψ χ₀ Q m Kc R S n l).hC (classLabel ψ χ₀ Q m Kc R S n l).hD
        (classLabel ψ χ₀ Q m Kc R S n l).U (classLabel ψ χ₀ Q m Kc R S n l).R
        (classLabel ψ χ₀ Q m Kc R S n l).rows ballProfile
        (dyadicScale (n 0) * dyadicScale (n 1) / (dyadicScale (n 2) * dyadicScale (n 3)))
        (classLabel ψ χ₀ Q m Kc R S n l).ρ (classLabel ψ χ₀ Q m Kc R S n l).x
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold classBlock
  exact labelBlock_rows_filter ψ t S β _ _ _ _ l.2 R _ ballProfile _ _ _ _ _ (dyadicScale_pos _)

theorem classLabel_pool (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (Kc R : ℝ)
    (S : Finset Id) (n : Fin 4 → ℤ) (l : Lab S) :
    (classLabel ψ χ₀ Q m Kc R S n l).pool = labelPool S l := rfl


#print axioms classLabel
#print axioms classBlock_eq
end
end QRH.Cycle092.FixedPhysicalClassLedger
