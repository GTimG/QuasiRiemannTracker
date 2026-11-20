/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original FreeRow witnesses enter P4's O-image without a new choice.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafGuards
import Candidate.C092.transport.StrongPairRegularTerminalOrdinaryApprox
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness ConcretePrimeRowBridge ConcreteTraceCRT HeckeDetectorZeros
open HeckeRowClosure ProbeHighRowFamily CanonicalRowCompletion
open CenteredMomentEnergyBands QRH.Cycle092.WholeSlot
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.LowActual
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.WitnessRowSup.Actual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafReindex_290d5d5c47f00679_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- P4's element rows are precisely the same sparse original source rows.
The supported record, including the selected zero, is transported unchanged. -/
theorem terminal_original_image_witness
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    {U Bmask bstate : ℝ} (s : NaturalState U Bmask bstate) (base : Character)
    (rows : Finset FreeRow) (hrows : ∀u∈rows,s.radial.keep u.val)
    (Z a epsilon cutoff T allowance : ℝ) (i : ℕ)
    (wc : ∀u : rows,SupportedWitness (family M H hH s base
      (naturalRow s.character u.val.val u.val.property.1)) Z a epsilon cutoff T allowance i) :
    let hk : ∀z∈rows.image Subtype.val,s.radial.keep z := fun z hz => by
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      exact hrows u hu
    ∃ ws : ∀z : rows.image Subtype.val,SupportedWitness (family M H hH s base
      (naturalRow s.character z.val (s.row_ne_zero z.val (hk z.val z.property)))) Z a epsilon cutoff T allowance i,
      ∀u : rows,(ws (sourceRowEquiv rows u)).label=(wc u).label ∧
        (ws (sourceRowEquiv rows u)).left=(wc u).left ∧
        (ws (sourceRowEquiv rows u)).right=(wc u).right ∧
        (ws (sourceRowEquiv rows u)).r=(wc u).r ∧
        (ws (sourceRowEquiv rows u)).m=(wc u).m ∧
        (ws (sourceRowEquiv rows u)).zero=(wc u).zero := by
  classical
  dsimp only
  let F := fun z : rows.image Subtype.val => SupportedWitness (family M H hH s base
    (naturalRow s.character z.val (s.row_ne_zero z.val (by
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp z.property
      rw [←he];exact hrows u hu)))) Z a epsilon cutoff T allowance i
  let wc' : ∀u : rows,F (sourceRowEquiv rows u) := wc
  let ws : ∀z,F z := Equiv.piCongrLeft F (sourceRowEquiv rows) wc'
  refine ⟨ws,?_⟩
  intro u
  have he : ws (sourceRowEquiv rows u)=wc u := by
    simpa only [ws,wc'] using Equiv.piCongrLeft_apply_apply F (sourceRowEquiv rows) wc' u
  exact ⟨congrArg (fun w=>w.label) he,congrArg (fun w=>w.left) he,
    congrArg (fun w=>w.right) he,congrArg (fun w=>w.r) he,
    congrArg (fun w=>w.m) he,congrArg (fun w=>w.zero) he⟩

#print axioms terminal_original_image_witness
end
end QRH.Cycle092.RegularColoredForward
