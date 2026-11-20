/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P4's canonical regular state and its actual witness height budget. -/
import Candidate.C092.transport.WitnessRowSupActualPair
import Candidate.C092.transport.WitnessRowSupActualReindex

set_option autoImplicit false
namespace QRH.Cycle092.WitnessRowSup.Actual
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness CenteredMomentEnergyState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentDetectorEnergyInitialState
open CenteredMomentInductionEnergy ConcretePrimeRowBridge
open QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

/-- The exact state used by source_core_conductors and regular_core_P4
satisfies the mask and keep contracts of actual_witness_rowwise by definition.
No general puncture-removal or replacement-keep premise is introduced. -/
theorem regular_state_contract (η η₀ : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ U V δ : ℝ) (hU : 1 ≤ U) (hV : 0 ≤ V) (hδ : 0 ≤ δ)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ) (hp : ∀ x,0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ) :
    let s := regularState η (internalQ Q η₀) Φ bΦ U V δ hU hV hδ hs hp hη
    s.puncture=1 ∧ s.mask=fixedBadMask*idealGenerator 1 ∧
      s.fixedModulus=internalQ Q η₀ ∧
      ∀ z,s.radial.keep z ↔ initialKeep s.character (internalQ Q η₀) z :=
  ⟨rfl,rfl,rfl,fun _=>Iff.rfl⟩

/-- Both coordinates and the simplified original-height budget follow from
P4's authentic SupportedWitness fields and the conductor-bank range. -/
theorem P4_witness_coordinates {Label : Type*} {χ : Label→Character}
    {U d dmax τ a ε cutoff : ℝ} {i : ℕ}
    (w : SupportedWitness χ (U^d) a ε cutoff (U^τ) ((U^d)^(τ/(2*dmax))) i)
    (hU : 1 < U) (ha : 0 ≤ a) (hd : d ≤ dmax) (hdmax : 0 < dmax) (hτ : 0 ≤ τ) :
    w.zero.re ∈ Icc (0:ℝ) 1 ∧
      |2*Real.pi*w.nu-w.zero.im| ≤ (2*Real.pi+(3*i : ℕ))*U^τ :=
  ⟨(witness_coordinates w ha).1,
    (witness_coordinates w ha).2.trans (witness_height_budget hU hd hdmax hτ i).2⟩

#print axioms regular_state_contract
#print axioms P4_witness_coordinates
end
end QRH.Cycle092.WitnessRowSup.Actual
