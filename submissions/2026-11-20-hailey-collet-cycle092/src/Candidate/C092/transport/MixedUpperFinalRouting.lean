/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Frozen descriptor classification at the actual Q1 row budget. -/
import Candidate.C092.transport.MixedUpperFinalCentral
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090

/-- The same original full phase mean and exact predecessor offset appear
in both the finite classification and the native centered count. -/
def bankScore {Label : Type*} {N : ℕ} (U δ p t₀ γ factor : ℝ)
    (σ : Descriptor Label N) (j : Offset) : ℝ :=
  δ*MixedCenteredFaces.center (Return.kI p) (inverseLength U σ j) (ordinaryLength U σ j)
    (t₀/3) (factor*max 0 (offset γ j-γ/65536-3*witnessCollar))

/-- This is a deterministic predicate of the frozen original response bank.
It is fixed before any error-prime mask or coefficient tuple is selected. -/
def remainingMiddle {Label : Type*} {N : ℕ} (U δ p t₀ γ factor budget : ℝ)
    (σ : Descriptor Label N) : Prop :=
  ∃j : Offset,firstShort (inverseLength U σ)=some j ∧
    centralLengths (inverseLength U σ j) (ordinaryLength U σ j) ∧
    bankScore U δ p t₀ γ factor σ j<4*budget/3

/-- Every excluded common class has a native source route: all-long,
one of four outside anchors, or a genuine sufficient centered saving. -/
theorem not_remaining_cases {Label : Type*} {N : ℕ} (U δ p t₀ γ factor budget : ℝ)
    (σ : Descriptor Label N) (hnot : ¬remainingMiddle U δ p t₀ γ factor budget σ) :
    firstShort (inverseLength U σ)=none ∨
      (∃j : Offset,firstShort (inverseLength U σ)=some j ∧
        ¬centralLengths (inverseLength U σ j) (ordinaryLength U σ j)) ∨
      (∃j : Offset,firstShort (inverseLength U σ)=some j ∧
        centralLengths (inverseLength U σ j) (ordinaryLength U σ j) ∧
        4*budget/3 ≤ bankScore U δ p t₀ γ factor σ j) := by
  classical
  cases he:firstShort (inverseLength U σ) with
  | none => exact Or.inl rfl
  | some j =>
    by_cases hc:centralLengths (inverseLength U σ j) (ordinaryLength U σ j)
    · exact Or.inr (Or.inr ⟨j,rfl,hc,le_of_not_gt (fun hs=>hnot ⟨j,he,hc,hs⟩)⟩)
    · exact Or.inr (Or.inl ⟨j,rfl,hc⟩)

#print axioms not_remaining_cases
end
end QRH.Cycle092.MixedUpperFinal
