/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact homogeneous restoration for the literal finite original pair. -/
import Candidate.C092.transport.RegularColoredTerminalLeafNative
import Candidate.C092.transport.TerminalProfileUniformEnergy
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.TerminalProfileUniform QRH.Cycle092.OrdinaryColumn

/-- The exact two-arm homogeneity, including zero profile controls, on any
original sparse rows and any complete selected common subproduct. -/
theorem terminal_finite_unit_reconstruct {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (rows : Finset FreeRow) (η₁ η₂ : Character)
    (p : Profiles (1/4) (9/4)) (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot→FreeRow→ℂ)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) {C : ℝ} (hC : 0<C) :
    StrongPair.finiteEnergyOn T rows η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark=
      C^4*(p.control S)^2*StrongPair.finiteEnergyOn T rows η₁ η₂
        ((unitPair S C p).profile 0) ((unitPair S C p).profile 1) t₁ t₂ X₁ X₂ mark := by
  have h := actualEnergy_reconstruct rows η₁ η₂
    (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1) (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1)
    (fun u=>u.val) (fun _=>t₁) (fun _=>t₂) (fun _=>X₁) (fun _=>X₂) (fun _=>0)
    (p.profile 0) (p.profile 1) (fun _=>false) (fun _=>0) (fun u=>∏j∈T,mark j u) S hS hC
  simpa only [actualEnergy,actualShort,Bool.false_eq_true,ite_false,norm_mul,mul_pow,norm_prod,
    Finset.prod_pow,StrongPair.finiteEnergyOn,Profiles.control,unitPair] using h

/-- Applying an already proved genuine unit-source output restores the
original physical pair with its true degree-two profile control. -/
theorem terminal_finite_unit_payment {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (rows : Finset FreeRow) (η₁ η₂ : Character)
    (p : Profiles (1/4) (9/4)) (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot→FreeRow→ℂ)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) {C E : ℝ} (hC : 0<C)
    (bound : StrongPair.finiteEnergyOn T rows η₁ η₂
      ((unitPair S C p).profile 0) ((unitPair S C p).profile 1) t₁ t₂ X₁ X₂ mark≤E) :
    StrongPair.finiteEnergyOn T rows η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark≤C^4*(p.control S)^2*E := by
  rw [terminal_finite_unit_reconstruct T rows η₁ η₂ p t₁ t₂ X₁ X₂ mark S hS hC]
  exact mul_le_mul_of_nonneg_left bound (by positivity)

#print axioms terminal_finite_unit_reconstruct
#print axioms terminal_finite_unit_payment
end
end QRH.Cycle092.RegularColoredForward
