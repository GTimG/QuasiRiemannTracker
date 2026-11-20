/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The native profile-uniform source energy is the literal original finite
StrongPair source on the same sparse rows and complete surviving subproduct.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafShort
import Candidate.C092.transport.TerminalProfileUniformSup
import Candidate.C092.transport.StrongPairFinite
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.TerminalProfileUniform
local notation "O" => HeckeFamily.O

/-- No new profile or row is substituted: the native zero-height short
factor is exactly the original independent-height factor in norm. -/
theorem terminal_native_plain_energy {Slot : Type} [Fintype Slot]
    {U Bmask bPhi : ℝ} (s : NaturalState U Bmask bPhi)
    (rows : Finset FreeRow) (hrows : ∀u∈rows,s.radial.keep u.val)
    (η₁ η₂ : Character) (hchar : s.character=η₂)
    (hmask : s.mask=fixedBadMask*idealGenerator 1)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (A B : ℝ) (hA : 0<A)
    (hs : Function.support (W₂:ℝ→ℂ)⊆Set.Icc A B)
    (t₁ t₂ X₁ X₂ : ℝ) (hX₂ : 0<X₂) (V : ℝ→ℂ)
    (T : Finset Slot) (mark : Slot→FreeRow→ℂ) :
    nativeEnergy rows η₁ η₂ (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1)
      (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1) Subtype.val
      (fun _=>t₁) (fun _=>X₁) (fun _=>X₂) (fun _=>0) (fun _=>t₂) V W₁ W₂
      (fun _=>false) (fun _=>1) (fun _=>1) (fun u=>∏i∈T,mark i u)=
    StrongPair.finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  unfold nativeEnergy StrongPair.finiteEnergyOn
  apply Finset.sum_congr rfl
  intro u hu
  have hn := terminal_original_short_twist s u (hrows u hu) W₂ A B hA hs (W₂.smooth ⊤) t₂ X₂ hX₂
  rw [hchar,hmask] at hn
  simp only [shortProfile,Bool.false_eq_true,ite_false,norm_mul,mul_pow,norm_prod,Finset.prod_pow]
  rw [←hn]

/-- The genuine unit-profile supplier output returns to the literal
common-pair physical source with one fixed Fourier weight. -/
theorem terminal_common_pair_finite_payment
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) {C : ℝ} (hC : 0<C) :
    ∃ J : ℕ,∃ K : ℝ,0<K ∧
    ∀ (Slot : Type) [Fintype Slot] (U Bmask bPhi : ℝ) (s : NaturalState U Bmask bPhi)
      (rows : Finset FreeRow) (hrows : ∀u∈rows,s.radial.keep u.val)
      (η₁ η₂ : Character),s.character=η₂ → s.mask=fixedBadMask*idealGenerator 1 →
    ∀ (T : Finset Slot) (mark : Slot→FreeRow→ℂ) (t₁ t₂ X₁ X₂ : ℝ),0<X₂ →
    ∀ (V : ℝ→ℂ) (e : Fin 2×Fin 2) (tau : ℝ×ℝ) (E : ℝ),0≤E →
      nativeEnergy rows η₁ η₂ (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1)
        (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1) Subtype.val
        (fun _=>t₁) (fun _=>X₁) (fun _=>X₂) (fun _=>0) (fun _=>t₂) V
        ((unitPair S C (QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau)).profile 0)
        ((unitPair S C (QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau)).profile 1)
        (fun _=>false) (fun _=>1) (fun _=>1) (fun u=>∏i∈T,mark i u)≤E →
      StrongPair.finiteEnergyOn T rows η₁ η₂
        ((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).profile 0)
        ((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).profile 1)
        t₁ t₂ X₁ X₂ mark≤K*QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.pairWeight J tau*E := by
  obtain ⟨J,K,hK,hpayment⟩:=native_common_pair_energy S hS hC
  refine ⟨J,K,hK,?_⟩
  intro Slot _ U Bmask bPhi s rows hrows η₁ η₂ hchar hmask T mark t₁ t₂ X₁ X₂ hX₂ V e tau E hE hunit
  have h:=hpayment FreeRow rows η₁ η₂ (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1)
    (fun _=>fixedBadMask*idealGenerator 1) (fun _=>1) Subtype.val
    (fun _=>t₁) (fun _=>X₁) (fun _=>X₂) (fun _=>0) (fun _=>t₂) V e tau
    (fun _=>false) (fun _=>1) (fun _=>1) (fun u=>∏i∈T,mark i u) E hE hunit
  rw [terminal_native_plain_energy s rows hrows η₁ η₂ hchar hmask _ _ (1/4) (9/4)
    (by norm_num) ((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).support 1)
    t₁ t₂ X₁ X₂ hX₂ V T mark] at h
  exact h

#print axioms terminal_common_pair_finite_payment
#print axioms terminal_native_plain_energy
end
end QRH.Cycle092.RegularColoredForward
