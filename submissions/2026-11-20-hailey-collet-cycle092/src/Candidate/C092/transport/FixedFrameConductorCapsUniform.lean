/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Uniform completion gates for all actual selected fixed frames. -/
import Candidate.C092.transport.FixedFrameConductorCapsRows
import Candidate.C092.transport.FixedFrameConductorCapsAllocations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Cycle092.SignedCenter
open CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFrameConductorCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def uniformExponent (Nmax : ℕ) (Bmask : ℝ) : ℝ := (Nmax:ℝ)+3*Bmask+128

/-- Nmax and Bmask are chosen before Z. Every selected slot count and every
native class/label/B/E allocation is quantified after the one threshold. -/
theorem eventually_uniform_allocation_budget (Nmax : ℕ) (Bmask : ℝ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ {L mesh : ℝ} (θ : GData L), θ.N≤Nmax → θ.Bmask≤Bmask →
      ∀ (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z) (η : Character) (x : GLabel θ mesh Z),
      Fits η rs x → s.Fhole=1 → (s.R.absNorm:ℝ)≤Z^(8:ℝ) → (∀i,s.P i≤Z) →
      (x.G.absNorm:ℝ)≤Z^(uniformExponent Nmax Bmask) ∧
      (x.D.absNorm:ℝ)≤Z^(uniformExponent Nmax Bmask) ∧
      ∀ (B : commonAlloc s x.G) (E : fullPrimaryAlloc s x.G B x.D),
        (s.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*s.P i.val.val)*s.R.absNorm*
          x.G.absNorm*x.D.absNorm ≤ Z^(uniformExponent Nmax Bmask) := by
  filter_upwards [eventually_ge_atTop ((2:ℝ)^Nmax),eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro L mesh θ hN hB s rs η x hf hhole hR hP
  have hpow : (2:ℝ)^θ.N≤Z :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN).trans hconst
  have hpay := allocation_budget θ hZ hpow s rs η x hf hhole hR hP
  have hn : (θ.N:ℝ)≤Nmax := by exact_mod_cast hN
  have hb : budgetExponent θ≤uniformExponent Nmax Bmask := by
    unfold budgetExponent uniformExponent
    linarith
  have hm := Real.rpow_le_rpow_of_exponent_le hZ.le hb
  exact ⟨hpay.1.trans hm,hpay.2.1.trans hm,fun B E=>(hpay.2.2 B E).trans hm⟩

/-- The H15 FixedCubeDatum's real, prepacked conductor is bounded by the
same exponent used for all allocations and both native ideal caps. -/
theorem eventually_uniform_fixed_datum (η : Character) (Nmax : ℕ) (Bmask : ℝ) (hB : 0≤Bmask) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀ (C E : Id) (hC : Supported C) (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C E))
      (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C E hC U ξ₁ ξ₂)
      (ρ : Character), (ρ=F.left ∨ ρ=F.right) → (C.absNorm:ℝ)≤Z^(8:ℝ) →
      ∀ {L mesh : ℝ} (θ : GData L),θ.N≤Nmax → θ.Bmask≤Bmask →
      ∀ (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z),
      Fits η rs x → commonH rs≤19/10 → s.Fhole=1 → (s.R.absNorm:ℝ)≤Z^(8:ℝ) →
      (∀i,s.P i≤Z) → ∀ (ξ χ : RayFourExpansion.RayCharacter) (D : FixedCubeDatum),
      D.η=childCharacter (childCharacter ρ ξ) χ → D.m=nativeSourceMask s → D.A=x.twist →
      ((Ideal.span {D.z}).absNorm:ℝ)≤2*dyadicScale (x.n 1) →
      (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ)≤Z^(uniformExponent Nmax Bmask) ∧
      (x.G.absNorm:ℝ)≤Z^(uniformExponent Nmax Bmask) ∧
      (x.D.absNorm:ℝ)≤Z^(uniformExponent Nmax Bmask) ∧
      ∀ (B : commonAlloc s x.G) (E : fullPrimaryAlloc s x.G B x.D),
        (s.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*s.P i.val.val)*s.R.absNorm*
          x.G.absNorm*x.D.absNorm≤Z^(uniformExponent Nmax Bmask) := by
  filter_upwards [eventually_actual_conductor η,eventually_uniform_allocation_budget Nmax Bmask] with Z hc ha
  refine ⟨hc.1,?_⟩
  intro C E hC U ξ₁ ξ₂ F ρ hρ hcap L mesh θ hN hBM s rs x hf hH hhole hR hP ξ χ D hη hm hA hz
  have hrow := hc.2 C E hC U ξ₁ ξ₂ F ρ hρ hcap s rs x hf hH hR ξ χ D.z hz
  rw [←hη,←hm,←hA] at hrow
  have hb : (27:ℝ)≤uniformExponent Nmax Bmask := by
    unfold uniformExponent
    have := Nat.cast_nonneg (α:=ℝ) Nmax
    linarith
  exact ⟨hrow.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le hb),
    ha.2 θ hN hBM s rs η x hf hhole hR hP⟩

#print axioms eventually_uniform_allocation_budget
#print axioms eventually_uniform_fixed_datum
end QRH.Cycle092.FixedFrameConductorCaps
