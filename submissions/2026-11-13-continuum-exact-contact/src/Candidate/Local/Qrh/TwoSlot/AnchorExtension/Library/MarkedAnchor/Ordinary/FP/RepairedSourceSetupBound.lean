/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Arvi (2026-10-25): the contrary hypothesis `theta < beta` is replaced by
`51/100 ≤ beta`, the only consequence of it that the source construction uses.
Assembles the retained source energy from the reference estimate and
the explicit raw-side input. The original radial diagonal control is used
once, and the two ordinary profiles retain degree two on each branch.
Modified by Sil (2026-10-26): uniform_setup_core G eps meshCap (ProviderAt G eps meshCap) gives the retained source energy at Z^(1+4 eps); uniform_setup_of_side_provider instantiates the root chain at eps/12 (Lcap = windowCap G N (eps/12), slot widths <= min (mesh G (eps/12)) meshCap, s0 <= markedWidth) and keeps the conclusion at Z^(1+eps); setup_mesh_of_contrary extracts meshCap from ContraryRawSideProvider G before the ambient type; the parametric uniform_root_family_dispatch G.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSetupBound`; the reference lane
`hlane : ReferenceEnergyFine D` is threaded through to the family dispatch with the core's own
`bΦ η η₀ Q0`, `V`, `hfreq`; the slot widths are also capped by `laneMesh hlane (ω + ε/100)`, the
inner `Q` satisfies `internalQ Q η₀ = Q0`, and the reference height is `height 0 V`
(`reference_height_bound_V`).
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RepairedSourceActualBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSetupBound
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedFirstProfileEnvelope
open RestoredRootDictionary RestoredRootEnergy RestoredInitialSource
open Qrh.MarkedAnchor.Ordinary.RootParameters RepairedSourceSideSupply RepairedSourceProfiles RepairedSourceRootGeometry
open RepairedSourceActualBall RecenteredRootSetup RecenteredRootFixedMajorant RecenteredRootFamilyDispatch
open CenteredMomentAllocatedNaturalRadial
open QuadraticInitialBound
open RecenteredRootReferenceBound Qrh.MarkedAnchor.Ordinary.Reference CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqSetupBound {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance instFiniteQuotSetupBound (M : Id) [NeZero M] : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

set_option maxHeartbeats 1800000 in
/-- Core: the whole root chain at the RootInput loss `ε` (contract loss `3ε`), output `Z^(1+4ε)`. -/
theorem uniform_setup_core {D : StepData} (G : StepGates D) (hlane : ReferenceEnergyFine D)
    (ε : ℝ) (hε : 0 < ε) (meshCap : ℝ) (hsupply : ProviderAt G ε meshCap) (α : Type) [Fintype α]
    (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q0 : Id) [NeZero Q0]
    (hQt : Q0 ≠ ⊤) (hQ72 : Q0 ≤ Ideal.span {(72:O)}) (hQM : Q0 ≤ M) (hQη : Q0 ≤ η₀.modulus) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H D T0,
      s.Z=Z → s.W=W → s.η₀=η₀ → s.Lcap=windowCap G (Fintype.card α) ε →
    ∀ V : ℝ, 0 ≤ V → (∀i,|s.v i| ≤ V) →
      (∀i,s.w i ≤ min (min (mesh G ε) meshCap) (laneMesh hlane (omegaLoss G ε+ε/100))) → D.s₀ ≤ markedWidth M H s →
    ∀ Q : Id, internalQ Q η₀ = Q0 → ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ →
      (∀x,0 ≤ (Φ x).re) → ∀ rows : Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤
        C*diagonalControl Φ*(s.p.control control)^2*(1+|s.t|+V)^J*Z^(1+4*ε) := by
  obtain ⟨Jb,Sb,Cb,hCb,hball⟩ := uniform_actual_ball_of_side_provider G ε hε meshCap hsupply α
    M H hH W hW hWs bΦ hbΦ η η₀ Q0 hQt hQ72 hQM hQη
  obtain ⟨Jr,Sr,Cr,hCr,href⟩ := uniform_root_family_dispatch (α:=α) M H hH G hlane W hW hWs
    (windowCap G (Fintype.card α) ε) ε (windowCap_ge_eight G _ ε hε) hε bΦ hbΦ η η₀ Q0 hQt hQ72 hQM hQη
  let Cf := Cr*2^Jr
  have hCf : 0 < Cf := mul_pos hCr (by positivity)
  let Cout := 2*(Cb+Cf)
  have hCout : 0 < Cout := by dsimp only [Cout];positivity
  refine ⟨Jb+Jr,Sb∪Sr,Cout,hCout,?_⟩
  filter_upwards [hball,href] with Z hb hr
  refine ⟨hb.1,?_⟩
  intro T0 s hsZ hsW hsη hLc V hV hfreq hwm2 hs₀ Q hQ Φ hΦs hΦ rows
  have hwm : ∀ i, s.w i ≤ min (mesh G ε) meshCap := fun i => (hwm2 i).trans (min_le_left _ _)
  have hwl : ∀ i, s.w i ≤ laneMesh hlane (omegaLoss G ε+ε/100) := fun i => (hwm2 i).trans (min_le_right _ _)
  have hdiag := diagonalControl_nonneg Φ
  let B := (s.p.control (Sb∪Sr))^2*(1+|s.t|+V)^(Jb+Jr)*Z^(1+4*ε)
  have hB : 0 ≤ B := by
    have hh := (root_height s.t V hV).1
    have hz := zero_lt_one.trans hr.1
    dsimp only [B]
    positivity
  have htarget : Cout*diagonalControl Φ*B=
      Cout*diagonalControl Φ*(s.p.control (Sb∪Sr))^2*(1+|s.t|+V)^(Jb+Jr)*Z^(1+4*ε) := by
    dsimp only [B]
    ring
  rw [←htarget]
  by_cases hsmall : s.Y₁ ≤ comparisonScale (9/4) ∨ s.Y₂ ≤ comparisonScale (9/4)
  · have he := s.initial_energy_small hH η Q Φ rows hsmall
    rw [←hsZ]
    rw [he]
    exact mul_nonneg (mul_nonneg hCout.le hdiag) hB
  · have hn₁ : comparisonScale (9/4) < s.Y₁ := lt_of_not_ge (fun h => hsmall (Or.inl h))
    have hn₂ : comparisonScale (9/4) < s.Y₂ := lt_of_not_ge (fun h => hsmall (Or.inr h))
    have hballs := hb.2 T0 s hsZ hsW hsη hLc V hV hfreq hwm hs₀ hn₁ hn₂
    have hdispatch := hr.2 T0 s hsZ hsW hLc hsη hwl V hV hfreq hn₁ hn₂ Q hQ Φ hΦs hΦ rows
    have hbmono := profile_budget_mono s.p s.t V Z (1+4*ε) (1+4*ε) hV hr.1.le
      (by linarith) Jb (Jb+Jr) (Nat.le_add_right _ _) Sb (Sb∪Sr) Finset.subset_union_left
    have hrmono := profile_budget_mono s.p s.t V Z (1+omegaLoss G ε+ε/100) (1+4*ε)
      hV hr.1.le (by linarith [(outer_loss_budget G ε hε).2.1]) Jr (Jb+Jr)
      (Nat.le_add_left _ _) Sr (Sb∪Sr) Finset.subset_union_right
    have hrefheight := reference_height_bound_V s.p s.t V hV Jr Sr Cr hCr.le
    have hrefcost : profileCost M H G s ε Jr Sr Cr V ≤ Cf*B := by
      have hzpow : 0 ≤ Z^(1+omegaLoss G ε+ε/100) := Real.rpow_nonneg (zero_lt_one.trans hr.1).le _
      calc
        profileCost M H G s ε Jr Sr Cr V ≤ Cf*((s.p.control Sr)^2*(1+|s.t|+V)^Jr*Z^(1+omegaLoss G ε+ε/100)) := by
          have he := mul_le_mul_of_nonneg_right hrefheight hzpow
          simpa only [profileCost,Profiles.control,hsZ,Cf,mul_assoc] using he
        _ ≤ Cf*B := mul_le_mul_of_nonneg_left hrmono hCf.le
    have hbpay {r : Source (RestoredRootDictionary.remainingSet s.r s.A) (1/4) (9/4)}
        (he : fullBallCost r (by norm_num) η (bΦ*Z) ≤ Cb*(s.p.control Sb)^2*(1+|s.t|+V)^Jb*Z^(1+4*ε)) :
        fullBallCost r (by norm_num) η (bΦ*Z) ≤ Cb*B := by
      apply he.trans
      simpa only [mul_assoc,B] using mul_le_mul_of_nonneg_left hbmono hCb.le
    by_cases hhigh : NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s)
    · by_cases hshort : s.Y₁ ≤ rootReference M H G s ε ∨ s.Y₂ ≤ rootReference M H G s ε
      · have he := (hdispatch.2 hs₀ hhigh).1 hshort
        apply he.trans
        have hh := mul_le_mul_of_nonneg_left hrefcost hdiag
        have hcomp : Cf ≤ Cout := by dsimp only [Cout];linarith [hCb,hCf]
        have hp := mul_le_mul_of_nonneg_right hcomp (mul_nonneg hdiag hB)
        nlinarith
      · have h₁ : rootReference M H G s ε ≤ s.Y₁ := (lt_of_not_ge (fun h => hshort (Or.inl h))).le
        have h₂ : rootReference M H G s ε ≤ s.Y₂ := (lt_of_not_ge (fun h => hshort (Or.inr h))).le
        have he := (hdispatch.2 hs₀ hhigh).2 h₁ h₂
        have hbc := hbpay (hballs.2 hhigh h₁ h₂)
        apply he.trans
        have hh := mul_le_mul_of_nonneg_left (add_le_add hbc hrefcost)
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hdiag)
        convert hh using 1 <;> (try simp only [Cout]) <;> ring
    · have he := hdispatch.1 hhigh
      have hbc := hbpay (hballs.1 hhigh)
      apply he.trans
      have hh := mul_le_mul_of_nonneg_left hbc hdiag
      have hcomp : Cb ≤ Cout := by dsimp only [Cout];linarith [hCb,hCf]
      have hp := mul_le_mul_of_nonneg_right hcomp (mul_nonneg hdiag hB)
      nlinarith

set_option maxHeartbeats 1800000 in
/-- Assembles the retained source energy from the reference estimate and the explicit
raw-side input, at the outer loss `ε`: the root chain (mesh, window cap, centering,
RootInput) is instantiated at `ε/12`, so the contract loss is `3·(ε/12) = ε/4` and the slot
widths are capped by `min (mesh G (ε/12)) meshCap` and by the lane mesh
`laneMesh hlane (omegaLoss G (ε/12) + ε/12/100)`. -/
theorem uniform_setup_of_side_provider {D : StepData} (G : StepGates D) (hlane : ReferenceEnergyFine D)
    (ε : ℝ) (hε : 0 < ε) (meshCap : ℝ) (hsupply : ProviderAt G (ε/12) meshCap) (α : Type) [Fintype α]
    (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q0 : Id) [NeZero Q0]
    (hQt : Q0 ≠ ⊤) (hQ72 : Q0 ≤ Ideal.span {(72:O)}) (hQM : Q0 ≤ M) (hQη : Q0 ≤ η₀.modulus) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H D T0,
      s.Z=Z → s.W=W → s.η₀=η₀ → s.Lcap=windowCap G (Fintype.card α) (ε/12) →
    ∀ V : ℝ, 0 ≤ V → (∀i,|s.v i| ≤ V) →
      (∀i,s.w i ≤ min (min (mesh G (ε/12)) meshCap) (laneMesh hlane (omegaLoss G (ε/12)+ε/12/100))) →
      D.s₀ ≤ markedWidth M H s →
    ∀ Q : Id, internalQ Q η₀ = Q0 → ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ →
      (∀x,0 ≤ (Φ x).re) → ∀ rows : Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤
        C*diagonalControl Φ*(s.p.control control)^2*(1+|s.t|+V)^J*Z^(1+ε) := by
  obtain ⟨J,control,C,hC,hcore⟩ := uniform_setup_core G hlane (ε/12) (by positivity) meshCap hsupply α
    M H hH W hW hWs bΦ hbΦ η η₀ Q0 hQt hQ72 hQM hQη
  refine ⟨J,control,C,hC,?_⟩
  filter_upwards [hcore] with Z hz
  refine ⟨hz.1,?_⟩
  intro T0 s hsZ hsW hsη hLc V hV hfreq hwm hs₀ Q hQ Φ hΦs hΦ rows
  apply (hz.2 T0 s hsZ hsW hsη hLc V hV hfreq hwm hs₀ Q hQ Φ hΦs hΦ rows).trans
  have hZ1 : 1 ≤ Z := by linarith [hz.1]
  have hpow : Z^(1+4*(ε/12)) ≤ Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hh : 0 ≤ 1+|s.t|+V := by positivity
  have hd := diagonalControl_nonneg Φ
  have h0 : 0 ≤ C*diagonalControl Φ*(s.p.control control)^2*(1+|s.t|+V)^J := by positivity
  exact mul_le_mul_of_nonneg_left hpow h0

/-- The slot-width cap is exported before the ambient type (it depends only on `ε`). -/
theorem setup_mesh_of_contrary {D : StepData} (G : StepGates D)
    (hsupply : ContraryRawSideProvider G) (hcontra : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (ε : ℝ) (hε : 0 < ε) : ∃ meshCap : ℝ, 0 < meshCap ∧ ProviderAt G (ε/12) meshCap :=
  hsupply hcontra (ε/12) (by positivity)

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSetupBound
