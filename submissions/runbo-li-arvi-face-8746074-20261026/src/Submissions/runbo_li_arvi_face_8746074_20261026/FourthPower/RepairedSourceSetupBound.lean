/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Arvi (2026-10-25): the contrary hypothesis `theta < beta` is replaced by
`51/100 ≤ beta`, the only consequence of it that the source construction uses.
Assembles the retained source energy from the reference estimate and
the explicit raw-side input. The original radial diagonal control is used
once, and the two ordinary profiles retain degree two on each branch.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSourceActualBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSourceSetupBound
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedFirstProfileEnvelope
open RestoredRootDictionary RestoredRootEnergy RestoredInitialSource
open RepairedRootParameters RepairedSourceSideSupply RepairedSourceProfiles RepairedSourceRootGeometry
open RepairedSourceActualBall RecenteredRootSetup RecenteredRootFixedMajorant RecenteredRootFamilyDispatch
open CenteredMomentAllocatedNaturalRadial
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

set_option maxHeartbeats 1800000 in
theorem uniform_setup_of_side_provider
    (hsupply : ContraryRawSideProvider) (hcontra : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (ε : ℝ) (hε : 0 < ε) (α : Type) [Fintype α]
    (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q0 : Id) [NeZero Q0]
    (hQt : Q0 ≠ ⊤) (hQ72 : Q0 ≤ Ideal.span {(72:O)}) (hQM : Q0 ≤ M) (hQη : Q0 ≤ η₀.modulus) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H T0,
      s.Z=Z → s.W=W → s.η₀=η₀ → s.Lcap=windowCap (Fintype.card α) ε →
    ∀ V : ℝ, 0 ≤ V → (∀i,|s.v i| ≤ V) → (∀i,s.w i ≤ mesh ε) →
    ∀ Q : Id, ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ →
      (∀x,0 ≤ (Φ x).re) → ∀ rows : Finset O,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤
        C*diagonalControl Φ*(s.p.control control)^2*(1+|s.t|+V)^J*Z^(1+ε) := by
  obtain ⟨Jb,Sb,Cb,hCb,hball⟩ := uniform_actual_ball_of_side_provider hsupply hcontra ε hε α
    M H hH W hW hWs bΦ hbΦ η η₀ Q0 hQt hQ72 hQM hQη
  obtain ⟨Jr,Sr,Cr,hCr,href⟩ := uniform_root_family_dispatch (α:=α) M H hH W hW hWs
    (windowCap (Fintype.card α) ε) ε (windowCap_ge_eight _ ε hε) hε
  let Cf := Cr*2^Jr
  have hCf : 0 < Cf := mul_pos hCr (by positivity)
  let Cout := 2*(Cb+Cf)
  have hCout : 0 < Cout := by dsimp only [Cout];positivity
  refine ⟨Jb+Jr,Sb∪Sr,Cout,hCout,?_⟩
  filter_upwards [hball,href η bΦ hbΦ] with Z hb hr
  refine ⟨hb.1,?_⟩
  intro T0 s hsZ hsW hsη hLc V hV hfreq hwm Q Φ hΦs hΦ rows
  have hdiag := diagonalControl_nonneg Φ
  let B := (s.p.control (Sb∪Sr))^2*(1+|s.t|+V)^(Jb+Jr)*Z^(1+ε)
  have hB : 0 ≤ B := by
    have hh := (root_height s.t V hV).1
    have hz := zero_lt_one.trans hr.1
    dsimp only [B]
    positivity
  have htarget : Cout*diagonalControl Φ*B=
      Cout*diagonalControl Φ*(s.p.control (Sb∪Sr))^2*(1+|s.t|+V)^(Jb+Jr)*Z^(1+ε) := by
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
    have hballs := hb.2 T0 s hsZ hsW hsη hLc V hV hfreq hwm hn₁ hn₂
    have hdispatch := hr.2 T0 s hsZ hsW hLc hn₁ hn₂ Q Φ hΦs hΦ rows
    have hbmono := profile_budget_mono s.p s.t V Z (1+ε/2) (1+ε) hV hr.1.le
      (by linarith) Jb (Jb+Jr) (Nat.le_add_right _ _) Sb (Sb∪Sr) Finset.subset_union_left
    have hrmono := profile_budget_mono s.p s.t V Z (1+omegaLoss ε+ε/100) (1+ε)
      hV hr.1.le (by linarith [(outer_loss_budget ε hε).2.1]) Jr (Jb+Jr)
      (Nat.le_add_left _ _) Sr (Sb∪Sr) Finset.subset_union_right
    have hrefheight := reference_height_bound s.p s.t V hV Jr Sr Cr hCr.le
    have hrefcost : profileCost M H s ε Jr Sr Cr ≤ Cf*B := by
      have hzpow : 0 ≤ Z^(1+omegaLoss ε+ε/100) := Real.rpow_nonneg (zero_lt_one.trans hr.1).le _
      calc
        profileCost M H s ε Jr Sr Cr ≤ Cf*((s.p.control Sr)^2*(1+|s.t|+V)^Jr*Z^(1+omegaLoss ε+ε/100)) := by
          have he := mul_le_mul_of_nonneg_right hrefheight hzpow
          simpa only [profileCost,Profiles.control,hsZ,Cf,mul_assoc] using he
        _ ≤ Cf*B := mul_le_mul_of_nonneg_left hrmono hCf.le
    have hbpay {r : Source (RestoredRootDictionary.remainingSet s.r s.A) (1/4) (9/4)}
        (he : fullBallCost r (by norm_num) η (bΦ*Z) ≤ Cb*(s.p.control Sb)^2*(1+|s.t|+V)^Jb*Z^(1+ε/2)) :
        fullBallCost r (by norm_num) η (bΦ*Z) ≤ Cb*B := by
      apply he.trans
      simpa only [mul_assoc,B] using mul_le_mul_of_nonneg_left hbmono hCb.le
    by_cases hhigh : NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s)
    · by_cases hshort : s.Y₁ ≤ rootReference M H s ε ∨ s.Y₂ ≤ rootReference M H s ε
      · have he := (hdispatch.2 hhigh).1 hshort
        apply he.trans
        have hh := mul_le_mul_of_nonneg_left hrefcost hdiag
        have hcomp : Cf ≤ Cout := by dsimp only [Cout];linarith [hCb,hCf]
        have hp := mul_le_mul_of_nonneg_right hcomp (mul_nonneg hdiag hB)
        nlinarith
      · have h₁ : rootReference M H s ε ≤ s.Y₁ := (lt_of_not_ge (fun h => hshort (Or.inl h))).le
        have h₂ : rootReference M H s ε ≤ s.Y₂ := (lt_of_not_ge (fun h => hshort (Or.inr h))).le
        have he := (hdispatch.2 hhigh).2 h₁ h₂
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

end
end Candidate.FourthPower.RepairedSourceSetupBound
