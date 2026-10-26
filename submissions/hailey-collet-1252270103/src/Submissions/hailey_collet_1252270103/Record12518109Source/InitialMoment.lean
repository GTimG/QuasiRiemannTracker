/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The literal initial-energy interface follows Cycle61.Moment.InitialAffineContract;
the six source-domain constants are explicit parameters. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.InitialAffineContract

set_option autoImplicit false

namespace QRH.Record12518109Source
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

structure SourceFace where
  B : ℝ
  lam : ℝ
  plainLo : ℝ
  plainHi : ℝ
  slotLo : ℝ
  slotHi : ℝ

def SourceFace.Admissible (f : SourceFace) (m₁ m₂ s M : ℝ) : Prop :=
  f.plainLo*M ≤ m₁ ∧ m₁ ≤ f.plainHi*M ∧
  f.plainLo*M ≤ m₂ ∧ m₂ ≤ f.plainHi*M ∧
  f.slotLo*M ≤ s ∧ s ≤ f.slotHi*M ∧
  m₁+m₂+f.lam*s ≤ f.B*M

/-- All parameters and literal energy data are preserved when a source theorem
is restricted to a smaller admitted domain. -/
structure SourceFace.Restricts (strong weak : SourceFace) : Prop where
  plainLo : strong.plainLo ≤ weak.plainLo
  plainHi : weak.plainHi ≤ strong.plainHi
  slotLo : strong.slotLo ≤ weak.slotLo
  slotHi : weak.slotHi ≤ strong.slotHi
  lam : strong.lam ≤ weak.lam
  budget : weak.B-strong.B ≤ (weak.lam-strong.lam)*weak.slotLo

theorem SourceFace.admissible_of_restricts {strong weak : SourceFace}
    (h : strong.Restricts weak) {m₁ m₂ s M : ℝ} (hM : 0 ≤ M)
    (ha : weak.Admissible m₁ m₂ s M) : strong.Admissible m₁ m₂ s M := by
  rcases ha with ⟨h₁lo,h₁hi,h₂lo,h₂hi,hslo,hshi,hbudget⟩
  refine ⟨(mul_le_mul_of_nonneg_right h.plainLo hM).trans h₁lo,
    h₁hi.trans (mul_le_mul_of_nonneg_right h.plainHi hM),
    (mul_le_mul_of_nonneg_right h.plainLo hM).trans h₂lo,
    h₂hi.trans (mul_le_mul_of_nonneg_right h.plainHi hM),
    (mul_le_mul_of_nonneg_right h.slotLo hM).trans hslo,
    hshi.trans (mul_le_mul_of_nonneg_right h.slotHi hM),?_⟩
  have hgap : (weak.B-strong.B)*M ≤ (weak.lam-strong.lam)*s := calc
    (weak.B-strong.B)*M ≤ ((weak.lam-strong.lam)*weak.slotLo)*M :=
      mul_le_mul_of_nonneg_right h.budget hM
    _ = (weak.lam-strong.lam)*(weak.slotLo*M) := by ring
    _ ≤ (weak.lam-strong.lam)*s :=
      mul_le_mul_of_nonneg_left hslo (sub_nonneg.mpr h.lam)
  nlinarith

def countFace : SourceFace :=
  ⟨9763743/10000000,906637/250000,2/5,11/25,17/500,43/1000⟩

def cPlusFace : SourceFace :=
  ⟨12239/12500,372765011/100000000,81/200,11/25,17/500,1/25⟩

def oldWeakFace : SourceFace :=
  ⟨1005451199/1000000000,44999/10000,81/200,11/25,17/500,1/25⟩

theorem count_restricts_cPlus : countFace.Restricts cPlusFace := by
  constructor <;> norm_num [countFace,cPlusFace]

theorem count_restricts_oldWeak : countFace.Restricts oldWeakFace := by
  constructor <;> norm_num [countFace,oldWeakFace]

theorem cPlus_budget_slack :
    countFace.B-cPlusFace.B+(cPlusFace.lam-countFace.lam)*(17/500) =
      (34588587/50000000000 : ℝ) := by norm_num [countFace,cPlusFace]

theorem oldWeak_budget_slack :
    countFace.B-oldWeakFace.B+(oldWeakFace.lam-countFace.lam)*(17/500) =
      (617069/1000000000 : ℝ) := by norm_num [countFace,oldWeakFace]

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- A parameterized bound for the actual initial source. Its natural character,
relative slot coefficients, zeros, initialKeep and whole-product normalization
are the literal data of the established initial energy. -/
def InitialAffineAt (face : SourceFace) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters rayModulus H)
      (w σ v : T → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, σlo ≤ σ i) → (∀ i, σ i ≤ σhi) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    face.Admissible (length Z X₁) (length Z X₂) (∑ i, w i) M →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayModulus H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^degree*Z^(M+ε)

theorem initialAffineAt_restrict {strong weak : SourceFace}
    (hface : strong.Restricts weak) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (hMmin : 0 ≤ Mmin)
    (hsource : InitialAffineAt (α:=α) rayModulus H hH strong W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C) :
    InitialAffineAt (α:=α) rayModulus H hH weak W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
  exact hsource T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂
    (SourceFace.admissible_of_restricts hface (hMmin.trans hMlo) hadm)

end
end QRH.Record12518109Source

#print axioms QRH.Record12518109Source.SourceFace.admissible_of_restricts
#print axioms QRH.Record12518109Source.count_restricts_cPlus
#print axioms QRH.Record12518109Source.count_restricts_oldWeak
#print axioms QRH.Record12518109Source.initialAffineAt_restrict
