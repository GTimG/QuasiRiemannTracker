/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The energy and quantifier telescope are those of Record12518109Source.InitialMoment and Record12518109Existence.UniformSource. The domain is now the ordered P.1 rectangle in either orientation. -/
import Candidate.C092.PhysicalInlet
import Candidate.C092.Induction
set_option autoImplicit false
namespace QRH.Cycle092.NativeStrip
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Cycle090 QRH.SourceCertificate
open Filter
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

def Box (N Y L m₁ m₂ s : ℝ) : Prop :=
  0 ≤ m₁ ∧ 0 ≤ m₂ ∧ ((m₁ ≤ N ∧ m₂ ≤ Y) ∨ (m₁ ≤ Y ∧ m₂ ≤ N)) ∧ 0 ≤ s ∧ s ≤ L

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance c092LocalInst_Candidate_C092_transport_NativeStrip_c3f60d33825ce189_001 : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

def LabelledAt (N Y L : ℝ) (W : ℝ → ℂ)
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
    Box N Y L (length Z X₁) (length Z X₂) (∑ i, w i) →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayModulus H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^degree*Z^(M+ε)

def UnitBox (N Y L : ℝ) (mesh ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H),
  ∀ (W : ℝ→ℂ), ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2≤bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
    Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃controls : Finset (ℕ×ℕ), ∃C : ℝ, 0<C ∧
      ∀ᶠZ : ℝ in atTop,
        LabelledAt (α:=α) rayM H hH N Y L W 2 (1/4) (9/4) bΦ mesh
          (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C

/-- An early mesh exists prior to all the original finite ray, mask and profile data. -/
def UniformBox (n y l : ℝ) : Prop := ∀ ε : ℝ, 0<ε → ∃ mesh : ℝ, 0 < mesh ∧ UnitBox n y l mesh ε

/-- The literal source energy on a symmetric pair of ordered rectangles. -/
theorem uniformBox_of_source {face : SourceFace} {n y l : ℝ} (src : UniformUnitFaceSource face)
    (dom : ∀ m₁ m₂ s, Box n y l m₁ m₂ s → face.Admissible m₁ m₂ s 1) : UniformBox n y l := by
  intro ε hε; obtain ⟨mesh,hm,hsrc⟩ := src ε hε
  refine ⟨mesh,hm,?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨d,S,C,hC,h⟩ := hsrc α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨d,S,C,hC,h.mono ?_⟩
  intro Z hZ T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦ hp p X₁ X₂ h₁ h₂ hadm
  have hM1 := le_antisymm hM' hM; subst M
  exact hZ T θ w σ v t height hw hwm hlo hhi hh hv 1 le_rfl le_rfl Φ hΦ hp p X₁ X₂ h₁ h₂ (dom _ _ _ hadm)

theorem native_box (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y l : ℝ} (hy : sourceY ≤ y) (hy' : y ≤ sourceY/(QRH.SourceCertificate.H:ℝ)) (hn : y ≤ n)
    (hr : n ≤ sourceRatio*y) (hl : l ≤ sourceWidth n y) : UniformBox n y l := by
  let s₀ : ℝ := 1/1000000000
  apply uniformBox_of_source (Qrh.TwoSlot.AnchorContinuum.PositiveSource.source (s:=s₀) (by norm_num [s₀]) (by norm_num [s₀]) hβ)
  intro x z t ht
  obtain ⟨hx,hz,hpair,ht0,htl⟩ := ht
  have hg := QRH.Cycle092Continuation.native_strip_gain hy hy'
  unfold sourceWidth at hl
  norm_num [sourceY,QRH.SourceCertificate.H,u,sourceRatio] at hy hy' hr
  rcases hpair with ⟨hxn,hzy⟩ | ⟨hxy,hzn⟩ <;>
    dsimp [SourceFace.Admissible,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face,s₀] <;>
    refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- P.1 instantiated on genuine energies: only the within-strip analytic increment remains. -/
def OpenWidth (n y : ℝ) : Prop := ∀ l : ℝ, 0 ≤ l → l < sourceWidth n y → UniformBox n y l

theorem all_strips_of_increment (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (increment : ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      OpenWidth (n/(QRH.SourceCertificate.H:ℝ)) (y/(QRH.SourceCertificate.H:ℝ)) → (∀ m, y/(QRH.SourceCertificate.H:ℝ) ≤ m → m ≤ sourceY →
      OpenWidth (max (n/(QRH.SourceCertificate.H:ℝ)) m) (min (n/(QRH.SourceCertificate.H:ℝ)) m)) → OpenWidth n y) :
    ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → OpenWidth n y :=
  QRH.Cycle092Continuation.ordered_source_induction OpenWidth
    (fun _ _ hy hy' hn hr _ _ hl => native_box hβ hy hy' hn hr hl.le) increment

#print axioms native_box
#print axioms all_strips_of_increment
end
end QRH.Cycle092.NativeStrip
