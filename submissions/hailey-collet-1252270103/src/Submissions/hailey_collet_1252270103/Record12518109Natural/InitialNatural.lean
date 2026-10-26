/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Uses the genuine incumbent natural terminal and Cycle61 fixedParentState.
The exact initial energy contract follows InitialMoment/InitialAffineAt,
with natural capacity in place of an affine face. Underlying natural/source
interfaces: OpenAI/math, Apache-2.0; incumbent assembly credits retained in
Record12518109Source.Incumbent. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.DomainCompletion
import Submissions.hailey_collet_1252270103.Record12518109Source.Incumbent
import Submissions.hailey_collet_1252270103.Cycle61.Moment.InitialState

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Natural.InitialNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge
open CenteredMomentPrimeSlot QuadraticInitialBound Cycle61Moment
open QRH.Record12518109Source
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- Literal initial energy under natural capacity. All slot coefficients,
fixed inducing exclusions, original mask and full product normalization are
those of InitialAffineAt. No positive lower plain or total slot width occurs. -/
def InitialNaturalAt (K : ℝ) (W : ℝ → ℂ)
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
    NaturalCapacity K (length Z X₁) (length Z X₂) (∑ i, w i) M →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayModulus H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε)

/-- The natural fallback is supplied by the checked analytic terminal.
The fixed conductor is paid uniformly over the fixed finite character
family before the live slots, masks, derivatives and shortened scales. -/
theorem natural_initial_uniform
    (κI K : ℝ) (hκlo : 7/10 ≤ κI) (hκhi : κI ≤ 3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κI) (hK : 6*κI ≤ K)
    (W : ℝ → ℂ) (aslot bslot a b bΦ mesh lo hi Mmin Mmax ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hbΦ : 0 < bΦ)
    (hmesh : mesh ≤ Cycle25.Energy.commonMesh (Mmax+1) 0 (Mmax+1) (ε/2))
    (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (hε : 0 < ε) (hεone : ε ≤ 1)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (η : Label → Character) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ rayModulus → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ label : Label,
      InitialNaturalAt (α:=α) rayModulus H hH K W bslot a b bΦ mesh lo hi Mmin Mmax
        ε Z (η label) η₀ Q degree S C := by
  have hMmax : 0 < Mmax := hMmin.trans_le hMM
  obtain ⟨degree,S,hinc⟩ := Record12518109SourceLow.incumbent_at (α:=α)
    rayModulus H hH κI hκlo hκhi hκbeta W aslot bslot a b bΦ 0 (Mmax+1)
      lo hi (Mmax+1) (ε/2) haslot hWs hW hbslot ha haUpper hb hbΦ
      (by norm_num) (by linarith) (by positivity) hbeta
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hterminal⟩ := hinc η₀ Q hQR hQ0 hQt hQ72
  refine ⟨C₁,hC₁,?_⟩
  have hanchor := fixed_anchor_width_uniform η Mmin (ε/(2*Mmax)) hMmin (by positivity)
  filter_upwards [hterminal,hanchor] with Z hz hanchor
  refine ⟨hz.1,?_⟩
  intro label T θ w σ v t height hw hwm hσlo hσhi hheight hv width hwidth hwidthmax
    Φ hΦsupport hΦ p X₁ X₂ hX₁ hX₂ hcapacity
  have hwidth0 : 0 ≤ width := hMmin.le.trans hwidth
  let s := fixedParentState (η label) (internalQ Q η₀) Φ bΦ Z width hz.1 hwidth0 hΦsupport hΦ
  have hlog : Real.logb Z ((η label).modulus.absNorm : ℝ) ≤ ε/2 := by
    apply (hanchor.2 label width hwidth).trans
    apply (mul_le_mul_of_nonneg_left hwidthmax (by positivity : 0 ≤ ε/(2*Mmax))).trans_eq
    field_simp
  have hs : s.width ≤ Mmax+1 := by
    dsimp only [s,fixedParentState_width]
    linarith
  have hslots : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hκ : 0 ≤ 6*κI := by linarith
  have hc : length Z X₁+length Z X₂+6*κI*(∑ i,w i) ≤ width := by
    have hmono := mul_le_mul_of_nonneg_right hK hslots
    dsimp only [NaturalCapacity] at hcapacity
    linarith
  have hplain₁ : length Z X₁ ≤ width := by
    nlinarith [length_nonneg Z X₂ hz.1, mul_nonneg hκ hslots]
  have hplain₂ : length Z X₂ ≤ width := by
    nlinarith [length_nonneg Z X₁ hz.1, mul_nonneg hκ hslots]
  have hscale (X : ℝ) (hx : length Z X ≤ width) : X ≤ Z^(Mmax+1) := by
    apply (le_max_right 1 X).trans
    apply (Real.logb_le_iff_le_rpow hz.1 (zero_lt_one.trans_le (le_max_left 1 X))).mp
    change length Z X ≤ Mmax+1
    linarith
  have hwidthle : width ≤ s.width := by
    change width ≤ width+Real.logb Z ((η label).modulus.absNorm : ℝ)
    have hh := s.character_nonneg
    exact le_add_of_nonneg_right hh
  have he := hz.2.2 T θ w σ v t height hw (fun i => (hwm i).trans hmesh)
    hσlo hσhi hheight hv s rfl hs p X₁ X₂ hX₁ hX₂ (hscale X₁ hplain₁) (hscale X₂ hplain₂)
    (hc.trans hwidthle)
  have hExp : s.width+ε/2 ≤ width+ε := by
    change width+Real.logb Z ((η label).modulus.absNorm : ℝ)+ε/2 ≤ _
    linarith
  have hdiag := diagonalControl_nonneg Φ
  apply he.trans
  change C₁*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(s.width+ε/2) ≤ _
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.1.le hExp) (by positivity)

end
end OAI.SevenEighths.Record12518109Natural.InitialNatural
#print axioms OAI.SevenEighths.Record12518109Natural.InitialNatural.natural_initial_uniform
