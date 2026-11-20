/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.OrderedPairClosureInduction
import Candidate.C092.transport.OrderedPairPhaseRoot
import Candidate.C092.transport.TinyCoreErasure

set_option autoImplicit false
namespace QRH.Cycle092.OrderedPairPhase
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle092.StrongPair QRH.Cycle092.ReferenceShortP3
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr)

/-- The remaining actual individually phase-aligned centered finite root, only when both
original coordinates are above .115. Its normalizer, original marks, masks,
independent pitches/characters and exceptional keeps are literal. P.3 has
already proved its short-coordinate and equal-product reference pieces. -/
def CenteredAt (N Y l : ℝ) (W : ℝ→ℂ) (bΦ mesh ε Z : ℝ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ (T : Finset Slot) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr) (w σ₁ σ₂ v₁ v₂ : Slot→ℝ)
    (t₁ t₂ height : ℝ),
    (∀ i,0 ≤ w i) → (∀ i,w i ≤  mesh) →
    (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
    (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
    0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) → (∑ i∈T,w i) ≤ l →
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
    length Z X₁ ≤ N → length Z X₂ ≤ Y →
  ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
    (∀ u∈s,rowNorm u ≤ Z) →
    (∀ u∈s,∀ i∈T,‖mark i u‖=
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₁ θ₁ W Z w σ₁ v₁ i) t₁ (Z^(w i))‖) →
    (∀ u∈s,∀ i∈T,‖mark i u‖=
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₂ θ₂ W Z w σ₂ v₂ i) t₂ (Z^(w i))‖) →
    Z^shortWidth < X₁ → Z^shortWidth < X₂ →
    alignedPairEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (Z^shortWidth) (X₁*X₂/Z^shortWidth) mark ≤ 
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*Z^(1+ε)

/-- Early mesh; then finite slot family, ray dictionary and fixed data; then
one finite control set and degree before every live profile, height or row. -/
def CenteredUnitBox (N Y l mesh ε : ℝ) : Prop :=
  ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
  ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr),
  ∀ W : ℝ→ℂ, ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
  ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
    Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ →
    internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
    Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ →
    internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop,
        CenteredAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
          η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C

def CenteredUniformBox (N Y l : ℝ) : Prop :=
  ∀ ε : ℝ,0 < ε → ∃ mesh : ℝ,0 < mesh ∧ CenteredUnitBox N Y l mesh ε


/-- The fixed radial majorant has positive native control. -/
theorem radial_diagonal_ge_one : (1:ℝ) ≤ QuadraticInitialBound.diagonalControl radialMajorant := by
  have h := CenteredMomentEnergyFixedRadialSource.norm_le_diagonalControl radialMajorant 0
  rw [radialMajorant_one 0 (by norm_num)] at h
  simpa using h

/-- A genuine length cap controls the actual positive scale, including
bounded/subunit scales; the original max-one length is not discarded. -/
theorem scale_le_of_length {Z X N : ℝ} (hZ : 1 < Z) (h : length Z X ≤ N) : X ≤ Z^N := by
  exact (le_max_right (1:ℝ) X).trans
    ((Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left _ _))).mp h)

/-- This is an actual source assembly transition: the genuine P.3 short
reference and exact root triangle are invoked internally. The only input
left is the signed centered finite root on the original both-long masks. -/
theorem pair_unit_of_centered
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {N Y l mesh ε : ℝ} (hN : N ≤ 1) (hY : Y ≤ 1) (hNY : N+Y ≤ 1+shortWidth)
    (hl : 4*(shortWidth+l) < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (terminal : CenteredUnitBox N Y l mesh ε) : PairUnitBox N Y l mesh ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨dc,Sc,Cc,hCc,hcenter⟩ := terminal Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  let Ccenter := Cc*QuadraticInitialBound.diagonalControl radialMajorant
  have hCcenter : 0 ≤ Ccenter := mul_nonneg hCc.le
    (QuadraticInitialBound.diagonalControl_nonneg _)
  obtain ⟨d,S,C,hC,hroot⟩ := actual_uncentered_root Slot hβ rayM Hr hHr W hW.continuous hWs
    1 l ε bΦ Ccenter dc Sc (by norm_num) le_rfl hl hε hε1 hCcenter
    (by linarith) hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨d,S,C,hC,?_⟩
  filter_upwards [hroot,hcenter] with Z hr hc
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂
  have hx₁ := scale_le_of_length hr.1 hXN
  have hx₂ := scale_le_of_length hr.1 hXY
  have hXN' : X₁ ≤ Z^(1:ℝ) := hx₁.trans (Real.rpow_le_rpow_of_exponent_le hr.1.le hN)
  have hXY' : X₂ ≤ Z^(1:ℝ) := hx₂.trans (Real.rpow_le_rpow_of_exponent_le hr.1.le hY)
  have hprod : X₁*X₂ ≤ Z^(1+shortWidth) := by
    calc
      _ ≤ Z^N*Z^Y := mul_le_mul hx₁ hx₂ hX₂.le (Real.rpow_nonneg (zero_lt_one.trans hr.1).le _)
      _ = Z^(N+Y) := (Real.rpow_add (zero_lt_one.trans hr.1) _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hr.1.le hNY
  have hy' : ∀ u∈rows,rowNorm u ≤ Z^(1:ℝ) := by simpa only [Real.rpow_one] using hy
  have hb := hr.2 T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ (fun i _=>hσ₁lo i) (fun i _=>hσ₁hi i)
    (fun i _=>hσ₂lo i) (fun i _=>hσ₂hi i) hsum
    p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hXN' hXY' hprod rows mark hk₁ hk₂ hy' hm₁ hm₂ (by
      intro hlong₁ hlong₂
      convert hc T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
        hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂ hlong₁ hlong₂ using 1 <;>
        dsimp [Ccenter] <;> ring)
  have hn : 0 ≤ C*(p.control S)^2*(1+|t₁|+|t₂|+height)^d*Z^(1+ε) := by
    have hz : 0 ≤ Z^(1+ε) := Real.rpow_nonneg (zero_lt_one.trans hr.1).le _
    positivity
  have hd := mul_le_mul_of_nonneg_left radial_diagonal_ge_one hn
  exact hb.trans (by convert hd using 1 <;> ring)

#print axioms radial_diagonal_ge_one
#print axioms pair_unit_of_centered
end
end QRH.Cycle092.OrderedPairPhase
