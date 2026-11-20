/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early mesh and finite metadata for actual independent-pair source calls. -/
import Candidate.C092.transport.StrongPairLowMetadata
import Candidate.C092.transport.LowActualBankUniform

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
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
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary QRH.Cycle092.LowActual
open CenteredMomentEnergyState CenteredMomentCoreFloor
local notation "O" => ActualEisensteinCubic.O

/-- The complete original unmarked pair, including unequal lengths and
independent profiles, at every 0<=V<=1. The fixed η modulus is absorbed
before the live radius; no padding by twice the ordinary length is needed. -/
theorem freely_small_unmarked_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ ε : ℝ) (hbΦ : 0 < bΦ) (hε : 0 < ε) (hε1 : ε ≤ 1) (η η₀ : Character) (Q : Ideal O)
    (hQray : Q ≤ rayM) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ hU : 1 ≤ U,
      ∀ V : ℝ, 0 ≤ V → V ≤ 1 → ∀ (Φ : 𝓢(ℝ,ℂ)),
        ∀ (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ) (hΦ : ∀ x, 0 ≤ (Φ x).re),
      ∀ (p : Profiles (1/4) (9/4)) (t height X₁ X₂ : ℝ),
        0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂
        { keep := initialKeep η (internalQ Q η₀), profile := Φ, scale := U^V,
          scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _, nonneg := fun _ => hΦ _ } ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V+ε) := by
  obtain ⟨degree,controls,C,hC,hsource⟩ := incumbent_zero_source hβ rayM Hr hHr bΦ (ε/2)
    hbΦ (by positivity) η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,?_⟩
  have hmod := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε/2)).eventually
    (eventually_ge_atTop (η.modulus.absNorm : ℝ))
  filter_upwards [hsource,hmod] with U hsource hη
  intro hU V hV0 hV1 Φ hΦs hΦ p t height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U
  let st := regularState η (internalQ Q η₀) Φ bΦ U V (ε/2) hU hV0
    (by positivity) hΦs hΦ hη
  have hw : st.width ≤ 2 := by change V+ε/2 ≤ 2; linarith only [hV1,hε1]
  have hf := hsource.2 st rfl hw p t X₁ X₂ hX₁ hX₂ (by simpa using hX₁U) (by simpa using hX₂U)
  rw [st.plainEnergy_eq_zero] at hf
  have hheight : (1+‖t‖)^degree ≤ (1+|t|+height)^degree := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hh]) _
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hp := p.control_nonneg controls
  have hf' : zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂ st.radial ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+‖t‖)^degree*U^(V+ε) := by
    simpa [st,regularState,NaturalState.width,NaturalState.mask,add_assoc,show ε/2+ε/2=ε by ring] using hf
  exact hf'.trans (by gcongr)

/-- An actual independent unmarked fourth at arbitrarily small positive
error, on exactly the selected finite original regular rows. -/
theorem freely_small_unmarked_fourth
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ ε : ℝ) (hbΦ : 0 < bΦ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hΦs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η η₀ : Character) (Q : Ideal O) (hQray : Q ≤ rayM)
    (hQ0 : internalQ Q η₀ ≠ 0) (hQtop : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ,∃ S : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ Z : ℝ in atTop,∀ hZ : 1 ≤ Z,
    ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (t height X : ℝ),
      0 ≤ height → 0 < X → X ≤ Z →
    ∀ s : Finset FreeRow,(∀ u∈s,initialKeep η (internalQ Q η₀) u.val) → (∀ u∈s,rowNorm u ≤ Z) →
      (∑ u∈s,‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(sourceControl S (p.profile j))^4*
          (1+|t|+height)^d*Z^(1+ε) := by
  obtain ⟨d,S,C,hC,hsource⟩ := freely_small_unmarked_source hβ rayM Hr hHr bΦ ε hbΦ hε hε1
    η η₀ Q hQray hQ0 hQtop hQ72
  refine ⟨d,S,C,hC,hsource.mono ?_⟩
  intro Z hsource hZ p j t height X hh hX hXZ s hk hy
  have hfinite := finite_original_fourth η (internalQ Q η₀) (p.profile j) t X (9/4) Z
    (fun _ hx=>(p.support j hx).2) hX (zero_lt_one.trans_le hZ) s hk hy
  have h := hsource hZ 1 (by norm_num) le_rfl radialMajorant hΦs radialMajorant_nonneg
    (repeatedProfile p j) t height X X hh hX hX hXZ hXZ
  rw [repeated_control,←pow_mul] at h
  apply hfinite.trans
  simpa only [Real.rpow_one,repeatedProfile,show (2:ℕ)*2=4 from rfl] using h

#print axioms freely_small_unmarked_source
#print axioms freely_small_unmarked_fourth
end
end QRH.Cycle092.StrongPair
