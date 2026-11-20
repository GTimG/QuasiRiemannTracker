/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Independent ordinary characters and heights on actual regular core subrows.
The fourth suppliers are the original zero-slot source at the same U^V. -/
import Candidate.C092.transport.CofactorCleanEnergy
import Candidate.C092.transport.TinyCoreUnmarked
import Candidate.C092.transport.TinyCoreBridgeData

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore
local notation "O" => ActualEisensteinCubic.O

/-- A fourth moment of the literal original ordinary polynomial, on any
finite sixth-free regular subrow in the actual radial ball. -/
theorem finite_original_fourth
    (η : Character) (Q : Ideal O) (W : ℝ → ℂ) (t X b Y : ℝ)
    (hs : Function.support W ⊆ Set.Iic b) (hX : 0 < X) (hY : 0 < Y)
    (s : Finset FreeRow) (hk : ∀ u ∈ s, initialKeep η Q u.val)
    (hy : ∀ u ∈ s, rowNorm u ≤ Y) :
    (∑ u ∈ s, ‖original η (fixedBadMask*idealGenerator 1) 1 u.val W t X‖^4) ≤
      zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t W W X X
        { keep := initialKeep η Q, profile := radialMajorant, scale := Y,
          scale_pos := hY, nonneg := fun _ => radialMajorant_nonneg _ } := by
  rw [zero_energy_eq]
  have h := finite_clean_energy (ι := Fin 0) η (fixedBadMask*idealGenerator 1) 1 W W
    (fun _ => ∅) (fun _ => 0) (fun _ => 1) t X X b b Y hs hs hX hX
    (fun _ => zero_lt_one) hY s (initialKeep η Q) hk hy
  simp only [Fin.prod_univ_zero, one_mul, norm_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- Incumbent analytic fourth bounds, uniformly in all positive lengths up
to U, independent of the actual selected finite regular subrow. -/
theorem independent_fourth_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ : ℝ) (hbΦ : 0 < bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (η η₀ : Character) (Q : Ideal O)
    (hQray : Q ≤ rayM) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ hU : 1 ≤ U,
      ∀ V : ℝ, 0 ≤ V → V ≤ 1 →
      ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (t height X : ℝ),
        0 ≤ height → 0 < X → X ≤ U →
      ∀ (s : Finset FreeRow),
        (∀ u ∈ s, initialKeep η (internalQ Q η₀) u.val) →
        (∀ u ∈ s, rowNorm u ≤ U^V) →
      (∑ u ∈ s, ‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl controls (p.profile j))^4*
          (1+|t|+height)^degree*U^(V+1/10000) := by
  obtain ⟨degree,controls,C,hC,hsource⟩ := original_unmarked_source hβ rayM Hr hHr
    bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,hsource.mono ?_⟩
  intro U hsource hU V hV0 hV1 p j t height X hh hX hXU s hk hy
  have hfinite := finite_original_fourth η (internalQ Q η₀) (p.profile j) t X (9/4) (U^V)
    (fun _ hx => (p.support j hx).2) hX (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) s hk hy
  have hsource' := hsource hU V hV0 hV1 radialMajorant hsΦ radialMajorant_nonneg
    (repeatedProfile p j) t height X X hh hX hX hXU hXU
  apply hfinite.trans
  rw [repeated_control] at hsource'
  simpa only [repeatedProfile,← pow_mul] using hsource'

#print axioms finite_original_fourth
#print axioms independent_fourth_source
end
end QRH.Cycle092.CofactorOrdinary
