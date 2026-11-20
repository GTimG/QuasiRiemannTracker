/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Cap monotonicity, exact original common specialization and the correct
ordered invariant. The genuine native base is StrongPairSource.native_pair_box. -/
import Candidate.C092.transport.StrongPairPhysical

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

/-- Componentwise shorter labelled caps and any smaller positive width use
exactly the same source, control set, degree and constant. -/
theorem pair_caps_mono {N Y l N' Y' l' mesh ε : ℝ}
    (hN : N' ≤ N) (hY : Y' ≤ Y) (hl : l' ≤ l)
    (hsrc : PairUnitBox N Y l mesh ε) : PairUnitBox N' Y' l' mesh ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d,S,C,hC,h⟩ := hsrc Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨d,S,C,hC,h.mono ?_⟩
  intro Z hZ T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY
  exact hZ T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ (hsum.trans hl) p X₁ X₂ hX₁ hX₂ (hXN.trans hN) (hXY.trans hY)

theorem pair_uniform_mono {N Y l N' Y' l' : ℝ}
    (hN : N' ≤ N) (hY : Y' ≤ Y) (hl : l' ≤ l)
    (hsrc : PairUniformBox N Y l) : PairUniformBox N' Y' l' := by
  intro ε hε
  obtain ⟨mesh,hm,h⟩ := hsrc ε hε
  exact ⟨mesh,hm,pair_caps_mono hN hY hl h⟩

/-- Literal common-character source specialization on the original finite
rows; the ordinary and all prime kernels are the existing native objects. -/
theorem finiteEnergy_common {Slot : Type} [Fintype Slot]
    (s : Finset FreeRow) (η : Character) (W₁ W₂ : ℝ→ℂ) (t X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) :
    finiteEnergy s η η W₁ W₂ t t X₁ X₂ mark =
    ∑ u∈s,‖original η (fixedBadMask*idealGenerator 1) 1 u.val W₁ t X₁*
      original η (fixedBadMask*idealGenerator 1) 1 u.val W₂ t X₂‖^2*
      ∏ i,‖mark i u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [norm_mul,mul_pow]

/-- The polynomial degree is fixed BEFORE the freely chosen small τ. This
bound pays both independent ordinary heights and the live prime frequency. -/
theorem bounded_height_payment {Z τ ε t₁ t₂ height : ℝ} (d : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (ht₁ : |t₁| ≤ Z^τ) (ht₂ : |t₂| ≤ Z^τ)
    (hh0 : 0 ≤ height) (hh : height ≤ Z^τ) :
    (1+|t₁|+|t₂|+height)^d*Z^(1+ε) ≤ (4:ℝ)^d*Z^(1+ε+τ*(d:ℝ)) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hpow : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ
  have hb : 1+|t₁|+|t₂|+height ≤ 4*Z^τ := by linarith
  have hn : 0 ≤ 1+|t₁|+|t₂|+height := by positivity
  have he : (Z^τ)^d = Z^(τ*(d:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le]
  calc
    _ ≤ (4*Z^τ)^d*Z^(1+ε) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hn hb _) (Real.rpow_nonneg hZp.le _)
    _ = _ := by rw [mul_pow,he,mul_assoc,←Real.rpow_add hZp]; congr 1 <;> ring

/-- The ordered descent now ranges over the genuinely two-anchor source.
Its native input is proved above; the still-needed analytic increment must
supply this strengthened invariant on both strictly earlier cap calls. -/
theorem all_pair_strips_of_increment (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (increment : ∀ n y,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      PairOpenWidth (n/(H:ℝ)) (y/(H:ℝ)) →
      (∀ m,y/(H:ℝ) ≤ m → m ≤ sourceY →
        PairOpenWidth (max (n/(H:ℝ)) m) (min (n/(H:ℝ)) m)) → PairOpenWidth n y) :
    ∀ n y,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → PairOpenWidth n y :=
  QRH.Cycle092Continuation.ordered_source_induction PairOpenWidth
    (fun _ _ hy hy' hn hr l hl0 hl=>native_pair_box hβ hy hy' hn hr hl0 hl) increment

#print axioms pair_caps_mono
#print axioms finiteEnergy_common
#print axioms all_pair_strips_of_increment
end
end QRH.Cycle092.StrongPair
