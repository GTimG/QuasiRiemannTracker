import Cycle25.Energy.Physical.SourceState
import Cycle25.Energy.Endpoint
import ZetaZeroFree.Analytic.Moments.Unconditional

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace OAI.SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem weighted_terminal_positive_energy {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ)
    (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop, 1 < U ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (Cycle25.Energy.commonMesh 2 0 1 (D.t/4))
        (33/50) (33/50) 2 (D.t/4) κ U η₀ (weighted_sourceFixedIdeal F) degree control C := by
  have hsupport : Function.support (fun x=>conj (F.W x)) ⊆ Set.Icc (1:ℝ) 2 := by
    intro x hx
    exact F.complex_support (by simpa using hx)
  obtain ⟨degree,control,hbound⟩ := Cycle25.Energy.terminal_positive_at (α:=Fin D.N)
    F.modulus ⊤ le_top (fun x=>conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1
    (33/50) (33/50) 2 κ (D.t/4) (by norm_num) hsupport
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) hκlo hκhi
    (div_pos D.t_pos (by norm_num)) hbeta hκbeta
  refine ⟨degree,control,?_⟩
  intro η₀
  exact hbound η₀ (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2

theorem weighted_terminal_zero_energy {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    ∃degree:ℕ, ∃control:Finset (ℕ×ℕ), ∀η₀:Character,
      ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop, 1 < U ∧
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 2 2
        (D.t/4) U degree control C := by
  obtain ⟨degree,control,hbound⟩ := ZetaZeroFree.Analytic.Moments.Unconditional.nonfixed_zero_at
    F.modulus (1/4) (9/4) bΦ 0 2 2 (D.t/4) (by norm_num) (by norm_num)
    (by norm_num) hbΦ (by norm_num) (by norm_num) (div_pos D.t_pos (by norm_num))
  refine ⟨degree,control,?_⟩
  intro η₀
  exact hbound η₀ (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η₀).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η₀)
    (weighted_source_fixed_gates F η₀).2.2.2

end OAI.SevenEighths.Cycle25WeightedNumeratorPhysical

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The positive contour assumptions are explicit; the empty-slot endpoint is unconditional. -/
