import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.RestrictedIncumbent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.LowSourceAdapters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.SlotPrice
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Physical.ExtractedBranches
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

variable {α : Type*}
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Global slot pricing is paid before invoking the original capacity. Exhaustion
uses `ZeroAt`, and no capacity premise is imposed on the undeleted slots. -/
theorem restricted_global_main
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε Z mesh : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε Cycle63.Optimization.slotPrice Z η₀ Q degree S C₁)
    (J : Finset α) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (t height : ℝ) (B : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ Lslot)
    (hmesh : 0 ≤ mesh) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (hσlo : ∀ i, lo ≤ σ i) (hσhi : ∀ i, σ i ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀ i, |v i| ≤ height) (hB : ∀ i ∈ J, 0 ≤ B i)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = internalQ Q η₀)
    (hs : s.width ≤ Mcap) (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ (w i)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (Cycle63.Optimization.slotPrice * w i)) :
    let F := max (length Z X₁ + length Z X₂ + (6*Cycle63.Optimization.slotPrice)*(∑ i ∈ J, w i) - s.width) 0
    ∃ R : Finset α, R ⊆ J ∧
      (R = J ∨ length Z X₁ + length Z X₂ + (6*Cycle63.Optimization.slotPrice)*(∑ i ∈ J \ R, w i) ≤ s.width) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z ^ (w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
        s.radial.profile s.radial.scale ≤
        (∏ i ∈ R, B i) * ((C₀ + C₁) * diagonalControl s.radial.profile *
          (p.control S)^2 * (1 + |t| + height)^degree) *
          Z ^ (s.width + ε + (1/6 : ℝ)*F +
            Cycle63.Optimization.slotPrice*mesh) := by
  dsimp only
  obtain ⟨R,hR,hcap,hpay⟩ := LocalMomentSourceAudit.greedy_low_selection J w
    (length Z X₁) (length Z X₂) s.width Cycle63.Optimization.slotPrice Cycle63.Optimization.slotPrice mesh
    Cycle63.Optimization.slotPrice_pos Cycle63.Optimization.slotPrice_pos.le hmesh (fun i _ => hw i) hwm
  have hsixth : Cycle63.Optimization.slotPrice/(6*Cycle63.Optimization.slotPrice) = 1/6 := by
    have hk := Cycle63.Optimization.slotPrice_pos.ne'
    field_simp
  rw [hsixth] at hpay
  refine ⟨R,hR,hcap,?_⟩
  have hbR : ∀ i ∈ R, 0 ≤ B i := fun i hi => hB i (hR hi)
  have hb := LocalMoment.restricted_paid_incumbent M H hH W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε Cycle63.Optimization.slotPrice Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R hR θ w σ v t height Cycle63.Optimization.slotPrice B hw hwL hσlo hσhi hheight hv hbR
    s hQ hs low p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    (fun z hz hl i hi => hslot z hz hl i (hR hi))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
  exact mul_nonneg (Finset.prod_nonneg hbR)
    (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁)
      (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _))

end
end OAI.SevenEighths.Cycle63Physical.ExtractedBranches

end Record1252270103Bootstrap.PR67
