import Candidate.LocalMoment.RestrictedIncumbent
import Candidate.LocalMoment.LowSourceAdapters
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false

namespace Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => HeckeFamily.O

variable {α : Type*}
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Apply the old capacity only after paying the actual low-bin slots. The
row predicate remains in the sum until removal; exhaustion uses `ZeroAt`. -/
theorem restricted_low_main
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε Z mesh q κ : ℝ)
    (hκ : 0 < κ) (hq : 0 ≤ q)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C₁)
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
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (q * w i)) :
    let F := max (length Z X₁ + length Z X₂ + (6*κ)*(∑ i ∈ J, w i) - s.width) 0
    ∃ R : Finset α, R ⊆ J ∧
      (R = J ∨ length Z X₁ + length Z X₂ + (6*κ)*(∑ i ∈ J \ R, w i) ≤ s.width) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z ^ (w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
        s.radial.profile s.radial.scale ≤
        (∏ i ∈ R, B i) * ((C₀ + C₁) * diagonalControl s.radial.profile *
          (p.control S)^2 * (1 + |t| + height)^degree) *
          Z ^ (s.width + ε + (q/(6*κ))*F +
            q*mesh) := by
  dsimp only
  obtain ⟨R,hR,hcap,hpay⟩ := LocalMomentSourceAudit.greedy_low_selection J w
    (length Z X₁) (length Z X₂) s.width κ q mesh
    hκ hq hmesh (fun i _ => hw i) hwm
  refine ⟨R,hR,hcap,?_⟩
  have hbR : ∀ i ∈ R, 0 ≤ B i := fun i hi => hB i (hR hi)
  have hb := LocalMoment.restricted_paid_incumbent M H hH W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R hR θ w σ v t height q B hw hwL hσlo hσhi hheight hv hbR
    s hQ hs low p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    (fun z hz hl i hi => hslot z hz hl i (hR hi))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
  exact mul_nonneg (Finset.prod_nonneg hbR)
    (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁)
      (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _))

#print axioms restricted_low_main
end
end Target874836.SourceProvider
