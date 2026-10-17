import Candidate.Cycle63.Physical.ExtractedBranches.Paid
import Candidate.Cycle63.Physical.ExtractedBranches.Slots
import Candidate.Cycle63.Moment.LowBranch.Payment

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Physical.ExtractedBranches
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual original energy beyond the incumbent capacity, paid by globally
priced deletion. All analytic constants precede the live natural state,
ray labels, widths and independent heights. -/
theorem actual_global_main
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree degreeSlot : ℕ, ∃ S : Finset (ℕ × ℕ),
    ∀ η₀ : Character, ∀ Q : Ideal O, ∀ _hQM : Q ≤ M,
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh : ℝ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, lo ≤ σ j) → (∀ j, σ j ≤ hi) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      let F := max (length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J, w j)-s.width) 0
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        (C*(1+|t|+height)^degreeSlot*Z^loss)^J.card *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(s.width+εold+(1/6)*F+(3/4)*mesh) := by
  classical
  obtain ⟨degree,S,hinc⟩ := Cycle63Moment.LowBranch.original_incumbent (α := α)
    M H hH W A B ap bp bΦ Bmask L lo hi Mcap εold hA hWs hW hB hap hap' hbp
    hbΦ hBmask hMcap hεold hbeta
  obtain ⟨degreeSlot,C,hC,hslots⟩ := actual_global_slots M H hH W A B hA hWs hW
    bΦ Mcap Bmask (Cycle25.Energy.commonMesh Mcap Bmask L εold) margin loss lo hi
    hbΦ.le hMcap.le hBmask
    (Cycle25.Energy.commonMesh_pos Mcap Bmask L εold hMcap.le hBmask hεold).le
    hmargin hloss hbeta
  refine ⟨degree,degreeSlot,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hold⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  refine ⟨max 1 C,C₀,C₁,le_max_left _ _,hC₀,hC₁,?_⟩
  filter_upwards [hold,hslots η₀] with Z hZ hslot
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh hw hwL hmesh hwm hσlo hσhi hheight hv
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  let hQM' : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
  let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
  let supported : O → Prop := fun z => s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0
  let pay : ℝ := max 1 C*(1+|t|+height)^degreeSlot*Z^loss
  have hpay : 1 ≤ pay := by
    have hh : 1 ≤ (1+|t|+height)^degreeSlot := one_le_pow₀ (by linarith [abs_nonneg t])
    have hz : 1 ≤ Z^loss := Real.one_le_rpow hZ.1.le hloss.le
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hh) hz
  have hpayslot : ∀ z, s.radial.keep z → supported z → ∀ j ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w j)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (v j) I) t (Z^(w j))‖^2 ≤
          pay*Z^((3/4:ℝ)*w j) := by
    intro z hz hΦ j hj
    have hb := hslot.2 s hs hQM' hQη (w j) (σ j) t (v j) (hw j) (hwL j)
      (hσlo j) (hσhi j) z hz hΦ (θ j)
    apply hb.trans
    dsimp [pay]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
    exact mul_le_mul (le_max_right 1 C)
      (pow_le_pow_left₀ (by positivity) (by linarith [hv j]) degreeSlot)
      (by positivity) (by positivity)
  obtain ⟨R,hR,hcap,hbound⟩ := restricted_global_main M H hH W B ap bp bΦ Bmask L
    (Cycle25.Energy.commonMesh Mcap Bmask L εold) lo hi Mcap εold Z mesh η₀ Q
    degree S C₀ C₁ hC₀.le hC₁.le hZ.2.1 hZ.2.2 J θ w σ v t height (fun _ => pay)
    hw hwL hmesh hwm hσlo hσhi hheight hv (fun _ _ => zero_le_one.trans hpay)
    s hQ hs supported p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hpayslot
  have heq := Cycle63Moment.LowBranch.energy_support_restriction s.character s.mask 1 t
    (p.profile 0) (p.profile 1) (fun j : J => primePool M H B (Z^(w j)))
    (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (v j) I) (fun j : J => Z^(w j)) X₁ X₂
    s.radial.keep (fun _ => True) s.radial.profile s.radial.scale
  simp only [and_true] at heq
  rw [heq]
  refine ⟨R,hR,hcap,hbound.trans ?_⟩
  have hprod : (∏ j ∈ R, pay) ≤ pay^J.card := by
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hpay (Finset.card_le_card hR)
  have hd := diagonalControl_nonneg s.radial.profile
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (by positivity))
    (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)

#print axioms actual_global_main
end
end OAI.SevenEighths.Cycle63Physical.ExtractedBranches
