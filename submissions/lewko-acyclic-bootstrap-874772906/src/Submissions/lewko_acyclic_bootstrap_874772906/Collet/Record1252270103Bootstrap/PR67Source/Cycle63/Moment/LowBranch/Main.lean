import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Gate
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Incumbent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.RestrictedLowMain
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine original incumbent moments plus the proved actual low slots.
All fixed constants precede the live state, selected slots and both heights.
The retained low predicate and the exhaustion alternative remain explicit. -/
theorem actual_low_main
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      ∀ hQM : Q ≤ M, internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh a : ℝ) (i : ℕ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀ j ∈ J, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, lo ≤ σ j) → (∀ j, σ j ≤ hi) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      let F := max (length Z X₁+length Z X₂+(6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J, w j)-s.width) 0
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        (C*Z^(2*ε*d))^J.card *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(s.width+εold+q/(6*Cycle63.Optimization.slotPrice)*F+q*mesh) := by
  obtain ⟨degree,S,hinc⟩ := original_incumbent (α := α) M H hH W A B ap bp bΦ Bmask L
    lo hi Mcap εold hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hold⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hslots⟩ := actual_low_slots M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η lo hi bΦ Mcap Bmask margin d hRw hdmax hτ hε he he' hκ hη
    hbudget hbΦ.le hmargin hd hdsupply hdm q hq₀ hq₁
  refine ⟨max 1 C,C₀,C₁,le_max_left _ _,hC₀,hC₁,?_⟩
  filter_upwards [hold,hslots η₀] with Z hZ hslot
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv
    ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  let hQM' : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
  let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
  let low := ActualLow M H hH s η₀ hQM' hQη a e (3*(i+1 : ℕ)*Z^τ)
  let pay : ℝ := max 1 C*Z^(2*ε*d)
  have hpay : 1 ≤ pay := by
    have hpow : 1 ≤ Z^(2*ε*d) := Real.one_le_rpow hZ.1.le (by positivity)
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow
  have hBpay : ∀ j ∈ J, 0 ≤ pay := fun _ _ => zero_le_one.trans hpay
  have hpayslot : ∀ z, s.radial.keep z → low z → ∀ j ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w j)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (v j) I) t (Z^(w j))‖^2 ≤
          pay*Z^(q*w j) := by
    intro z hz hl j hj
    have hf : |t+v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
      have hh := abs_add_le t (v j)
      linarith [hv j]
    exact (hslot.2 s hs hQM' hQη a i ha ha' (w j) (σ j) t (v j) (hw j)
      (hwr j hj) (hσlo j) (hσhi j) hf hhigh z hz hl (θ j)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 C)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
  obtain ⟨R,hR,hcap,hbound⟩ := restricted_low_main M H hH W B ap bp bΦ Bmask L
    (Cycle25.Energy.commonMesh Mcap Bmask L εold) lo hi Mcap εold Z mesh q hq₀ η₀ Q
    degree S C₀ C₁ hC₀.le hC₁.le hZ.2.1 hZ.2.2 J θ w σ v t height (fun _ => pay)
    hw hwL hmesh hwm hσlo hσhi hheight hv hBpay s hQ hs low p X₁ X₂
    hX₁ hX₂ hc₁ hc₂ hpayslot
  refine ⟨R,hR,hcap,hbound.trans ?_⟩
  have hprod : (∏ j ∈ R, pay) ≤ pay^J.card := by
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hpay (Finset.card_le_card hR)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hmoment : 0 ≤ (C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hmoment)
    (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
