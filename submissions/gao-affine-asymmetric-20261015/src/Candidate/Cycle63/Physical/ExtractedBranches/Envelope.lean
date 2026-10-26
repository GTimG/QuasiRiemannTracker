import Candidate.Cycle63.Physical.ExtractedBranches.Main

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Physical.ExtractedBranches
noncomputable section

/-- The finite slot loss and height degree have fixed ambient bounds. -/
theorem payment_envelope (C Z height loss control exponent : ℝ)
    (degree degreeSlot n N : ℕ) (hC : 1 ≤ C) (hZ : 1 ≤ Z)
    (hheight : 1 ≤ height) (hloss : 0 ≤ loss) (hcontrol : 0 ≤ control) (hn : n ≤ N) :
    (C*height^degreeSlot*Z^loss)^n*(control*height^degree)*Z^exponent ≤
      (C^N*control)*height^(degree+degreeSlot*N)*Z^(exponent+loss*(N:ℝ)) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hpay : 1 ≤ C*height^degreeSlot*Z^loss :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hheight))
      (Real.one_le_rpow hZ hloss)
  calc
    _ ≤ (C*height^degreeSlot*Z^loss)^N*(control*height^degree)*Z^exponent :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hpay hn) (by positivity))
        (Real.rpow_nonneg hZp.le _)
    _ = _ := by
      rw [mul_pow,mul_pow,← Real.rpow_natCast (Z^loss) N,
        ← Real.rpow_mul hZp.le,Real.rpow_add hZp,pow_add,pow_mul]
      ring

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

/-- A fixed ambient height degree and loss bound for the same original energy. -/
theorem actual_global_main_uniform
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ),
    ∀ η₀ : Character, ∀ Q : Ideal O, ∀ _hQM : Q ≤ M,
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧
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
      let F := max (length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J, w j)-s.width) 0;
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree*
          Z^(s.width+εold+loss*(Fintype.card α:ℝ)+(1/6)*F+(3/4)*mesh) := by
  classical
  obtain ⟨degree,degreeSlot,S,hmain⟩ := actual_global_main (α := α) M H hH W A B ap bp
    bΦ Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp hbΦ hBmask
    hMcap hεold hloss hmargin hbeta
  refine ⟨degree+degreeSlot*Fintype.card α,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C^(Fintype.card α)*(C₀+C₁),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh hw hwL hmesh hwm hσlo hσhi hheight hv
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  obtain ⟨R,hR,hcap,he⟩ := hZ.2 J θ w σ v t height mesh hw hwL hmesh hwm hσlo hσhi
    hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hd := diagonalControl_nonneg s.radial.profile
  have hp := payment_envelope C Z (1+|t|+height) loss
    ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2)
    (s.width+εold+(1/6)*max (length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J, w j)-s.width) 0+
      (3/4)*mesh) degree degreeSlot J.card (Fintype.card α) hC hZ.1.le
    (by linarith [abs_nonneg t]) hloss.le (by positivity) (Finset.card_le_univ J)
  apply he.trans (hp.trans_eq ?_)
  rw [show s.width+εold+1/6*max (length Z X₁+length Z X₂+9/2*(∑ j ∈ J, w j)-s.width) 0+
      3/4*mesh+loss*(Fintype.card α:ℝ) =
      s.width+εold+loss*(Fintype.card α:ℝ)+1/6*max
        (length Z X₁+length Z X₂+9/2*(∑ j ∈ J, w j)-s.width) 0+3/4*mesh by ring]
  ring

/-- Joint payment of the actual width deficit and global greedy deletion. -/
theorem paid_global_exponent {width nominal allowance total oldLoss slotLoss mesh : ℝ}
    (hwidth : width-nominal ≤ allowance) (hallowance : 0 ≤ allowance) :
    width+oldLoss+slotLoss+(1/6)*max (total-width) 0+(3/4)*mesh ≤
      nominal+allowance+oldLoss+slotLoss+(1/6)*max (total-nominal) 0+(3/4)*mesh := by
  have hpaid := Cycle63.Physical.paid_deletion_bound
    (F := total-nominal) hwidth hallowance (show 0 ≤ (1/6:ℝ) ∧ (1/6:ℝ) ≤ 1 by norm_num)
  rw [show total-nominal-(width-nominal) = total-width by ring] at hpaid
  linarith

#print axioms payment_envelope
#print axioms actual_global_main_uniform
#print axioms paid_global_exponent
end
end OAI.SevenEighths.Cycle63Physical.ExtractedBranches
