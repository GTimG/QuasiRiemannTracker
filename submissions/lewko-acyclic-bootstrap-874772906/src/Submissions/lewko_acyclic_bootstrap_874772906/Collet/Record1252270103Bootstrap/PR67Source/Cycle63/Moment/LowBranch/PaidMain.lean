import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Payment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Main
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

variable [Cycle63.AffineLedger] in
/-- Algebraic payment of the actual greedy-deletion energy bound. The
constant uses the fixed ambient label count, before the live selected set. -/
theorem paid_energy_bound [Cycle63.AffineLedger.DeletesIntoOldRegion] {E A C Z ε d b M nominal width δ total padding εold mesh : ℝ}
    {n N : ℕ} (hZ : 1 < Z) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hε : 0 < ε) (hd : 0 < d) (hn : n ≤ N)
    (hb : Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-nominal ≤ M*Cycle63.AffineLedger.g b+6*(M*Cycle63.AffineLedger.amp b)+padding)
    (hE : E ≤ (C*Z^(2*ε*d))^n*A*
      Z^(width+εold+Cycle63.AffineLedger.lowRate*max (total-width) 0+
        Cycle63.AffineLedger.q*mesh)) :
    E ≤ C^N*A*Z^(nominal+δ+M*Cycle63.AffineLedger.amp b-M*(Cycle63.AffineLedger.lowReserve)+εold+
      2*ε*d*(N:ℝ)+Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh) := by
  have hp := paid_low_exponent_shifted (buffer := 2*ε*d*(N:ℝ)) (εold := εold) (mesh := mesh) hb hM hwidth hδ hpad htotal
  have hn' : (n:ℝ) ≤ N := by exact_mod_cast hn
  have hbuf := mul_le_mul_of_nonneg_left hn' (show 0 ≤ 2*ε*d by positivity)
  have hexp : width+εold+Cycle63.AffineLedger.lowRate*max (total-width) 0+
      Cycle63.AffineLedger.q*mesh+2*ε*d*(n:ℝ) ≤
    nominal+δ+M*Cycle63.AffineLedger.amp b-M*(Cycle63.AffineLedger.lowReserve)+εold+
      2*ε*d*(N:ℝ)+Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh := by
    linarith
  rw [buffer_power_identity C Z ε d n (zero_lt_one.trans hZ)] at hE
  have heq : C^n*Z^(2*ε*d*(n:ℝ))*A*
      Z^(width+εold+Cycle63.AffineLedger.lowRate*max (total-width) 0+Cycle63.AffineLedger.q*mesh) =
    C^n*A*Z^(width+εold+Cycle63.AffineLedger.lowRate*max (total-width) 0+
      Cycle63.AffineLedger.q*mesh+2*ε*d*(n:ℝ)) := by
    conv_rhs => rw [Real.rpow_add (zero_lt_one.trans hZ)]
    ring
  rw [heq] at hE
  exact hE.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hn) hA)
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity))

variable [Cycle63.AffineLedger] in
/-- Actual local low energy with the genuine incumbent and slot estimates,
paid at the second-transform nominal width. No low-slot moment premise. -/
theorem actual_paid_low_main [Cycle63.AffineLedger.DeletesIntoOldRegion]
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
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
      51/100 ≤ a → a ≤ ((1+Cycle63.AffineLedger.q)/2) →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ (b Mrow nominal δ padding : ℝ),
      (Cycle63.AffineLedger.firstCellTop≤b ∧ b≤Cycle63.AffineLedger.slotTop) → 0 ≤ Mrow →
      s.width-nominal ≤ δ → 0 ≤ δ → 0 ≤ padding →
      length Z X₁+length Z X₂+(6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J, w j)-nominal ≤
        Mrow*Cycle63.AffineLedger.g b+6*(Mrow*Cycle63.AffineLedger.amp b)+padding →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        C^(Fintype.card α) *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(nominal+δ+Mrow*Cycle63.AffineLedger.amp b-Mrow*(Cycle63.AffineLedger.lowReserve)+εold+
            2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.lowRate*padding+
            Cycle63.AffineLedger.q*mesh) := by
  obtain ⟨degree,S,hmain⟩ := actual_low_main (α := α) M H hH W A B ap bp bΦ Bmask L
    lo hi Mcap εold hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin
    hd hdsupply hdm Cycle63.AffineLedger.q Cycle63.AffineLedger.q_pos.le
    Cycle63.AffineLedger.q_le_one
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,C₀,C₁,hC,hC₀,hC₁,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv
    ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ b Mrow nominal δ padding
    hb hMrow hwidth hδ hpad htotal
  dsimp only
  obtain ⟨R,hR,hcap,henergy⟩ := hZ.2 J θ w σ v t height mesh a i hw hwL hwr hmesh
    hwm hσlo hσhi hheight hv ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  refine ⟨R,hR,hcap,?_⟩
  rw [← Cycle63.AffineLedger.lowRate_eq] at henergy
  exact paid_energy_bound hZ.1 hC (by
    have hdiag := diagonalControl_nonneg s.radial.profile
    positivity) hε hd (by simpa using Finset.card_le_univ J)
    hb hMrow hwidth hδ hpad htotal henergy

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
