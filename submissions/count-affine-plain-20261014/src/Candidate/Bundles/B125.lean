/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B084
import Candidate.Bundles.B095
import Candidate.Bundles.B108
import Candidate.Bundles.B117
import Candidate.Bundles.B124
import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.PaidMain; sha256 d7f35471bd351284b29c27d373c0f2a2455c6cb3099b64c59985778e2e38decb -/
section
                                       

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
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

/-- Algebraic payment of the actual greedy-deletion energy bound. The
constant uses the fixed ambient label count, before the live selected set. -/
theorem paid_energy_bound {E A C Z ε d b M nominal width δ total padding εold mesh : ℝ}
    {n N : ℕ} (hZ : 1 < Z) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hε : 0 < ε) (hd : 0 < d) (hn : n ≤ N)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-nominal ≤ M*Cycle61.Arithmetic.g b+6*(M*Cycle61.Arithmetic.amp b)+padding)
    (hE : E ≤ (C*Z^(2*ε*d))^n*A*
      Z^(width+εold+(2*Cycle61.Arithmetic.q0/9)*max (total-width) 0+
        Cycle61.Arithmetic.q0*mesh)) :
    E ≤ C^N*A*Z^(nominal+δ+M*Cycle61.Arithmetic.amp b-M*(1/3750000)+εold+
      2*ε*d*(N:ℝ)+(2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh) := by
  have hp := paid_low_exponent_shifted (buffer := 2*ε*d*(N:ℝ)) (εold := εold) (mesh := mesh) hb hM hwidth hδ hpad htotal
  have hn' : (n:ℝ) ≤ N := by exact_mod_cast hn
  have hbuf := mul_le_mul_of_nonneg_left hn' (show 0 ≤ 2*ε*d by positivity)
  have hexp : width+εold+(2*Cycle61.Arithmetic.q0/9)*max (total-width) 0+
      Cycle61.Arithmetic.q0*mesh+2*ε*d*(n:ℝ) ≤
    nominal+δ+M*Cycle61.Arithmetic.amp b-M*(1/3750000)+εold+
      2*ε*d*(N:ℝ)+(2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh := by
    linarith
  rw [buffer_power_identity C Z ε d n (zero_lt_one.trans hZ)] at hE
  have heq : C^n*Z^(2*ε*d*(n:ℝ))*A*
      Z^(width+εold+(2*Cycle61.Arithmetic.q0/9)*max (total-width) 0+Cycle61.Arithmetic.q0*mesh) =
    C^n*A*Z^(width+εold+(2*Cycle61.Arithmetic.q0/9)*max (total-width) 0+
      Cycle61.Arithmetic.q0*mesh+2*ε*d*(n:ℝ)) := by
    conv_rhs => rw [Real.rpow_add (zero_lt_one.trans hZ)]
    ring
  rw [heq] at hE
  exact hE.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hn) hA)
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity))

/-- Actual local low energy with the genuine incumbent and slot estimates,
paid at the second-transform nominal width. No low-slot moment premise. -/
theorem actual_paid_low_main
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
      51/100 ≤ a → a ≤ 167/200 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ (b Mrow nominal δ padding : ℝ),
      (3401/100000 ≤ b ∧ b ≤ 1/25) → 0 ≤ Mrow →
      s.width-nominal ≤ δ → 0 ≤ δ → 0 ≤ padding →
      length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J, w j)-nominal ≤
        Mrow*Cycle61.Arithmetic.g b+6*(Mrow*Cycle61.Arithmetic.amp b)+padding →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        C^(Fintype.card α) *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(nominal+δ+Mrow*Cycle61.Arithmetic.amp b-Mrow*(1/3750000)+εold+
            2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*padding+
            Cycle61.Arithmetic.q0*mesh) := by
  obtain ⟨degree,S,hmain⟩ := actual_low_main (α := α) M H hH W A B ap bp bΦ Bmask L
    lo hi Mcap εold hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin
    hd hdsupply hdm
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
  exact paid_energy_bound hZ.1 hC (by
    have hdiag := diagonalControl_nonneg s.radial.profile
    positivity) hε hd (by simpa using Finset.card_le_univ J)
    hb hMrow hwidth hδ hpad htotal henergy

#print axioms paid_energy_bound
#print axioms actual_paid_low_main
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.PaidMain -/

/- BEGIN ORIGINAL Cycle61.Physical.ChildMatches; sha256 d8c8018c9c4f5ea0455ab3f33cd175bcc98161964bad00c0c421de24d9f01756 -/
section
                                               
                                                                       

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61ChildMatches
noncomputable section
open scoped Classical
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Common allocation restricts the same relative slot dictionary. Changing
the row character or its height does not change any of these slot data. -/
theorem actual_child_matches
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ freq : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i => θ i.val) (fun i => w i.val) (fun i => σ i.val)
      (fun i => freq i.val) W bslot Z := by
  exact ⟨fun i I => hm.character i.val I, fun i y => hm.profile i.val y,
    fun i => hm.pool i.val, fun i => hm.scale i.val⟩

/-- Prime extraction preserves the dictionary through both actual allocations;
no claim that the extracted prime divides a final row is used. -/
theorem actual_twice_child_matches
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ freq : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i => θ i.val.val) (fun i => w i.val.val) (fun i => σ i.val.val)
      (fun i => freq i.val.val) W bslot Z := by
  exact actual_child_matches M H hH _ η₀ _ _ _ _ W bslot Z
    (actual_child_matches M H hH s η₀ θ w σ freq W bslot Z hm C R B τ t)
    (Q^k) (R*C) Bp υ v

end
end OAI.SevenEighths.Cycle61ChildMatches
#print axioms OAI.SevenEighths.Cycle61ChildMatches.actual_child_matches
#print axioms OAI.SevenEighths.Cycle61ChildMatches.actual_twice_child_matches

end
/- END ORIGINAL Cycle61.Physical.ChildMatches -/

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.SideGeometry; sha256 890f5f9824bb40e57f4951db33419fd5e1e489c2bbe6d316a03f637bc2a11c00 -/
section
                                               
                                          
                                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem source_plain_positive (s : Data α) (second : Bool) (j : Fin 2) :
    0 < Cycle61.Physical.sourcePlainScales s.toSource second j := by
  cases second <;> fin_cases j
  · exact s.X₁_pos
  · exact s.X₂_pos
  · exact s.Y₁_pos
  · exact s.Y₂_pos

/-- Selected-plain quotients are applied exactly once; clipping is the
positive part of their exact logarithmic reduction. -/
theorem final_plain_length (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (j : Fin 2) :
    length Z (finalPlain s second L a j) =
      max 0 (Real.logb Z (Cycle61.Physical.sourcePlainScales s.toSource second j)-
        Cycle61.Physical.actualPlainReduction Z L a j) := by
  have hn : (0:ℝ) < (Ideal.absNorm (selectedPlain L a j):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  have hx := source_plain_positive s second j
  change Real.logb Z (max 1 (max 1 (_/_))) = _
  rw [max_eq_right (le_max_left 1 (_/_))]
  change length Z (Cycle61.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain L a j):ℝ)) = _
  rw [length_eq_max_log Z _ hZ (div_pos hx hn),Real.logb_div hx.ne' hn.ne']
  rfl

/-- The genuine retained cutoff never enlarges a clamped plain length. -/
theorem final_plain_length_le (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (j : Fin 2) :
    length Z (finalPlain s second L a j) ≤
      length Z (Cycle61.Physical.sourcePlainScales s.toSource second j) := by
  have hn : (1:ℝ) ≤ (Ideal.absNorm (selectedPlain L a j):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  have hx := source_plain_positive s second j
  have hdiv : Cycle61.Physical.sourcePlainScales s.toSource second j/
      (Ideal.absNorm (selectedPlain L a j):ℝ) ≤
      Cycle61.Physical.sourcePlainScales s.toSource second j :=
    (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
      (le_mul_of_one_le_right hx.le hn)
  apply Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
  change max 1 (max 1 (_/_)) ≤ max 1 _
  rw [max_eq_right (le_max_left 1 (_/_))]
  exact max_le_max_left 1 hdiv

/-- The actual residual slot family loses widths only. -/
theorem final_total_le (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (w : α → ℝ) (hw : ∀ j, 0 ≤ w j) :
    length Z (finalPlain s second L a 0)+length Z (finalPlain s second L a 1)+
        (9/2)*(∑ j ∈ liveIndices L a, w j) ≤
      length Z (Cycle61.Physical.sourcePlainScales s.toSource second 0)+
        length Z (Cycle61.Physical.sourcePlainScales s.toSource second 1)+
        (9/2)*(∑ j, w j) := by
  have hsum : (∑ j ∈ liveIndices L a, w j) ≤ ∑ j, w j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hw j)
  linarith [final_plain_length_le s second L a Z hZ 0,
    final_plain_length_le s second L a Z hZ 1]

#print axioms final_plain_length
#print axioms final_plain_length_le
#print axioms final_total_le
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.SideGeometry -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalCapacity.Capacity; sha256 04d440cf8eee55dd8b11908bb5393e1c79ee0cb4a555cb926a77d25ba830729d -/
section
                                                
                                            
                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The old 9/2 capacity of an actual surviving residual row is paid by
 its genuine raw volume and the fixed plain-support clipping cost. -/
theorem supported_residual_capacity (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (hP : ∀i,1 ≤ s.P i) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=s.X₁*s.X₂) (z : O)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P L a
      s.W₁ s.W₂ X₁ X₂ ≠ 0) :
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z s.P ≤
      Real.logb Z (preVolume s)+(7/2)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s L a z X₁ X₂ hX₁ hX₂ hne
  have hc := (clipping_loss_bound Z _ _ s.b₁ s.b₂ hZ
    (rawScale_pos L a X₁ hX₁ 0) (rawScale_pos L a X₂ hX₂ 1) hs₁ hs₂).2
  have hl := remainingLogs_le L a Z hZ s.P hP
  have hr := Real.logb_nonneg hZ (formalReduction_ge_one L a s.P hP)
  have he := affine_exact L a Z X₁ X₂ (3/4) 0 hZ hX₁ hX₂ s.P s.P_pos
  rw [hprod] at he
  change _ = Real.logb Z (preVolume s)-_ - _ + _ + _ at he
  linarith

/-- Two actual common allocations retain the original slot budget; all
 deleted and residual slots are accounted for by their genuine reductions. -/
theorem two_stage_supported_capacity (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z) (hP : ∀i,1 ≤ s.P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₁*
      (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let first := child s C₁ R₁ B₁ χ t
    let final := commonData first C₂ R₂ B₂
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z final.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        Real.logb Z (rawReduction B₂.val first.P)+(7/2)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let final := commonData first C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hp₂ : ∀i,1 ≤ final.P i := fun i => hp₁ i.val
  have hb := supported_residual_capacity final L a Z hZ hp₂ X₁ X₂ hX₁ hX₂ hprod z hne
  have hv : Real.logb Z (preVolume final) = Real.logb Z (preVolume s.toData)-
      Real.logb Z (rawReduction B₁.val s.P)-Real.logb Z (rawReduction B₂.val first.P) := by
    rw [common_preVolume,Real.logb_div (preVolume_pos first.toData).ne'
      (rawReduction_pos B₂.val (alloc_ne first C₂ B₂) first.P first.P_pos).ne',
      first_child_prevolume,Real.logb_div (preVolume_pos s.toData).ne'
      (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos).ne']
  have hl₁ := common_slot_logs_le s C₁ B₁ Z hZ hP
  have hl₂ := common_slot_logs_le first C₂ B₂ Z hZ hp₁
  rw [hv] at hb
  change _ ≤ _ at hb ⊢
  change (∑i,Real.logb Z (final.P i)) ≤ ∑i,Real.logb Z (first.P i) at hl₂
  have hl : (∑i,Real.logb Z (final.P i)) ≤ ∑i,Real.logb Z (s.P i) := hl₂.trans hl₁
  change _ ≤ Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
    Real.logb Z (rawReduction B₂.val first.P)+(7/2)*(∑i,Real.logb Z (final.P i))+
      Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  linarith

#print axioms supported_residual_capacity
#print axioms two_stage_supported_capacity
end
end OAI.SevenEighths.Cycle61FinalCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalCapacity.Capacity -/
