/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B079
import Submissions.gao_cycle61_plane_20261013.Bundles.B089
import Submissions.gao_cycle61_plane_20261013.Bundles.B091
import Submissions.gao_cycle61_plane_20261013.Bundles.B093
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

/- BEGIN ORIGINAL Cycle61.Moment.HighSlotProduct; sha256 d5b60e4da7a59b753a1b489fddd7732e072d5a68ef3b728e6970b63703c7be8f -/
section
                               

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The finite live slots all use the same buffered whole-family bin. The
buffer loss is proportional to the live slot count; the zero rate is charged
only to their total actual width. -/
theorem actual_high_slot_product
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
      ∀ {ι : Type*} [Fintype ι] (w σ v : ι → ℝ) (t : ℝ)
        (θ : ι → RayQuotient.Characters M H),
      (∀ k, 0 ≤ w k) → (∀ k, w k/d ≤ Rwidth) →
      (∀ k, σmin ≤ σ k) → (∀ k, σ k ≤ σmax) →
      (∀ k, |t+v k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*Z^τ) z →
      (∏ k, ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w k)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
          annularWeight W (Z^(w k)) (σ k) (v k) I) t (Z^(w k))‖^2) ≤
        C^(Fintype.card ι)*Z^((2*a-1)*(∑ k, w k)+2*ε*d*(Fintype.card ι)) := by
  obtain ⟨C,hC,hslots⟩ := actual_high_slots M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' ι _ w σ v t θ hw hwr hσ hσ' hfreq hheight z hz hbin
  calc
    _ ≤ ∏ k, (C*Z^(2*ε*d))*Z^((2*a-1)*w k) :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun k _ =>
        hZ.2 s hs hQM hQη a i ha ha' (w k) (σ k) t (v k)
          (hw k) (hwr k) (hσ k) (hσ' k) (hfreq k) hheight z hz hbin (θ k))
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,mul_pow,
        ←Real.rpow_sum_of_pos (zero_lt_one.trans hZ.1),←Finset.mul_sum,
        ←Real.rpow_mul_natCast (zero_lt_one.trans hZ.1).le,
        mul_assoc,←Real.rpow_add (zero_lt_one.trans hZ.1)]
      congr 2
      ring

#print axioms actual_high_slot_product
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.HighSlotProduct -/

/- BEGIN ORIGINAL Cycle61.Moment.HighRetainedRows; sha256 713285a07de3124c4969bd032051c93c9027fced26dc04384bc970f7a7cf3fad -/
section
                                     
                                          

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual retained row is estimated at one whole-family bin. Plain
coefficients are supplied by the natural row itself, including its puncture. -/
theorem actual_high_retained_row
    (Wslot : ℝ → ℂ) (A₀ B₀ : ℝ) (hA₀ : 0 < A₀)
    (hWs : Function.support Wslot ⊆ Icc A₀ B₀) (hW : ContDiff ℝ ∞ Wslot)
    (Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax
      bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hRp : 0 ≤ Rplain) (hdmax : 0 ≤ dmax)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hεp : 0 < εplain)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hvp : 0 ≤ vplain) (hvs : 0 ≤ vslot)
    (hslotBudget : 8*e*Rwidth+κ ≤ εslot)
    (hplainBudget : 12*e*(Rplain+2)+8*κ+2*vplain ≤ εplain)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hd : 0 < d)
    (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧
    ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : NaturalState Z Bmask bΦ), s.width ≤ Mcap →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
    ∀ z : O, ∀ hz : s.radial.keep z, ∀ F : NaturalRow s.character z,
    ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ) z →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (j : Dict),
    χ j = excluded F.character s.puncture →
    zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
    (χ j).modulus.absNorm ≤ Z^d →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (t : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k/d ≤ Rwidth) →
    (∀ k, σmin ≤ σ k) → (∀ k, σ k ≤ σmax) →
    (∀ k, |t+v k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
    (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^vslot →
    |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
    (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^vplain →
    ∀ (W : Fin 2 → ℝ → ℂ) (X r A B : Fin 2 → ℝ),
    (∀ k, 0 < X k) → (∀ k, clippedScale (X k) = (Z^d)^(r k)) →
    (∀ k, 0 < A k) →
    (∀ k, Function.support (dilated (W k) (clipDilation (X k))) ⊆ Icc (A k) (B k)) →
    (∀ k, ContDiff ℝ ∞ (dilated (W k) (clipDilation (X k)))) →
    (∀ k, 0 ≤ r k) → (∀ k, r k ≤ Rplain) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^2*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound 2) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^(n+2)*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound (n+2)) →
    ‖retainedPositiveRow s.character s.mask 1 z (W 0) (W 1)
      (fun k => primePool M H B₀ (Z^(w k)))
      (fun k I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
        annularWeight Wslot (Z^(w k)) (σ k) (v k) I)
      (fun k => Z^(w k)) t (X 0) (X 1)‖^2 ≤
      Cp^2*Cs^(Fintype.card ι)*
        Z^((2*a-1)*(d*(r 0+r 1)+(∑ k, w k))+
          2*εplain*d+2*εslot*d*(Fintype.card ι)) := by
  obtain ⟨n,Cp,hCp,hplain⟩ := actual_buffered_retained_plain_factors
    Rplain dmax τ εplain e κ vplain hRp hdmax hτ hεp he he' hκ hκ' hvp
    hplainBudget profileBound hprofile
  obtain ⟨Cs,hCs,hslots⟩ := actual_high_slot_product M H hH Wslot A₀ B₀ hA₀ hWs hW
    Rwidth dmax τ εslot e κ vslot σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hεs he he' hκ hvs hslotBudget hbΦ hmargin hd hdsupply hdm
  have hT : ∀ᶠ Z : ℝ in atTop, 2 < Z^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop _)
  refine ⟨n,Cp,Cs,hCp,hCs,?_⟩
  intro η₀
  filter_upwards [hslots η₀,hT] with Z hZ hZT
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' z hz F hbin Dict _ χ hχ j hj hzero hmod
    ι _ _ w σ v θ t hw hwr hσ hσ' hfreq hheight hfreqP hheightP W X r A B
    hX hscale hA hsupport hsmooth hr hrR hm₂ hmn
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hcoeff (I : Ideal O) :
      idealCoeff s.character I*CanonicalRowCompletion.idealRowHom (s.mask^6*(1*z)) I =
        if false then star (idealCoeff (χ j) I) else idealCoeff (χ j) I := by
    simp only [Bool.false_eq_true, ite_false, hj, one_mul]
    simpa only [NaturalState.mask] using (F.masked_ideal s.puncture s.puncture_ne_zero I).symm
  have hp := hplain Z d hZ.1.le hd.le hdm hZT χ hχ a i ha ha' hzero
    j s.character s.mask z false hcoeff
    (fun k => primePool M H B₀ (Z^(w k)))
    (fun k I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight Wslot (Z^(w k)) (σ k) (v k) I)
    (fun k => Z^(w k)) (fun _ => Real.rpow_pos_of_pos hZp _)
    W X r A B t hX hscale hA (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hsupport)
    (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hsmooth) hmod hr hrR hfreqP hheightP
    (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hm₂) (by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hmn)
  have hslt := hZ.2 s hs hQM hQη a i ha ha' w σ v t θ
    hw hwr hσ hσ' hfreq hheight z hz hbin
  apply hp.trans
  apply (mul_le_mul_of_nonneg_left hslt
    (mul_nonneg (sq_nonneg Cp) (Real.rpow_nonneg (Real.rpow_nonneg hZp.le _) _))).trans_eq
  rw [←Real.rpow_mul hZp.le]
  calc
    _ = Cp^2*Cs^(Fintype.card ι)*
        (Z^(d*((2*a-1)*(r 0+r 1)+2*εplain))*
         Z^((2*a-1)*(∑ k, w k)+2*εslot*d*(Fintype.card ι))) := by ring
    _ = _ := by
      rw [←Real.rpow_add hZp]
      congr 2
      ring

#print axioms actual_high_retained_row
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.HighRetainedRows -/

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.Main; sha256 f4e4b01b5a789a84cc164e929b92861b9fef474afb5388513c52840a58909d53 -/
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
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      let F := max (length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J, w j)-s.width) 0
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        (C*Z^(2*ε*d))^J.card *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(s.width+εold+(2*Cycle61.Arithmetic.q0/9)*F+Cycle61.Arithmetic.q0*mesh) := by
  obtain ⟨degree,S,hinc⟩ := original_incumbent (α := α) M H hH W A B ap bp bΦ Bmask L
    lo hi Mcap εold hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hold⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hslots⟩ := actual_low_slots M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η lo hi bΦ Mcap Bmask margin d hRw hdmax hτ hε he he' hκ hη
    hbudget hbΦ.le hmargin hd hdsupply hdm
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
          pay*Z^(Cycle61.Arithmetic.q0*w j) := by
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
    (Cycle25.Energy.commonMesh Mcap Bmask L εold) lo hi Mcap εold Z mesh η₀ Q
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

#print axioms actual_low_main
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.Main -/

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.DaughterState; sha256 4d453701cc5b6788ae7e0b911407d64e6ecf5fd4a53560ac525141ae69cd4105 -/
section
                                    
                                                                  

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open QuadraticInitialBound CenteredExceptionalProfile
open CenteredMomentAmplifiedRetainedRadius
local notation "O" => HeckeFamily.O

/-- The actual nonexceptional daughter mask. Fixed-inducing daughters remain
in the complementary branch; this definition does not declare them eligible. -/
def daughterKeep (χ : Character) (Q R : Ideal O) (z : O) : Prop :=
  z ≠ 0 ∧ ¬FixedInducingRow χ Q (fixedBadMask*idealGenerator R) 1 z

/-- Exact logarithmic widths of the retained radial cutoff and the actual
character conductor. The puncture is retained literally. -/
def daughterState (χ : Character) (Q R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (Z K Bmask bΦ : ℝ) (hZ : 1 < Z) (hK : 1 ≤ K) (hR : R ≠ 0)
    (hRcap : (R.absNorm : ℝ) ≤ Z^Bmask)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) : NaturalState Z Bmask bΦ where
  character := χ
  fixedModulus := Q
  puncture := R
  radial := {
    keep := daughterKeep χ Q R
    profile := Φ
    scale := K
    scale_pos := zero_lt_one.trans_le hK
    nonneg := fun _ => hp _ }
  rowWidth := Real.logb Z K
  characterWidth := Real.logb Z (χ.modulus.absNorm : ℝ)
  base_ge_one := hZ.le
  row_nonneg := Real.logb_nonneg hZ hK
  character_nonneg := Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
  scale_eq := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (zero_lt_one.trans_le hK)).symm
  modulus_bound := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))]
  puncture_ne_zero := hR
  puncture_bound := hRcap
  radial_support := hs
  row_ne_zero := fun _ h => h.1
  nonexceptional := fun _ h => h.2

theorem daughterState_width (χ : Character) (Q R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (Z K Bmask bΦ : ℝ) (hZ : 1 < Z) (hK : 1 ≤ K) (hR : R ≠ 0)
    (hRcap : (R.absNorm : ℝ) ≤ Z^Bmask)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) :
    (daughterState χ Q R Φ Z K Bmask bΦ hZ hK hR hRcap hs hp).width =
      Real.logb Z K + Real.logb Z (χ.modulus.absNorm : ℝ) := rfl

/-- The main retained radius gives the literal daughter width. The amplifier
is `sigma/3`, so its contribution here is six times that amplifier. -/
theorem daughter_main_width (χ : Character) (Z d K0 c sigma δ reserve : ℝ)
    (hZ : 1 < Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma δ reserve)+
      Real.logb Z (χ.modulus.absNorm : ℝ) =
    K0+max (d-c) 0+2*sigma+δ+reserve+
      Real.logb Z (χ.modulus.absNorm : ℝ) := by
  rw [mainCommonRadius, Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

#print axioms daughterState
#print axioms daughter_main_width
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.DaughterState -/
