import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighSlotProduct
import Submissions.hailey_collet_1252270103.Cycle61.Moment.BufferedRetainedRows

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
