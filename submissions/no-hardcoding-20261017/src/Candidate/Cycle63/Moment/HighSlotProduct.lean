import Candidate.Cycle63.Moment.HighSlots

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
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
end OAI.SevenEighths.Cycle63Moment
