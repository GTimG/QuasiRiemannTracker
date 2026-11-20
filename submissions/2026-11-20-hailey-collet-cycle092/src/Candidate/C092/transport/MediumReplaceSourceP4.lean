/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P4 for arbitrary source-side NaturalState data, without outer source records. -/
import Candidate.C092.transport.MediumReplaceSourceUpper

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckePrimeRay HeckeDetectorZeros
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeDyadic HeckeDetectorSupportedWitness
namespace QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_MediumReplaceSourceP4_4fabd5040819d427_001 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The SAME actual natural-source rows, same-zero witnesses, retained A_n,
whole Q and arbitrary nonnegative weights. The shorter upper is derived from
its union zero band and its own Mellin profile controls. At y=d*r the charge
is exactly nu*(y-d*m)+3*d*epsilon. d includes the actual conductor collar. -/
theorem regular_core_P4
    (bΦ Mcap Bmask margin R dmin dmax τ ε e κ heightCost : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k,0 ≤ profileBound k) :
    ∃ order : ℕ,∃ C : ℝ,0 < C ∧ ∀ (η₀ : Character) (I : ℕ),
      ∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
      ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus),
      ∀ rows : Finset O,∀ hkeep : ∀ z ∈ rows,s.radial.keep z,
        (∀ z ∈ rows,s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0) →
      let F := fun u : rows => naturalRow s.character u.val (s.row_ne_zero u.val (hkeep u.val u.property))
      ∀ (a cutoff r m : ℝ) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I → 0 ≤ r → r ≤ R →
      ∀ ws : ∀ u : rows,SupportedWitness (family M H hH s η₀ (F u)) (Z^d) a ε cutoff
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
        (∀ u : rows,(ws u).m=m) →
        (∀ u : rows,zeroMaximum (family M H hH s η₀ (F u))
          (family_nonprincipal M H hH s η₀ hQM hQη (hkeep u.val u.property) (F u))
          (3*(i+1 : ℕ)*Z^τ) < a+2*e) →
      ∀ (W : rows → ℝ → ℂ) (A B σ freq : rows → ℝ),
        (∀ u,0 < A u) → (∀ u,Function.support (W u) ⊆ Icc (A u) (B u)) →
        (∀ u,ContDiff ℝ ∞ (W u)) →
        (∀ u,|freq u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
        (∀ u,∀ x ∈ Icc (1-a-6*e-σ u) (2-σ u),∀ t : ℝ,
          (1+|t|)^2*‖mellin (W u) ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
        (∀ u,∀ x ∈ Icc (1-a-6*e-σ u) (2-σ u),∀ t : ℝ,
          (1+|t|)^(order+2)*‖mellin (W u) ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
      ∀ (A_n Q : rows → ℂ) (weight : rows → ℝ) (reverse : rows → Bool),(∀ u,0 ≤ weight u) →
        ∑ u : rows,weight u*‖A_n u*
          QRH.Cycle092.OrdinaryColumn.original s.character s.mask 1 u.val
            (HeckeInverseAmplification.twistProfile (W u) (σ u) (freq u)) 0 ((Z^d)^r)*Q u‖^2 ≤
          C*Z^((2*a-1)*(d*r-d*m)+3*d*ε)*
            ∑ u : rows,weight u*‖A_n u*QRH.Cycle092.SignedEnergy.oriented (reverse u)
              (QRH.Cycle092.SignedEnergy.actualPlain (ws u))*Q u‖^2 := by
  obtain ⟨order,C,hC,hupper⟩ := regular_core_short_upper M H hH bΦ Mcap Bmask margin R dmin dmax
    τ ε e κ heightCost hbΦ hmargin hR hdmin hdmax hτ hheight hε he he' hκ hκ' hcost hbudget profileBound hprofile
  refine ⟨order,C,hC,?_⟩
  intro η₀ I
  filter_upwards [hupper η₀ I] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd hd' hds s hs hQM hQη rows hkeep hΦ
  dsimp only
  intro a cutoff r m i ha ha' hi hr hr' ws hsame hnext W A B σ freq hA hW hsm hfreq hm₂ hmn A_n Q weight reverse hweight
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have hup := hZ.2 d hd hd' hds s hs hQM hQη u.val (hkeep u.val u.property) (hΦ u.val u.property)
    a i ha ha' hi (hnext u) (W u) (A u) (B u) r (σ u) (freq u) (hA u) (hW u) (hsm u)
    hr hr' (hfreq u) (hm₂ u) (hmn u)
  rw [natural_plain_eq_original s _ (W u) ((Z^d)^r) (σ u) (freq u)
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _)] at hup
  rw [show (Z^d)^((2*a-1)*r+ε) = Z^(d*((2*a-1)*r+ε)) from (Real.rpow_mul hZp.le _ _).symm] at hup
  have hex : d*((2*a-1)*r+ε)=(2*a-1)*(d*r)+d*ε := by ring
  rw [hex] at hup
  have hp := QRH.Cycle092.MediumReplace.supported_replace Z d a ε cutoff (Z^τ)
    ((Z^d)^(τ/(2*dmax))) C (d*r) (d*ε) (ws u)
    (QRH.Cycle092.OrdinaryColumn.original s.character s.mask 1 u.val
      (HeckeInverseAmplification.twistProfile (W u) (σ u) (freq u)) 0 ((Z^d)^r))
    (A_n u) (Q u) (reverse u) hZp hC.le hup
  rw [hsame u] at hp
  have hex' : (2*a-1)*(d*r-d*m)+d*ε+2*d*ε=(2*a-1)*(d*r-d*m)+3*d*ε := by ring
  rw [hex'] at hp
  exact (mul_le_mul_of_nonneg_left hp (hweight u)).trans_eq (by ring)

end QRH.Cycle092.MediumReplace.Source
#print axioms QRH.Cycle092.MediumReplace.Source.regular_core_P4
