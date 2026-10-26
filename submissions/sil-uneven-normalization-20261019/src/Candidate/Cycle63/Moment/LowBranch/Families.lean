import Candidate.LocalMoment.RestrictedIncumbent
import Candidate.LocalMoment.LowSourceAdapters
import Candidate.Cycle63.Arithmetic.Constants
import Candidate.LocalMoment.BufferedSlot

/- Original module: Candidate.Cycle63.Moment.RestrictedLowMain. -/
section

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap
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
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε Z mesh : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε (3/4) Z η₀ Q degree S C₁)
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
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (Cycle63.Arithmetic.q0 * w i)) :
    let F := max (length Z X₁ + length Z X₂ + (9/2)*(∑ i ∈ J, w i) - s.width) 0
    ∃ R : Finset α, R ⊆ J ∧
      (R = J ∨ length Z X₁ + length Z X₂ + (9/2)*(∑ i ∈ J \ R, w i) ≤ s.width) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z ^ (w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
        s.radial.profile s.radial.scale ≤
        (∏ i ∈ R, B i) * ((C₀ + C₁) * diagonalControl s.radial.profile *
          (p.control S)^2 * (1 + |t| + height)^degree) *
          Z ^ (s.width + ε + (2*Cycle63.Arithmetic.q0/9)*F +
            Cycle63.Arithmetic.q0*mesh) := by
  dsimp only
  obtain ⟨R,hR,hcap,hpay⟩ := LocalMomentSourceAudit.greedy_low_selection J w
    (length Z X₁) (length Z X₂) s.width (3/4) Cycle63.Arithmetic.q0 mesh
    (by norm_num) (by norm_num [Cycle63.Arithmetic.q0]) hmesh (fun i _ => hw i) hwm
  have hrate : Cycle63.Arithmetic.q0 / (9/2) = 2*Cycle63.Arithmetic.q0/9 := by ring
  norm_num only at hcap hpay
  rw [hrate] at hpay
  refine ⟨R,hR,hcap,?_⟩
  have hbR : ∀ i ∈ R, 0 ≤ B i := fun i hi => hB i (hR hi)
  have hb := LocalMoment.restricted_paid_incumbent M H hH W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε (3/4) Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R hR θ w σ v t height Cycle63.Arithmetic.q0 B hw hwL hσlo hσhi hheight hv hbR
    s hQ hs low p X₁ X₂ hX₁ hX₂ hc₁ hc₂ (by norm_num; exact hcap)
    (fun z hz hl i hi => hslot z hz hl i (hR hi))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
  exact mul_nonneg (Finset.prod_nonneg hbR)
    (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁)
      (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _))

#print axioms restricted_low_main
end
end OAI.SevenEighths.Cycle63Moment
end

/- Original module: Candidate.Cycle63.Moment.LowBranch.Families. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckePrimeRay HeckeDetectorZeros ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentFixedRayInducingTransport
open CenteredMomentRayNonprincipal
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- All ray twists of the actual punctured natural relative character remain
nonprincipal. The exclusion is the state's actual fixed ideal. -/
theorem whole_nonprincipal {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ)
    (ν : Character) (hQM : s.fixedModulus ≤ M) (hQν : s.fixedModulus ≤ ν.modulus)
    (z : O) (hz : s.radial.keep z) (F : NaturalRow s.character z) :
    ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ((excluded F.character s.puncture).product ν.inverse)
        θ).residue ≠ 1 := by
  have hmask : s.mask ≠ 0 := mul_ne_zero fixedBadMask_ne_zero
    (idealGenerator_ne_zero _ s.puncture_ne_zero)
  have hex := (not_fixedInducingRow_product_inverse_iff s.character ν s.fixedModulus
    s.mask 1 z hQν hmask one_ne_zero (s.row_ne_zero z hz)
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))).mpr (s.nonexceptional z hz)
  apply all_ray_twists_nonprincipal M H hH (s.character.product ν.inverse)
    ((excluded F.character s.puncture).product ν.inverse) s.fixedModulus s.mask 1 z
    _ hQM hex
  simpa only [one_mul] using product_row_presentation s.character
    (excluded F.character s.puncture) ν.inverse s.mask 1 z
    (by simpa only [one_mul, NaturalState.mask] using F.masked_element _ s.puncture_ne_zero)

/-- A subfamily maximum is bounded by the genuine finite whole-family maximum,
including the sentinel at 51/100. No selected-zero surrogate is used. -/
theorem zeroMaximum_subfamily {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (χ : ι → Character) (ψ : ρ → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ j, (ψ j).residue ≠ 1)
    (f : ι → ρ) (hf : ∀ i, χ i = ψ (f i)) (T : ℝ) :
    zeroMaximum χ hχ T ≤ zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with h | h
  · obtain ⟨i,z,hzero,hheight,he⟩ := maximum_attained χ hχ T h
    have hb := zero_re_le_maximum ψ hψ T (f i) (by rw [he]; exact h.le)
      hheight (by rwa [← hf])
    simpa only [he] using hb
  · exact h.trans (zeroMaximum_bounds ψ hψ T).1

/-- A literal buffered gate implies the low exponent; a bin below 21/25 has
`2*a-1 ≤ 17/25`. -/
theorem low_rate {a : ℝ} (ha : a ≤ 21/25) : 2*a-1 ≤ Cycle63.Arithmetic.q0 := by
  norm_num [Cycle63.Arithmetic.q0] at *
  linarith

#print axioms whole_nonprincipal
#print axioms zeroMaximum_subfamily
end
end OAI.SevenEighths.Cycle63Moment.LowBranch
end
