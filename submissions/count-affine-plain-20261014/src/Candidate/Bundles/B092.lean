/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B079
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeRay
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion

/- BEGIN ORIGINAL LocalMoment.LowSourceAdapters; sha256 fb32a39b12b378805effde9c72d3d9a4db84ded2c71259da8bf2cf99f0c6ee53 -/
section
                                                    
                                                                            
                                                       
                                                      
                                                            

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSourceAudit
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondNonexceptionalChosenBlock HeckePrimeRay HeckeDetectorZeros
open HeckeFiniteDeletion CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- The moving child character is τ.  The relative-slot base η₀ and the
fixed exclusion ideal internalQ Q η₀ remain independent of τ. -/
theorem canonical_all_twists
    (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (τ η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (n : Fin 4 → ℤ) (z : O)
    (hz : (canonicalRadial τ (internalQ Q η₀) n).keep z)
    (F : NaturalRow τ z) :
    ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue ≠ 1 := by
  exact natural_relative_twists M H hH F hz.1 η₀ Q hQM hz.2

/-- Removing Euler factors does not change any buffered maximum; this includes
height T and the sentinel 51/100, rather than only individual positive zeros. -/
theorem zeroMaximum_eq_of_mask {ι : Type*} [Fintype ι]
    (χ ψ : ι → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ i, (ψ i).residue ≠ 1)
    (hm : ∀ i I, idealCoeff (χ i) I =
      if IsCoprime I (χ i).modulus then idealCoeff (ψ i) I else 0)
    (T : ℝ) : zeroMaximum χ hχ T = zeroMaximum ψ hψ T := by
  have he (i : ι) (s : ℂ) (hs : (51/100 : ℝ) ≤ s.re) :
      LFunction (χ i) s = 0 ↔ LFunction (ψ i) s = 0 := by
    have hs0 : 0 < s.re := by linarith
    rw [LFunction_eq_of_mask_nonprincipal (χ i) (ψ i) (hm i) (hχ i) hs0,
      mul_eq_zero]
    exact or_iff_left (factors_ne_zero (χ i).modulus (ψ i) hs0)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with h | h
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T h
      have hr : (51/100 : ℝ) ≤ s.re := by rw [hs]; exact h.le
      have hh := zero_re_le_maximum ψ hψ T i hr ht ((he i s hr).mp hz)
      simpa only [hs] using hh
    · exact h.trans (zeroMaximum_bounds ψ hψ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with h | h
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T h
      have hr : (51/100 : ℝ) ≤ s.re := by rw [hs]; exact h.le
      have hh := zero_re_le_maximum χ hχ T i hr ht ((he i s hr).mpr hz)
      simpa only [hs] using hh
    · exact h.trans (zeroMaximum_bounds χ hχ T).1

/-- Greedy removal uses the incumbent capacity, while its payment uses the low
bin rate.  Exhaustion is a valid alternative and needs no extra residual cost. -/
theorem greedy_low_selection {α : Type*}
    (J : Finset α) (w : α → ℝ) (l₁ l₂ width κbase κlow mesh : ℝ)
    (hb : 0 < κbase) (hl : 0 ≤ κlow) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh) :
    let F := max (l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width) 0
    ∃ R : Finset α, R ⊆ J ∧
      (R = J ∨ l₁+l₂+6*κbase*(∑ i ∈ J \ R, w i) ≤ width) ∧
      κlow*(∑ i ∈ R, w i) ≤ κlow/(6*κbase)*F+κlow*mesh := by
  classical
  dsimp only
  let F := max (l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width) 0
  obtain ⟨R,hR,hbound,hpay,_⟩ := whole_removal J w F κbase mesh
    (le_max_right _ _) hb hm hw hwm
  refine ⟨R,hR,?_,?_⟩
  · rcases hpay with he | hp
    · exact Or.inl he
    · right
      have hsum := Finset.sum_sdiff hR (f := w)
      have hF : l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width ≤ F := le_max_left _ _
      nlinarith
  · have hp := mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hl
    convert hp using 1 <;> dsimp only [F] <;> ring

/-- Canonical children have an exact width, possibly smaller than the nominal
ledger width.  Pay width and defect together instead of dropping that deficit. -/
theorem width_plus_low_defect (d F pad rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (hpad : 0 ≤ pad) (hd : d ≤ pad) :
    d + rate*max (F-d) 0 ≤ pad + rate*max F 0 := by
  by_cases h : 0 ≤ F-d
  · rw [max_eq_left h]
    by_cases hf : 0 ≤ F
    · rw [max_eq_left hf]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hf)]
      nlinarith
  · rw [max_eq_right (le_of_not_ge h)]
    have hnn : 0 ≤ rate*max F 0 := mul_nonneg hrate0 (le_max_right _ _)
    linarith

#print axioms canonical_all_twists
#print axioms zeroMaximum_eq_of_mask
#print axioms greedy_low_selection
#print axioms width_plus_low_defect
end SevenEighths.LocalMomentSourceAudit
end
end OAI

end
/- END ORIGINAL LocalMoment.LowSourceAdapters -/

/- BEGIN ORIGINAL Cycle61.Moment.RestrictedLowMain; sha256 0050d68a02a2aa3c945dcb49a7bca44c50a8b40a8dad4c50805032289eb7d613 -/
section
                                      
                                    
                                   

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
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
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (Cycle61.Arithmetic.q0 * w i)) :
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
          Z ^ (s.width + ε + (2*Cycle61.Arithmetic.q0/9)*F +
            Cycle61.Arithmetic.q0*mesh) := by
  dsimp only
  obtain ⟨R,hR,hcap,hpay⟩ := LocalMomentSourceAudit.greedy_low_selection J w
    (length Z X₁) (length Z X₂) s.width (3/4) Cycle61.Arithmetic.q0 mesh
    (by norm_num) (by norm_num [Cycle61.Arithmetic.q0]) hmesh (fun i _ => hw i) hwm
  have hrate : Cycle61.Arithmetic.q0 / (9/2) = 2*Cycle61.Arithmetic.q0/9 := by ring
  norm_num only at hcap hpay
  rw [hrate] at hpay
  refine ⟨R,hR,hcap,?_⟩
  have hbR : ∀ i ∈ R, 0 ≤ B i := fun i hi => hB i (hR hi)
  have hb := LocalMoment.restricted_paid_incumbent M H hH W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε (3/4) Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R hR θ w σ v t height Cycle61.Arithmetic.q0 B hw hwL hσlo hσhi hheight hv hbR
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
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.RestrictedLowMain -/

/- BEGIN ORIGINAL LocalMoment.BufferedSlot; sha256 51b4542f41559a4b5c05dae3f5aa387cd42f8e2759545add636134e72a612ed0 -/
section
                                                 
                                                                     

/-! Buffered pointwise payment for the literal natural prime slots.  The
additional common puncture remains inside the actual row character. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The existing buffered prime estimate pays a genuine natural relative
slot at the local bin parameter `2*a-1`.  The original puncture, zero
extensions, real norm power, and the independent two frequency parameters
are retained exactly. -/
theorem natural_relative_slot_buffered_bound
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8 * e * Rwidth + κ ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax →
      2 ≤ Z ^ d → 2 < Z ^ τ →
      ∀ (ηrow : Character) (z : O) (F : NaturalRow ηrow z)
        (η₀ : Character) (puncture : Ideal O), puncture ≠ 0 →
      let χ := (excluded F.character puncture).product η₀.inverse
      ∀ (hχ : ∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).residue ≠ 1) (a : ℝ) (i : ℕ),
        51 / 100 ≤ a → a ≤ 1 →
        HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e →
      ∀ r σ t v : ℝ, 0 ≤ r → r ≤ Rwidth → σmin ≤ σ → σ ≤ σmax →
        2 * (|Real.log A| + |Real.log B|) + 1 ≤ Real.log ((Z ^ d) ^ r) →
        (∀ θ : RayQuotient.Characters M H,
          (twistedFamily M H hH χ θ).modulus.absNorm ≤ Z ^ d) →
        |t + v| + Z ^ τ / 2 ≤ (3 * i + 2 : ℕ) * Z ^ τ →
        (3 + (3 * i + 2 : ℕ) * Z ^ τ) ^ 2 ≤ (Z ^ d) ^ η →
        ‖normalizedSlot ηrow (fixedBadMask * idealGenerator puncture) 1 z
          (primePool M H B ((Z ^ d) ^ r))
          (fun I => idealCoeff η₀.inverse I *
            annularWeight W ((Z ^ d) ^ r) σ v I) t ((Z ^ d) ^ r)‖ ^ 2 ≤
          C ^ 2 * (Z ^ d) ^ ((2 * a - 1) * r + 2 * ε) := by
  obtain ⟨C, hC, hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax hRw hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C, hC, ?_⟩
  intro Z d hZ hd hd' hbase hT ηrow z F η₀ puncture hpuncture
    χ hχ a i ha ha' hmax r σ t v hr hr' hσ hσ' hlarge hmod hfreq hheight
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hbasep : 0 < Z ^ d := Real.rpow_pos_of_pos hZp d
  have hscale : 0 < (Z ^ d) ^ r := Real.rpow_pos_of_pos hbasep r
  have hb := hbound Z d hZ hd hd' hbase hT χ hχ a i ha ha' hmax
    r σ (t + v) hr hr' hσ hσ' hlarge hmod hfreq hheight
  rw [relative_normalizedSlot_eq_ray M H ηrow (excluded F.character puncture)
    η₀.inverse (fixedBadMask * idealGenerator puncture) 1 z
    (by simpa only [one_mul] using F.masked_element puncture hpuncture)
    W B ((Z ^ d) ^ r) σ t v hscale, norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power ((Z ^ d) ^ r) t hscale, one_mul]
  apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
  rw [mul_pow, pow_two ((Z ^ d) ^ ((a - 1 / 2) * r + ε)),
    ← Real.rpow_add hbasep]
  congr 2
  ring

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.BufferedSlot -/

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.Families; sha256 152819a487455a1555ba7596697508ec3139633650f15146ffb314534d90296e -/
section
                               
                                       

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
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
theorem low_rate {a : ℝ} (ha : a ≤ 167/200) : 2*a-1 ≤ Cycle61.Arithmetic.q0 := by
  norm_num [Cycle61.Arithmetic.q0] at *
  linarith

#print axioms whole_nonprincipal
#print axioms zeroMaximum_subfamily
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.Families -/
