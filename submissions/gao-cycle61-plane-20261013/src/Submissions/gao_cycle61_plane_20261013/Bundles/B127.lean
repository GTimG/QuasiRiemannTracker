/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B078
import Submissions.gao_cycle61_plane_20261013.Bundles.B079
import Submissions.gao_cycle61_plane_20261013.Bundles.B092
import Submissions.gao_cycle61_plane_20261013.Bundles.B093
import Submissions.gao_cycle61_plane_20261013.Bundles.B124

/- BEGIN ORIGINAL Cycle61.Physical.ExtractedBranches.Paid; sha256 a3c567b05197e14c6d4548df7307f9ac0940df72f6699c25eff8546d5bcd254b -/
section
                                      
                                    

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Physical.ExtractedBranches
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

/-- Global slot pricing is paid before invoking the original capacity. Exhaustion
uses `ZeroAt`, and no capacity premise is imposed on the undeleted slots. -/
theorem restricted_global_main
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
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ ((3/4 : ℝ) * w i)) :
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
          Z ^ (s.width + ε + (1/6 : ℝ)*F +
            (3/4 : ℝ)*mesh) := by
  dsimp only
  obtain ⟨R,hR,hcap,hpay⟩ := LocalMomentSourceAudit.greedy_low_selection J w
    (length Z X₁) (length Z X₂) s.width (3/4) (3/4 : ℝ) mesh
    (by norm_num) (by norm_num) hmesh (fun i _ => hw i) hwm
  norm_num only at hcap hpay
  refine ⟨R,hR,hcap,?_⟩
  have hbR : ∀ i ∈ R, 0 ≤ B i := fun i hi => hB i (hR hi)
  have hb := LocalMoment.restricted_paid_incumbent M H hH W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε (3/4) Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R hR θ w σ v t height (3/4 : ℝ) B hw hwL hσlo hσhi hheight hv hbR
    s hQ hs low p X₁ X₂ hX₁ hX₂ hc₁ hc₂ (by norm_num; exact hcap)
    (fun z hz hl i hi => hslot z hz hl i (hR hi))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
  exact mul_nonneg (Finset.prod_nonneg hbR)
    (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁)
      (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _))

#print axioms restricted_global_main
end
end OAI.SevenEighths.Cycle61Physical.ExtractedBranches

end
/- END ORIGINAL Cycle61.Physical.ExtractedBranches.Paid -/

/- BEGIN ORIGINAL Cycle61.Physical.ExtractedBranches.Slots; sha256 7c17798243be4d9ffeb89535126127cd34ac7a013f17b04b4bb71b163197534c -/
section
                                         
                                

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Physical.ExtractedBranches
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Global bootstrap pricing for the literal punctured natural relative slot,
including tiny scales and independent external and slot frequencies. -/
theorem actual_global_slots
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (bΦ Mcap Bmask Lslot margin loss lo hi : ℝ)
    (hbΦ : 0 ≤ bΦ) (hMcap : 0 ≤ Mcap) (hBmask : 0 ≤ Bmask)
    (hLslot : 0 ≤ Lslot) (hmargin : 0 < margin) (hloss : 0 < loss)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (_hQM : s.fixedModulus ≤ M) (_hQη : s.fixedModulus ≤ η₀.modulus),
      ∀ w σ t v : ℝ, 0 ≤ w → w ≤ Lslot → lo ≤ σ → σ ≤ hi →
      ∀ z : O, s.radial.keep z →
        s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ θ : RayQuotient.Characters M H,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^w))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
          annularWeight W (Z^w) σ v I) t (Z^w)‖^2 ≤
        C*(1+|t|+|v|)^degree*Z^loss*Z^((3/4:ℝ)*w) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩ := CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W A B hA hWs hW (Mcap+Bmask+margin) Lslot loss lo hi (3/4)
    (by positivity) hLslot hloss hbeta (by linarith [Cycle61.Assembly.baseline_beta])
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventual_relative_conductor M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin,
    eventually_ge_atTop Z₀] with Z hcond hZ₀'
  refine ⟨hcond.1,?_⟩
  intro s hs hQM hQη w σ t v hw hwL hσ hσ' z hz hΦ θ
  let F := naturalRow s.character z (s.row_ne_zero z hz)
  let χ := (excluded F.character s.puncture).product
    (relativeCharacter M H hH η₀ θ).inverse.inverse
  let : Finite (O ⧸ (twistedFamily M H hH χ 1).modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient (twistedFamily M H hH χ 1).modulus_ne_bot
  have hc : (χ.modulus.absNorm : ℝ) ≤ Z^(Mcap+Bmask+margin) := by
    have hn : χ.modulus.absNorm ≤ (twistedFamily M H hH χ 1).modulus.absNorm :=
      FiniteConductor.absNorm_le_of_le inf_le_left
    exact (show (χ.modulus.absNorm : ℝ) ≤ _ by exact_mod_cast hn).trans
      (hcond.2 s hs z F hΦ θ 1)
  have hnp := whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ θ).inverse
    hQM (relativeCharacter_fixedQ M H hH η₀ θ _ hQM hQη) z hz F
  have hZp : 0 < Z := zero_lt_one.trans hcond.1
  have hP : 1 ≤ Z^w := Real.one_le_rpow hcond.1.le hw
  have hb := hbound Z (Z^w) hZ₀' hP
    (Real.rpow_le_rpow_of_exponent_le hcond.1.le hwL) χ hc hnp σ (t+v) hσ hσ'
  have hcoeff (I : Ideal O) :
      idealCoeff (relativeCharacter M H hH η₀ θ).inverse.inverse I =
        idealCoeff (relativeCharacter M H hH η₀ θ) I := by
    simp only [idealCoeff_inverse_conj,starRingEnd_self_apply]
  have htransport := relative_normalizedSlot_eq_ray M H s.character
    (excluded F.character s.puncture)
    (relativeCharacter M H hH η₀ θ).inverse.inverse s.mask 1 z
    (by simpa only [one_mul,NaturalState.mask] using F.masked_element _ s.puncture_ne_zero)
    W B (Z^w) σ t v (zero_lt_one.trans_le hP)
  simp_rw [hcoeff] at htransport
  rw [htransport, norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power _ t (zero_lt_one.trans_le hP), one_mul]
  have hp : (Z^w)^(3/4:ℝ) = Z^((3/4:ℝ)*w) := by
    rw [← Real.rpow_mul hZp.le]
    congr 1
    ring
  rw [hp] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

#print axioms actual_global_slots
end
end OAI.SevenEighths.Cycle61Physical.ExtractedBranches

end
/- END ORIGINAL Cycle61.Physical.ExtractedBranches.Slots -/

/- BEGIN ORIGINAL Cycle61.Physical.ExtractedBranches.Main; sha256 72687bdb1a31af3ede9988d61e150575eb210e4e0adbac1e50aad5aaf8f2bdee -/
section
                                              
                                               
                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Physical.ExtractedBranches
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

/-- Actual original energy beyond the incumbent capacity, paid by globally
priced deletion. All analytic constants precede the live natural state,
ray labels, widths and independent heights. -/
theorem actual_global_main
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree degreeSlot : ℕ, ∃ S : Finset (ℕ × ℕ),
    ∀ η₀ : Character, ∀ Q : Ideal O, ∀ _hQM : Q ≤ M,
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
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
      let F := max (length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J, w j)-s.width) 0
      ∃ R : Finset α, R ⊆ J ∧
        (R = J ∨ length Z X₁+length Z X₂+(9/2)*(∑ j ∈ J \ R, w j) ≤ s.width) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        (C*(1+|t|+height)^degreeSlot*Z^loss)^J.card *
          ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree)*
          Z^(s.width+εold+(1/6)*F+(3/4)*mesh) := by
  classical
  obtain ⟨degree,S,hinc⟩ := Cycle61Moment.LowBranch.original_incumbent (α := α)
    M H hH W A B ap bp bΦ Bmask L lo hi Mcap εold hA hWs hW hB hap hap' hbp
    hbΦ hBmask hMcap hεold hbeta
  obtain ⟨degreeSlot,C,hC,hslots⟩ := actual_global_slots M H hH W A B hA hWs hW
    bΦ Mcap Bmask (Cycle25.Energy.commonMesh Mcap Bmask L εold) margin loss lo hi
    hbΦ.le hMcap.le hBmask
    (Cycle25.Energy.commonMesh_pos Mcap Bmask L εold hMcap.le hBmask hεold).le
    hmargin hloss hbeta
  refine ⟨degree,degreeSlot,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hold⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  refine ⟨max 1 C,C₀,C₁,le_max_left _ _,hC₀,hC₁,?_⟩
  filter_upwards [hold,hslots η₀] with Z hZ hslot
  refine ⟨hZ.1,?_⟩
  intro J θ w σ v t height mesh hw hwL hmesh hwm hσlo hσhi hheight hv
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  let hQM' : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
  let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
  let supported : O → Prop := fun z => s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0
  let pay : ℝ := max 1 C*(1+|t|+height)^degreeSlot*Z^loss
  have hpay : 1 ≤ pay := by
    have hh : 1 ≤ (1+|t|+height)^degreeSlot := one_le_pow₀ (by linarith [abs_nonneg t])
    have hz : 1 ≤ Z^loss := Real.one_le_rpow hZ.1.le hloss.le
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hh) hz
  have hpayslot : ∀ z, s.radial.keep z → supported z → ∀ j ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w j)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (v j) I) t (Z^(w j))‖^2 ≤
          pay*Z^((3/4:ℝ)*w j) := by
    intro z hz hΦ j hj
    have hb := hslot.2 s hs hQM' hQη (w j) (σ j) t (v j) (hw j) (hwL j)
      (hσlo j) (hσhi j) z hz hΦ (θ j)
    apply hb.trans
    dsimp [pay]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
    exact mul_le_mul (le_max_right 1 C)
      (pow_le_pow_left₀ (by positivity) (by linarith [hv j]) degreeSlot)
      (by positivity) (by positivity)
  obtain ⟨R,hR,hcap,hbound⟩ := restricted_global_main M H hH W B ap bp bΦ Bmask L
    (Cycle25.Energy.commonMesh Mcap Bmask L εold) lo hi Mcap εold Z mesh η₀ Q
    degree S C₀ C₁ hC₀.le hC₁.le hZ.2.1 hZ.2.2 J θ w σ v t height (fun _ => pay)
    hw hwL hmesh hwm hσlo hσhi hheight hv (fun _ _ => zero_le_one.trans hpay)
    s hQ hs supported p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hpayslot
  have heq := Cycle61Moment.LowBranch.energy_support_restriction s.character s.mask 1 t
    (p.profile 0) (p.profile 1) (fun j : J => primePool M H B (Z^(w j)))
    (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (v j) I) (fun j : J => Z^(w j)) X₁ X₂
    s.radial.keep (fun _ => True) s.radial.profile s.radial.scale
  simp only [and_true] at heq
  rw [heq]
  refine ⟨R,hR,hcap,hbound.trans ?_⟩
  have hprod : (∏ j ∈ R, pay) ≤ pay^J.card := by
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hpay (Finset.card_le_card hR)
  have hd := diagonalControl_nonneg s.radial.profile
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (by positivity))
    (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)

#print axioms actual_global_main
end
end OAI.SevenEighths.Cycle61Physical.ExtractedBranches

end
/- END ORIGINAL Cycle61.Physical.ExtractedBranches.Main -/

/- BEGIN ORIGINAL Cycle61.Physical.ExtractedBranches.Envelope; sha256 03a21d60cbafeaa2beb51536e0e915e4b8324eb66690a4b37b9e2d58a91d741b -/
section
                                              

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Physical.ExtractedBranches
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
  have hpaid := Cycle61.Physical.paid_deletion_bound
    (F := total-nominal) hwidth hallowance (show 0 ≤ (1/6:ℝ) ∧ (1/6:ℝ) ≤ 1 by norm_num)
  rw [show total-nominal-(width-nominal) = total-width by ring] at hpaid
  linarith

#print axioms payment_envelope
#print axioms actual_global_main_uniform
#print axioms paid_global_exponent
end
end OAI.SevenEighths.Cycle61Physical.ExtractedBranches

end
/- END ORIGINAL Cycle61.Physical.ExtractedBranches.Envelope -/
