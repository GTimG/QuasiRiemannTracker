/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B091
import Submissions.gao_cycle61_plane_20261013.Bundles.B105
import Submissions.gao_cycle61_plane_20261013.Bundles.B106
import Submissions.gao_cycle61_plane_20261013.Bundles.B107
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport

/- BEGIN ORIGINAL Cycle61.Moment.ActualRetainedMask; sha256 0cf95a836073c821f4e9db9e12d5effb6e22b95b1cf520d210a55458aaf9a1d4 -/
section
                                       
                                       
                                                                  
                                                                

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows IdealMobiusDivisorSum
open CenteredMomentHeckeColumnWindow CenteredMomentSecondChildProfile
local notation "O" => HeckeFamily.O

theorem actual_reduced_family_supported_ideal (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (χ : RayCharacter) (I : Ideal O) (hI : Supported I) :
    idealCoeff (τ χ) I = idealCoeff (childCharacter η χ) I *
      idealRowHom (reducedNumerator C D U) I := by
  have h := CenteredMomentSecondFamilyTransport.row_presentation_height
    η (τ χ) χ (reducedNumerator C D U) (hf.element_eq χ) I hI 0
  simp only [heightCoeff, Complex.ofReal_zero, mul_zero, Complex.cpow_zero,
    mul_one] at h
  rw [child_ideal_primary η χ I hI, h]
  ring

/-- The physical puncture restores the sixth factors cancelled in the second
character presentation; no conductor comparison for that presentation is used. -/
theorem actual_retained_reduced_mask (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (χ : RayCharacter) (z : O) (F : NaturalRow (τ χ) z)
    (G : NaturalRow (childCharacter η χ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded G.character P) I := by
  rw [excluded_ideal _ _ hP, excluded_ideal _ _ hP]
  by_cases hc : IsCoprime I P
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hs : Supported I
    · rw [natural_row_supported_ideal _ _ F I hs,
        natural_row_supported_ideal _ _ G I hs,
        actual_reduced_family_supported_ideal η C D hC hD U τ hf χ I hs,
        idealRowHom_argument_mul,
        residual_sixth_coefficient C D hC hCD U I hs
          (hc.of_isCoprime_of_dvd_right hCP).symm]
      ring
    · rw [natural_row_ideal_zero_of_not_supported _ _ F I hs,
        natural_row_ideal_zero_of_not_supported _ _ G I hs]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem actual_retained_fixed_dictionary_mask (η χ₁ : Character) (w : O)
    (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (z : O) (F : NaturalRow (τ ξ) z)
    (second : NaturalRow (childCharacter χ₁ ξ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (fixed : NaturalRow (childCharacter η ξ)
      (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded fixed.character (χ₁.modulus * P)) I := by
  rw [actual_retained_reduced_mask χ₁ C D hC hD hCD U τ hf ξ z F second P hP hCP I]
  exact actual_second_punctured_natural_mask η χ₁ w _ first hfirst ξ second fixed P hP I

#print axioms actual_reduced_family_supported_ideal
#print axioms actual_retained_reduced_mask
#print axioms actual_retained_fixed_dictionary_mask

section WholeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_retained_whole_dictionary_mask (η₀ η χ₁ : Character) (w : O)
    (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (z : O) (F : NaturalRow (τ ξ) z)
    (second : NaturalRow (childCharacter χ₁ ξ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (fixed : NaturalRow (childCharacter η ξ)
      (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P)
    (hw : w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z) ≠ 0)
    (G : ∀ j : WholeSourceIndex M H,
      NaturalRow (wholeSourceBase M H hH η₀ (childCharacter η ξ) j)
        (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ (excluded F.character P) j) I =
      idealCoeff (excluded (G j).character (χ₁.modulus * P)) I := by
  exact whole_source_family_mask M H hH η₀ (childCharacter η ξ)
    (excluded F.character P) _ hw fixed _ (mul_ne_zero χ₁.modulus_ne_bot hP)
    (actual_retained_fixed_dictionary_mask η χ₁ w first hfirst
      C D hC hD hCD U τ hf ξ z F second fixed P hP hCP) G j I

#print axioms actual_retained_whole_dictionary_mask
end WholeFamily
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.ActualRetainedMask -/

/- BEGIN ORIGINAL Cycle61.Moment.ActualJointDictionary; sha256 884aee9a6b32d8759420f0de5b00d598d4c64e81fb4d3bf4e8f19fa06b2451c9 -/
section
                                        

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentNaturalRowSource
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open RayFourExpansion IdealMobiusDivisorSum
open ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def jointFirstFrequency (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (l : JointSourceLabel) : O :=
  (u₀ * unit l.1) *
    primeSubsetGenerator (fun P : CommonIndex l.1.1.1 l.1.1.2 => P.val) l.1.2.val *
    firstSourceNumerator left l.1

theorem joint_source_row_factorization (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (l : JointSourceLabel) :
    jointSourceRow left u₀ unit l = jointFirstFrequency left u₀ unit l *
      ((commonFrequencyGenerator l.2.1.1 l.2.1.2 *
        nonunitFrequencyGenerator l.2.1.1 l.2.1.2 l.2.2.val.1) * l.2.2.val.2) := by
  unfold jointSourceRow jointFirstFrequency effectiveRow
  ring

/-- The exact retained physical character is a moving Euler mask of the
fixed natural character at the literal row used in the joint fiber count. -/
theorem actual_joint_retained_dictionary_mask (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (l : NonzeroJointSourceLabel left u₀ unit)
    (η χ₁ : Character) (first : NaturalRow η (jointFirstFrequency left u₀ unit l.val))
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (hC : Supported l.val.2.1.1) (hD : Supported l.val.2.1.2)
    (hCD : primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2)
    (τ : RayCharacter → Character)
    (hf : Family χ₁ l.val.2.1.1 l.val.2.1.2 hC hD l.val.2.2.val.1 τ)
    (ξ : RayCharacter) (F : NaturalRow (τ ξ) l.val.2.2.val.2)
    (P : Ideal O) (hP : P ≠ 0) (hCP : l.val.2.1.1 ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
        (χ₁.modulus * P)) I := by
  let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2 *
    nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1) * l.val.2.2.val.2
  have he : jointFirstFrequency left u₀ unit l.val * A = (nonzeroJointSourceRow l).val :=
    (joint_source_row_factorization left u₀ unit l.val).symm
  have hprod : jointFirstFrequency left u₀ unit l.val * A ≠ 0 := by
    rw [he]
    exact l.property
  let second := naturalRow (childCharacter χ₁ ξ) A (mul_ne_zero_iff.mp hprod).2
  let fixed := naturalRow (childCharacter η ξ)
    (jointFirstFrequency left u₀ unit l.val * A) hprod
  have h := actual_retained_fixed_dictionary_mask η χ₁ _ first hfirst
    _ _ hC hD hCD _ τ hf ξ _ F second fixed P hP hCP I
  apply h.trans
  rw [excluded_ideal _ _ (mul_ne_zero χ₁.modulus_ne_bot hP),
    excluded_ideal _ _ (mul_ne_zero χ₁.modulus_ne_bot hP)]
  split_ifs
  · rw [fixed.ideal, NaturalRow.ideal, he]
  · rfl

#print axioms joint_source_row_factorization
#print axioms actual_joint_retained_dictionary_mask

section WholeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_joint_whole_dictionary_mask (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (l : NonzeroJointSourceLabel left u₀ unit)
    (η₀ η χ₁ : Character) (first : NaturalRow η (jointFirstFrequency left u₀ unit l.val))
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (hC : Supported l.val.2.1.1) (hD : Supported l.val.2.1.2)
    (hCD : primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2)
    (τ : RayCharacter → Character)
    (hf : Family χ₁ l.val.2.1.1 l.val.2.1.2 hC hD l.val.2.2.val.1 τ)
    (ξ : RayCharacter) (F : NaturalRow (τ ξ) l.val.2.2.val.2)
    (P : Ideal O) (hP : P ≠ 0) (hCP : l.val.2.1.1 ∣ P)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ (excluded F.character P) j) I =
      idealCoeff (excluded (naturalRow
        (wholeSourceBase M H hH η₀ (childCharacter η ξ) j)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
        (χ₁.modulus * P)) I := by
  exact whole_source_family_mask M H hH η₀ (childCharacter η ξ)
    (excluded F.character P) _ (nonzeroJointSourceRow l).property
    (naturalRow _ _ (nonzeroJointSourceRow l).property) _
    (mul_ne_zero χ₁.modulus_ne_bot hP)
    (actual_joint_retained_dictionary_mask left u₀ unit l η χ₁ first hfirst
      hC hD hCD τ hf ξ F P hP hCP)
    (fun j => naturalRow _ _ (nonzeroJointSourceRow l).property) j I

#print axioms actual_joint_whole_dictionary_mask
end WholeFamily
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.ActualJointDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.JointAllocationEnergy; sha256 02ca851ca0a4c5156d85e7dc3fe74f612d2f2b2bda8af386a96fd74896bc3cad -/
section
                                           
                                                         

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators

/-- Select a maximizing allocation separately at each source label, then
apply one joint bound. Only the allocation weight is paid; there is no
additional count of source labels. Empty allocation sets contribute zero. -/
theorem joint_weighted_selection {Label : Type*} [Fintype Label]
    {β : Label→ Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (W E : ℝ) (hW : 0≤ W)
    (hw : ∀l a,0≤ weight l a) (hc : ∀l a,0≤ cost l a)
    (hmass : ∀l,∑a,weight l a≤ W)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∑l : S,cost l.val (pick l))≤ E) :
    (∑l,∑a,weight l a*cost l a)≤ W*E := by
  let S : Finset Label := Finset.univ.filter (fun l=>Nonempty (β l))
  have hnonempty (l : S) : (Finset.univ : Finset (β l.val)).Nonempty := by
    have : Nonempty (β l.val) := (Finset.mem_filter.mp l.property).2
    exact Finset.univ_nonempty
  choose pick hpick hmax using (fun l : S=>
    Finset.exists_max_image Finset.univ (cost l.val) (hnonempty l))
  have he := hjoint S pick
  have hsum : (∑l,∑a,weight l a*cost l a)=
      ∑l : S,∑a,weight l.val a*cost l.val a := by
    rw [Finset.sum_coe_sort S (fun l=>∑a,weight l a*cost l a)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l hl hnot
    have hempty : IsEmpty (β l) := ⟨fun a=>hnot (Finset.mem_filter.mpr ⟨hl,⟨a⟩⟩)⟩
    let _ := hempty
    simp
  rw [hsum]
  calc
    _ ≤ ∑l : S,W*cost l.val (pick l) := by
      apply Finset.sum_le_sum
      intro l hl
      calc
        _ ≤ ∑a,weight l.val a*cost l.val (pick l) :=
          Finset.sum_le_sum (fun a ha=>mul_le_mul_of_nonneg_left (hmax l a ha) (hw _ _))
        _ = (∑a,weight l.val a)*cost l.val (pick l) := (Finset.sum_mul ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (hmass _) (hc _ _)
    _ = W*∑l : S,cost l.val (pick l) := (Finset.mul_sum ..).symm
    _ ≤ W*E := mul_le_mul_of_nonneg_left he hW

/-- Zero-weight allocations are excluded before choosing maxima. This
retains the support information required for the sharp common-ideal shift. -/
theorem joint_supported_weighted_selection {Label : Type*} [Fintype Label]
    {β : Label→ Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (W E : ℝ) (hW : 0≤ W)
    (hw : ∀l a,0≤ weight l a) (hc : ∀l a,0≤ cost l a)
    (hmass : ∀l,∑a,weight l a≤ W)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∀l,weight l.val (pick l)≠0) → (∑l : S,cost l.val (pick l))≤ E) :
    (∑l,∑a,weight l a*cost l a)≤ W*E := by
  let live (l : Label) : Finset (β l) := Finset.univ.filter (fun a=>weight l a≠0)
  have he := joint_weighted_selection (β:=fun l=>live l)
    (fun l a=>weight l a.val) (fun l a=>cost l a.val) W E hW
    (fun l a=>hw l a.val) (fun l a=>hc l a.val)
    (fun l=> (le_of_eq (Finset.sum_coe_sort (live l) (weight l))).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _=>hw l a)).trans
        (hmass l)))
    (fun S pick=>hjoint S (fun l=>(pick l).val)
      (fun l=>(Finset.mem_filter.mp (pick l).property).2))
  have heq (l : Label) : (∑a : live l,weight l a.val*cost l a.val)=
      ∑a,weight l a*cost l a := by
    rw [Finset.sum_coe_sort (live l) (fun a=>weight l a*cost l a)]
    simp only [live,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h:weight l a=0 <;> simp [h]
  simpa only [heq] using he


/-- Repeated physical rows are selected jointly over their encoded image.
The fiber size is paid once; the bound on selected costs still ranges over
all encoded rows together. -/
theorem joint_fiber_selection {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→ Key) (cost : Row→ℝ) (W E : ℝ) (hW : 0≤ W)
    (hc : ∀r,0≤ cost r)
    (hmass : ∀k∈Finset.univ.image key,
      ((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤ W)
    (hjoint : ∀pick : (k : Finset.univ.image key)→ Row,
      (∀k,key (pick k)=k.val) → (∑k : Finset.univ.image key,cost (pick k))≤ E) :
    (∑r,cost r)≤ W*E := by
  let keys := Finset.univ.image key
  let fiber (k : Key) := Finset.univ.filter (fun r=>key r=k)
  have hnonempty (k : keys) : (fiber k.val).Nonempty := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp k.property
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩
  choose pick hpick hmax using (fun k : keys=>
    Finset.exists_max_image (fiber k.val) cost (hnonempty k))
  have he := hjoint pick (fun k=>(Finset.mem_filter.mp (hpick k)).2)
  have hsum : (∑k : keys,∑r∈fiber k.val,cost r)=∑r,cost r := by
    rw [Finset.sum_coe_sort keys (fun k=>∑r∈fiber k,cost r)]
    exact Finset.sum_fiberwise_of_maps_to (fun r hr=>Finset.mem_image_of_mem key hr) cost
  rw [←hsum]
  calc
    _≤∑k : keys,W*cost (pick k) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _≤∑_r∈fiber k.val,cost (pick k) := Finset.sum_le_sum (fun r hr=>hmax k r hr)
        _=(fiber k.val).card*cost (pick k) := by simp
        _≤ W*cost (pick k) := mul_le_mul_of_nonneg_right (hmass k.val k.property) (hc _)
    _=W*∑k : keys,cost (pick k) := (Finset.mul_sum ..).symm
    _≤ W*E := mul_le_mul_of_nonneg_left he hW

open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonLinearNormalization
local notation "O" => HeckeFamily.O

/-- The actual squared common coefficients, including the allocation
Cauchy factor, cost only a small power of the common ideal beyond its
inverse norm. Slot controls remain exactly quadratic. -/
theorem uniform_common_scalar_mass (N : ℕ) (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι],
      Fintype.card ι≤ N → ∀s : Input ι,s.upper≤ b → ∀C R : Ideal O,C≠0 →
      ((actualAllocations s.pools C).card:ℝ)*
        (∑B : actualAllocations s.pools C,‖commonScalar s C R B‖^2)≤
          K*(∏i,s.M i)^2*(C.absNorm:ℝ)^(ε-1) := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2*(max 1 b)^N,by positivity,?_⟩
  intro ι _ _ hn s hs C R hC
  have hnorm : 0<(C.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos C hC
  have hc := hcard (ι:=ι⊕Fin 2)
    (by simp only [Fintype.card_sum,Fintype.card_fin];omega) s.pools C hC
  have hc₂ := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hc 2
  rw [mul_pow,←Real.rpow_mul_natCast hnorm.le,show ε/2*(2:ℕ)=ε by norm_num] at hc₂
  have hsup : (max 1 s.upper)^Fintype.card ι≤(max 1 b)^N :=
    (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (max_le_max_left 1 hs) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hn)
  have hpoint (B : actualAllocations s.pools C) : ‖commonScalar s C R B‖^2≤
      (∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ) :=
    (commonScalar_sq_bound s C R hC B).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsup (sq_nonneg _)) hnorm.le)
  calc
    _ ≤ ((actualAllocations s.pools C).card:ℝ)*
        ∑_B : actualAllocations s.pools C,(∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hpoint B)) (Nat.cast_nonneg _)
    _ = ((actualAllocations s.pools C).card:ℝ)^2*
        ((∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ)) := by simp;ring
    _ ≤ (D^2*(C.absNorm:ℝ)^ε)*
        ((∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hc₂ (by positivity)
    _ = _ := by rw [Real.rpow_sub hnorm,Real.rpow_one];ring

/-- Applies joint allocation selection to the literal common retained cost,
after every residual shell has been summed at its original source. -/
theorem actual_joint_common_cost_selection {Label ι : Type*} [Fintype Label]
    [Fintype ι] [DecidableEq ι]
    (s : Label→ Input ι) (C R : Label→ Ideal O) (Ds : Label→ Finset (Ideal O))
    (z : Label→ O) (W E : ℝ) (hW : 0≤ W)
    (hmass : ∀l,((actualAllocations (s l).pools (C l)).card:ℝ)*
      (∑B : actualAllocations (s l).pools (C l),‖commonScalar (s l) (C l) (R l) B‖^2)≤ W)
    (hjoint : ∀S : Finset Label,
      ∀pick : (l : S)→ actualAllocations (s l.val).pools (C l.val),
      (∑l : S,∑L∈Ds l.val,
        ∑a∈(commonData (s l.val) (C l.val) (R l.val) (pick l)).toSource.active L,
          retainedAllocationCost (commonData (s l.val) (C l.val) (R l.val) (pick l))
            L a (z l.val))≤ E) :
    (∑l,∑L∈Ds l,commonRetainedCost (s l) (C l) (R l) L (z l))≤ W*E := by
  have hh := joint_weighted_selection
    (fun l (B : actualAllocations (s l).pools (C l))=>
      ((actualAllocations (s l).pools (C l)).card:ℝ)*‖commonScalar (s l) (C l) (R l) B‖^2)
    (fun l (B : actualAllocations (s l).pools (C l))=>
      ∑L∈Ds l,∑a∈(commonData (s l) (C l) (R l) B).toSource.active L,
        retainedAllocationCost (commonData (s l) (C l) (R l) B) L a (z l))
    W E hW (fun _ _=>by positivity)
    (fun _ _=>Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>
      retained_allocation_cost_nonneg _ _ _ _)))
    (fun l=>by rw [←Finset.mul_sum];exact hmass l) hjoint
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro l hl
  simp only [commonRetainedCost,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.joint_weighted_selection
#print axioms OAI.SevenEighths.Cycle61Moment.actual_joint_common_cost_selection
#print axioms OAI.SevenEighths.Cycle61Moment.uniform_common_scalar_mass

#print axioms OAI.SevenEighths.Cycle61Moment.joint_supported_weighted_selection

#print axioms OAI.SevenEighths.Cycle61Moment.joint_fiber_selection

end
/- END ORIGINAL Cycle61.Moment.JointAllocationEnergy -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.FirstProjectorMultiplicity; sha256 000748078f8fa6b02ab52d5368ef893fb606f51685ace60180a86ac3a0fa3aa1 -/
section
                                      
                                           

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- Only the first projector has this divisor provenance. No divisibility
of the residual second projector is asserted here. -/
theorem actual_first_projector_dvd_joint_row (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel→ O) (l : JointSourceLabel) (L : Ideal O)
    (hL : Squarefree L) (hC : Supported l.2.1.1) (hD : l.2.1.2≠0)
    (hLC : L∣l.2.1.1) (hLD : L∣l.2.1.2) :
    L∣Ideal.span {jointSourceRow left u₀ unit l} := by
  have hd := Cycle61.Physical.first_projector_dvd_frequency L _ _ hL hC hD hLC hLD
  apply hd.trans
  obtain ⟨v,hv⟩ := joint_source_second_generator_dvd left u₀ unit l
  rw [hv,←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_right _ _

theorem first_projector_small_power (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀Z : ℝ,1≤ Z → ∀w : O,w≠0 →
      ((Ideal.span {w}).absNorm:ℝ)≤ Z^B → ∀Ls : Finset (Ideal O),
      (∀L∈Ls,Squarefree L) → (∀L∈Ls,L∣Ideal.span {w}) →
      (Ls.card:ℝ)≤ K*Z^ε := by
  let δ := ε/(B+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨K,hK,hbound⟩ := SquarefreeDivisorBound.squarefree_divisor_small_power δ hδ
  refine ⟨K,hK,?_⟩
  intro Z hZ w hw hnorm Ls hL hd
  have hN : Ideal.span {w}≠0 := Ideal.span_singleton_eq_bot.not.mpr hw
  have hsub : Ls⊆(idealDivisors (Ideal.span {w})).filter Squarefree := by
    intro L hl
    exact Finset.mem_filter.mpr ⟨(mem_idealDivisors hN).mpr (hd L hl),hL L hl⟩
  have hc : (Ls.card:ℝ)≤((idealDivisors (Ideal.span {w})).filter Squarefree).card := by
    exact_mod_cast Finset.card_le_card hsub
  have he : B*δ≤ε := by
    have hid : δ*(B+1)=ε := by dsimp [δ]; field_simp
    nlinarith
  calc
    _≤ K*((Ideal.span {w}).absNorm:ℝ)^δ := hc.trans (hbound _ hN)
    _≤ K*(Z^B)^δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le) hK.le
    _=K*Z^(B*δ) := by rw [←Real.rpow_mul (zero_le_one.trans hZ)]
    _≤ K*Z^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) hK.le

/-- Repeated first-projector labels cost only the divisor small power.
The selected energy estimate is still a single joint row estimate. -/
theorem actual_first_projector_joint_selection (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀Z : ℝ,1≤ Z → ∀{Label : Type*}[Fintype Label]
      (row : Label→ O) (Ls : Label→ Finset (Ideal O))
      (cost : (l : Label)→ Ls l→ℝ) (E : ℝ),
      (∀l,row l≠0) → (∀l,((Ideal.span {row l}).absNorm:ℝ)≤ Z^B) →
      (∀l,Ls l⊆(idealDivisors (Ideal.span {row l})).filter Squarefree) →
      (∀l L,0≤ cost l L) →
      (∀S : Finset Label,∀pick : (l : S)→ Ls l.val,(∑l : S,cost l.val (pick l))≤ E) →
      (∑l,∑L : Ls l,cost l L)≤(K*Z^ε)*E := by
  obtain ⟨K,hK,hbound⟩ := first_projector_small_power B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ row Ls cost E hrow hnorm hLs hc he
  have hh := joint_weighted_selection (fun l (_L : Ls l)=>(1:ℝ)) cost (K*Z^ε) E
    (mul_nonneg hK.le (Real.rpow_nonneg (zero_le_one.trans hZ) _))
    (fun _ _=>zero_le_one) hc ?_ he
  · simpa only [one_mul] using hh
  intro l
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one]
  exact hbound Z hZ (row l) (hrow l) (hnorm l) (Ls l)
    (fun L hL=>(Finset.mem_filter.mp (hLs l hL)).2)
    (fun L hL=>(mem_idealDivisors (Ideal.span_singleton_eq_bot.not.mpr (hrow l))).mp
      (Finset.mem_filter.mp (hLs l hL)).1)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_projector_dvd_joint_row
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_projector_small_power
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_projector_joint_selection

end
/- END ORIGINAL Cycle61.Physical.InitialMass.FirstProjectorMultiplicity -/
