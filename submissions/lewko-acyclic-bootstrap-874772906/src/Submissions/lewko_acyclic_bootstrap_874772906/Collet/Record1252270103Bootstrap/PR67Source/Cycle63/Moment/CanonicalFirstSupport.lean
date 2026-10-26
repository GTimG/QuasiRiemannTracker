import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.CanonicalFirstNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinRadical
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic CanonicalRowCompletion
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCommonSupport
open CenteredMomentCompleteCommon
open CenteredMomentFirstDiscardedEnergy CenteredMomentRankinRadical
open UniqueFactorizationMonoid
open IdealMobiusDivisorSum hiding primeSupport
local notation "O" => HeckeFamily.O

def firstRetainedCommon (C D : Ideal O) (left : Bool) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P =>
    netExponent (leftExponent C D P) (rightExponent C D P) ≠ 0 ∧
      (if left then 1+netExponent (leftExponent C D P) (rightExponent C D P)
        else 7-netExponent (leftExponent C D P) (rightExponent C D P)) ≠ 6)

def firstProjectorRadical (C D : Ideal O) (E : Finset (CommonIndex C D)) : Ideal O :=
  ∏ P ∈ E, P.val

def firstRetainedCommonRadical (C D : Ideal O) (left : Bool) : Ideal O :=
  ∏ P ∈ firstRetainedCommon C D left, P.val

def firstMissingCommon (C D : Ideal O) (E : Finset (CommonIndex C D))
    (left : Bool) : Finset (CommonIndex C D) :=
  Finset.univ \ (E ∪ firstRetainedCommon C D left)

def firstMissingRadical (C D : Ideal O) (E : Finset (CommonIndex C D))
    (left : Bool) : Ideal O := ∏ P ∈ firstMissingCommon C D E left, P.val

theorem first_projector_retained_disjoint (C D : Ideal O)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) (left : Bool) :
    Disjoint E (firstRetainedCommon C D left) := by
  apply Finset.disjoint_left.mpr
  intro P hP hR
  have hp := Finset.mem_powerset.mp hE hP
  have hzero := (Finset.mem_filter.mp hp).2
  exact (Finset.mem_filter.mp hR).2.1 hzero

theorem first_common_radical_product (C D : Ideal O) :
    commonRadical C D = ∏ P : CommonIndex C D, P.val := by
  change (∏ P ∈ commonSupport C D, P) = _
  exact (Finset.prod_coe_sort (s := commonSupport C D) (f := fun P : Ideal O => P)).symm

/-- The first projector is counted once; the remainder is precisely the
radical not already visible in the retained signed row. -/
theorem actual_first_radical_partition (C D : Ideal O) (E : Finset (CommonIndex C D))
    (hE : E ∈ inactiveSubsets C D) (left : Bool) :
    commonRadical C D = firstProjectorRadical C D E *
      firstRetainedCommonRadical C D left * firstMissingRadical C D E left := by
  rw [first_common_radical_product]
  dsimp only [firstProjectorRadical, firstRetainedCommonRadical,
    firstMissingRadical, firstMissingCommon]
  rw [← Finset.prod_union (first_projector_retained_disjoint C D E hE left)]
  exact (Finset.prod_sdiff (Finset.subset_univ (E ∪ firstRetainedCommon C D left))).symm.trans
    (by ring)

theorem first_retained_left_radical (C D : Ideal O) :
    firstRetainedCommonRadical C D true = firstLeftRadical C D := by
  let S := firstRetainedCommon C D true
  have hs : S.subtype (fun P => P ∈ ActiveIndex C D) =
      Finset.univ.filter (fun P : ActiveIndex C D => 1+activeExponent C D P ≠ 6) := by
    ext P
    have hp := netExponent_ne_zero _ _ _ P
    simp only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [S, firstRetainedCommon, Finset.mem_filter, Finset.mem_univ, true_and, ite_true]
    change (netExponent (leftExponent C D P.val) (rightExponent C D P.val) ≠ 0 ∧
      1+activeExponent C D P ≠ 6) ↔ 1+activeExponent C D P ≠ 6
    exact and_iff_right hp
  have hh := Finset.prod_subtype_eq_prod_filter (s := S) (fun P : CommonIndex C D => P.val)
    (p := fun P => P ∈ ActiveIndex C D)
  have ht : S.filter (fun P => P ∈ ActiveIndex C D) = S := by
    apply Finset.filter_true_of_mem
    intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hP).2.1⟩
  rw [hs, ht] at hh
  exact hh.symm

theorem first_retained_right_radical (C D : Ideal O) :
    firstRetainedCommonRadical C D false = firstRightRadical C D := by
  let S := firstRetainedCommon C D false
  have hs : S.subtype (fun P => P ∈ ActiveIndex C D) =
      Finset.univ.filter (fun P : ActiveIndex C D => 7-activeExponent C D P ≠ 6) := by
    ext P
    have hp := netExponent_ne_zero _ _ _ P
    simp only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [S, firstRetainedCommon, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, ite_false]
    change (netExponent (leftExponent C D P.val) (rightExponent C D P.val) ≠ 0 ∧
      7-activeExponent C D P ≠ 6) ↔ 7-activeExponent C D P ≠ 6
    exact and_iff_right hp
  have hh := Finset.prod_subtype_eq_prod_filter (s := S) (fun P : CommonIndex C D => P.val)
    (p := fun P => P ∈ ActiveIndex C D)
  have ht : S.filter (fun P => P ∈ ActiveIndex C D) = S := by
    apply Finset.filter_true_of_mem
    intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hP).2.1⟩
  rw [hs, ht] at hh
  exact hh.symm

theorem first_projector_span (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} =
      firstProjectorRadical C D E := by
  rw [primeSubsetGenerator, span_idealGenerator]
  rfl

theorem powered_numerator_radical_dvd {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (ht : ∀ i ∈ S, 0 < t i) :
    (∏ i ∈ S, Ideal.span {p i}) ∣ Ideal.span {∏ i ∈ S, p i^(t i)} := by
  change _ ∣ principalIdealHom (∏ i ∈ S, p i^(t i))
  rw [map_prod]
  simp only [map_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i hi =>
    dvd_pow_self _ (Nat.ne_zero_of_lt (ht i hi)))

theorem first_left_radical_dvd_numerator (C D : Ideal O) (hC : Supported C) :
    firstLeftRadical C D ∣ Ideal.span {firstLeftUncancelled C D} := by
  have hh := powered_numerator_radical_dvd
    (Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 1+activeExponent C D P) (fun _ _ => by omega)
  simpa only [firstLeftRadical, firstLeftUncancelled, firstSignedPrime_span C D hC] using hh

theorem first_right_radical_dvd_numerator (C D : Ideal O) (hC : Supported C) :
    firstRightRadical C D ∣ Ideal.span {firstRightUncancelled C D} := by
  have hh := powered_numerator_radical_dvd
    (Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 7-activeExponent C D P) (by
      intro P _
      have h6 : activeExponent C D P < 6 := netExponent_lt_six _ _
      omega)
  simpa only [firstRightRadical, firstRightUncancelled, firstSignedPrime_span C D hC] using hh

theorem actual_first_left_radical_visible (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) :
    commonRadical C D ∣
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        firstLeftUncancelled C D} * firstMissingRadical C D E true := by
  rw [actual_first_radical_partition C D E hE true, first_retained_left_radical,
    ← Ideal.span_singleton_mul_span_singleton, first_projector_span]
  exact mul_dvd_mul (mul_dvd_mul dvd_rfl (first_left_radical_dvd_numerator C D hC)) dvd_rfl

theorem actual_first_right_radical_visible (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) :
    commonRadical C D ∣
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        firstRightUncancelled C D} * firstMissingRadical C D E false := by
  rw [actual_first_radical_partition C D E hE false, first_retained_right_radical,
    ← Ideal.span_singleton_mul_span_singleton, first_projector_span]
  exact mul_dvd_mul (mul_dvd_mul dvd_rfl (first_right_radical_dvd_numerator C D hC)) dvd_rfl

theorem firstCommonSubsetNorm_pos (C D : Ideal O) (hC : Supported C)
    (S : Finset (CommonIndex C D)) : 0 < (∏ P ∈ S, P.val).absNorm := by
  rw [map_prod]
  exact Finset.prod_pos (fun P _ => Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentSecondCanonical.commonPrime_supported_ideal C D hC P).1))

theorem actual_first_missing_width (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D)
    (left : Bool) (Z : ℝ) :
    Real.logb Z (firstMissingRadical C D E left).absNorm =
      Real.logb Z (commonRadical C D).absNorm-
      Real.logb Z (firstRetainedCommonRadical C D left).absNorm-
      Real.logb Z (firstProjectorRadical C D E).absNorm := by
  have hp : 0 < ((firstProjectorRadical C D E).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos C D hC E
  have hr : 0 < ((firstRetainedCommonRadical C D left).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos C D hC (firstRetainedCommon C D left)
  have hm : 0 < ((firstMissingRadical C D E left).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos C D hC (firstMissingCommon C D E left)
  rw [actual_first_radical_partition C D E hE left]
  simp only [map_mul, Nat.cast_mul]
  rw [Real.logb_mul (mul_ne_zero hp.ne' hr.ne') hm.ne',
    Real.logb_mul hp.ne' hr.ne']
  ring

theorem actual_first_left_missing_width (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) (Z : ℝ) :
    Real.logb Z (firstMissingRadical C D E true).absNorm =
      Real.logb Z (commonRadical C D).absNorm-
      Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
      Real.logb Z (firstProjectorRadical C D E).absNorm+
      Real.logb Z (firstLeftCancelledRadical C D).absNorm := by
  rw [actual_first_missing_width C D hC E hE true, first_retained_left_radical]
  have hk : 0 < ((firstLeftCancelledRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC (firstLeftCancelled C D)
  have hr : 0 < ((firstLeftRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC
      (Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6))
  rw [actual_first_left_radical_split]
  simp only [map_mul, Nat.cast_mul]
  rw [Real.logb_mul hk.ne' hr.ne']
  ring

theorem actual_first_right_missing_width (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) (Z : ℝ) :
    Real.logb Z (firstMissingRadical C D E false).absNorm =
      Real.logb Z (commonRadical C D).absNorm-
      Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
      Real.logb Z (firstProjectorRadical C D E).absNorm+
      Real.logb Z (firstRightCancelledRadical C D).absNorm := by
  rw [actual_first_missing_width C D hC E hE false, first_retained_right_radical]
  have hk : 0 < ((firstRightCancelledRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC (firstRightCancelled C D)
  have hr : 0 < ((firstRightRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC
      (Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6))
  rw [actual_first_right_radical_split]
  simp only [map_mul, Nat.cast_mul]
  rw [Real.logb_mul hk.ne' hr.ne']
  ring

theorem literal_effective_row_visible (u₀ e F G V h : O) (K R : Ideal O)
    (hR : R ∣ Ideal.span {e*F}*K) :
    R ∣ Ideal.span {effectiveRow u₀ e F G V h}*K := by
  have hd : e*F ∣ effectiveRow u₀ e F G V h := ⟨u₀*G*V*h, by dsimp [effectiveRow]; ring⟩
  have hi : Ideal.span {e*F} ∣ Ideal.span {effectiveRow u₀ e F G V h} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)
  exact hR.trans (mul_dvd_mul hi dvd_rfl)

theorem primeSupport_subset_of_dvd (R N : Ideal O) (hN : N ≠ 0) (hd : R ∣ N) :
    primeSupport R ⊆ primeSupport N := by
  intro P hP
  have hp := support_prime hP
  have hdiv := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  simpa only [primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hN, hp, true_and]
    using hdiv.trans hd

theorem actual_first_left_support_visible (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D)
    (u₀ G V h : O)
    (hw : effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
      (firstLeftUncancelled C D) G V h ≠ 0) :
    primeSupport C ⊆ primeSupport
      (Ideal.span {effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (firstLeftUncancelled C D) G V h} * firstMissingRadical C D E true) := by
  have hm : firstMissingRadical C D E true ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mp
      (Nat.ne_of_gt (firstCommonSubsetNorm_pos C D hC (firstMissingCommon C D E true)))
  have hn := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hm
  have hd := literal_effective_row_visible u₀
    (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
    (firstLeftUncancelled C D) G V h _ _ (actual_first_left_radical_visible C D hC E hE)
  have hs := primeSupport_subset_of_dvd _ _ hn hd
  have hc : primeSupport (commonRadical C D) = primeSupport C ∩ primeSupport D :=
    commonRadical_support C D
  rwa [hc, ← hCD, Finset.inter_self] at hs

theorem actual_first_right_support_visible (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D)
    (u₀ G V h : O)
    (hw : effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
      (firstRightUncancelled C D) G V h ≠ 0) :
    primeSupport C ⊆ primeSupport
      (Ideal.span {effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (firstRightUncancelled C D) G V h} * firstMissingRadical C D E false) := by
  have hm : firstMissingRadical C D E false ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mp
      (Nat.ne_of_gt (firstCommonSubsetNorm_pos C D hC (firstMissingCommon C D E false)))
  have hn := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hm
  have hd := literal_effective_row_visible u₀
    (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
    (firstRightUncancelled C D) G V h _ _ (actual_first_right_radical_visible C D hC E hE)
  have hs := primeSupport_subset_of_dvd _ _ hn hd
  have hc : primeSupport (commonRadical C D) = primeSupport C ∩ primeSupport D :=
    commonRadical_support C D
  rwa [hc, ← hCD, Finset.inter_self] at hs

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
