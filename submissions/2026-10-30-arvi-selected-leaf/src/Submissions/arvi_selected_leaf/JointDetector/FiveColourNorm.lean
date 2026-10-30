/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.PowerPairGauss
import Submissions.arvi_selected_leaf.JointDetector.SelectedBilinear
import Submissions.arvi_selected_leaf.JointDetector.SelectedReflection

/-!
# Fixed colour-one swap for arbitrary selected natural rows

Only the free colour-one radicals enter an operator norm. Every other colour
is a bounded coefficient independent of the ordinary dual source. The two
selected fibre families and their complex vectors may be different. Divisor
selectors are expanded before Cauchy; cross-colour natural zeros are retained.
No five-colour analytic norm estimate is assumed or asserted here.
-/
namespace Qrh.JointDetector.FiveColourNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

/-- Colours two through five have cross exponents one through four. -/
def pivotPhase (u : O) (higher : Fin 4 → Ideal O) : ℂ :=
  ∏ j : Fin 4, idealRowHom u (higher j)^(j.val+1)

theorem pivotPhase_norm_le (u : O) (higher : Fin 4 → Ideal O) : ‖pivotPhase u higher‖ ≤ 1 := by
  rw [pivotPhase, norm_prod]
  apply Finset.prod_le_one₀
  · intro j _; positivity
  · intro j _; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (idealRowHom_norm _ _)

theorem pivotPhase_zero_of_shared_prime (u : O) (higher : Fin 4 → Ideal O)
    (j : Fin 4) (P : Ideal O) (hP : Prime P) (hdiv : P ∣ higher j) (hu : u ∈ P) :
    pivotPhase u higher = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [idealRowHom_zero_of_dvd u hP hdiv hu, zero_pow (by omega : j.val+1 ≠ 0)]

theorem idealRowHom_zero_of_not_coprime (u : O) (hu : u ≠ 0) (I : Ideal O)
    (hcop : ¬IsCoprime (Ideal.span {u}) I) : idealRowHom u I = 0 := by
  have hproper : (Ideal.span {u} : Ideal O) ⊔ I ≠ ⊤ := by
    simpa only [Ideal.isCoprime_iff_sup_eq] using hcop
  obtain ⟨P,hP,hsub⟩ := Ideal.exists_le_maximal _ hproper
  have hup : u ∈ P := hsub ((show (Ideal.span {u} : Ideal O) ≤ Ideal.span {u} ⊔ I from le_sup_left)
    (Ideal.subset_span (by simp)))
  have hP0 : P ≠ 0 := by intro he; exact hu (by simpa [he] using hup)
  exact idealRowHom_zero_of_dvd u ((Ideal.prime_iff_isPrime hP0).2 hP.isPrime)
    (Ideal.dvd_iff_le.mpr (le_sup_right.trans hsub)) hup

/-- Every cross-coprime selector involving the pivot is an existing zero of
the actual phase, including colour four (exponent three). -/
theorem pivotPhase_cross_mask (u : O) (hu : u ≠ 0) (higher : Fin 4 → Ideal O) :
    (if ∀ j, IsCoprime (Ideal.span {u}) (higher j) then pivotPhase u higher else 0) =
      pivotPhase u higher := by
  split_ifs with hc
  · rfl
  · obtain ⟨j,hj⟩ := not_forall.mp hc
    have hz : pivotPhase u higher = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [idealRowHom_zero_of_not_coprime u hu (higher j) hj,zero_pow (by omega : j.val+1 ≠ 0)]
    exact hz.symm

abbrev Fibre {V : Type*} (E : V → Finset O) := Σ v, E v

/-- One common divisor pool suffices even for unequal left/right families. -/
theorem coprime_indicator_pool (I J : Ideal O) (hJ : J ≠ 0)
    (pool : Finset (Ideal O)) (hpool : idealDivisors J ⊆ pool) :
    (if IsCoprime I J then (1 : ℂ) else 0) =
      ∑ d ∈ pool, if d ∣ I ∧ d ∣ J then (UniqueFactorizationMonoid.moebius d : ℂ) else 0 := by
  rw [CenteredMomentMask.ideal_coprime_mobius I J hJ]
  symm
  calc
    _ = ∑ d ∈ idealDivisors J, if d ∣ I ∧ d ∣ J then (UniqueFactorizationMonoid.moebius d : ℂ) else 0 := by
      symm
      apply Finset.sum_subset hpool
      intro d hd hnot
      have hn : ¬d ∣ J := fun h => hnot ((mem_idealDivisors hJ).2 h)
      simp only [hn,and_false,ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [(mem_idealDivisors hJ).1 hd,and_true]

/-- Exact asymmetric Möbius expansion for arbitrary signed kernels. It is
proved before any positive estimate and never uses matrix monotonicity. -/
theorem coprime_bilinear_pool {L R : Type*} [Fintype L] [Fintype R]
    (rowL : L → Ideal O) (rowR : R → Ideal O) (hR : ∀ r, rowR r ≠ 0)
    (pool : Finset (Ideal O)) (hpool : ∀ r, idealDivisors (rowR r) ⊆ pool)
    (V : L → R → ℂ) :
    (∑ l, ∑ r, if IsCoprime (rowL l) (rowR r) then V l r else 0) =
      ∑ d ∈ pool, (UniqueFactorizationMonoid.moebius d : ℂ)*
        ∑ l, ∑ r, if d ∣ rowL l ∧ d ∣ rowR r then V l r else 0 := by
  have hp (l : L) (r : R) : (if IsCoprime (rowL l) (rowR r) then V l r else 0) =
      ∑ d ∈ pool, (UniqueFactorizationMonoid.moebius d : ℂ)*
        (if d ∣ rowL l ∧ d ∣ rowR r then V l r else 0) := by
    calc
      _ = (if IsCoprime (rowL l) (rowR r) then (1 : ℂ) else 0)*V l r := by split_ifs <;> simp
      _ = _ := by
        rw [coprime_indicator_pool (rowL l) (rowR r) (hR r) pool (hpool r),Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> simp
  simp_rw [hp]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

section FiniteSwap
variable {VL VR D : Type*} [Fintype VL] [Fintype VR] [Fintype D]
variable (EL : VL → Finset O) (ER : VR → Finset O) (S : Finset (Ideal O))
variable (maskL : D → Fibre EL → Prop) (maskR : D → Fibre ER → Prop)
variable (A : Fibre EL → ℂ) (B : Fibre ER → ℂ)
variable (FL : O → VR → ℂ) (FR : O → VL → ℂ)

/-- The pivot phases multiply arbitrary dual coefficients; they do not change
the ordinary source family in the selected operator. -/
def leftWord (d : D) (v : VL) (w : VR) (I : S) : ℂ :=
  ∑ u : EL v, selectedMatrix (EL v) S I u *
    (maskedRowVector maskL A d ⟨v,u⟩ * star (FL u.val w))

def rightWord (d : D) (v : VL) (w : VR) (I : S) : ℂ :=
  ∑ u : ER w, star (selectedMatrix (ER w) S I u) *
    (maskedRowVector maskR B d ⟨w,u⟩ * FR u.val v)

/-- The higher-colour kernel is arbitrary and independent of the two pivot
radicals. The common source weight may depend on both higher tuples. -/
def expandedSwap (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ) (d : D) : ℂ :=
  ∑ v, ∑ w, ∑ I : S, H v w * weight v w I *
    leftWord EL S maskL A FL d v w I * rightWord ER S maskR B FR d v w I

theorem leftWord_energy_le (KL : ℝ) (hKL : 0 ≤ KL)
    (hEL : ∀ v, selectedNorm (EL v) S ≤ KL) (hFL : ∀ u w, ‖FL u w‖ ≤ 1)
    (d : D) (v : VL) (w : VR) :
    (∑ I : S, ‖leftWord EL S maskL A FL d v w I‖^2) ≤
      KL*∑ u : EL v, ‖maskedRowVector maskL A d ⟨v,u⟩‖^2 := by
  have hm : (∑ u : EL v, ‖maskedRowVector maskL A d ⟨v,u⟩ * star (FL u.val w)‖^2) ≤
      ∑ u : EL v, ‖maskedRowVector maskL A d ⟨v,u⟩‖^2 := by
    apply Finset.sum_le_sum
    intro u _
    rw [norm_mul,norm_star,mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hFL _ _))
  exact (selectedDualEnergy_le (EL v) S (fun u =>
    maskedRowVector maskL A d ⟨v,u⟩ * star (FL u.val w))).trans
    (mul_le_mul (hEL v) hm (by positivity) hKL)

theorem rightWord_energy_le (KR : ℝ) (hKR : 0 ≤ KR)
    (hER : ∀ w, selectedNorm (ER w) S ≤ KR) (hFR : ∀ u v, ‖FR u v‖ ≤ 1)
    (d : D) (v : VL) (w : VR) :
    (∑ I : S, ‖rightWord ER S maskR B FR d v w I‖^2) ≤
      KR*∑ u : ER w, ‖maskedRowVector maskR B d ⟨w,u⟩‖^2 := by
  have he (I : S) : rightWord ER S maskR B FR d v w I =
      star (∑ u : ER w, selectedMatrix (ER w) S I u *
        star (maskedRowVector maskR B d ⟨w,u⟩ * FR u.val v)) := by
    rw [star_sum]
    simp only [star_mul,star_star,rightWord]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp_rw [he,norm_star]
  have hm : (∑ u : ER w, ‖star (maskedRowVector maskR B d ⟨w,u⟩ * FR u.val v)‖^2) ≤
      ∑ u : ER w, ‖maskedRowVector maskR B d ⟨w,u⟩‖^2 := by
    apply Finset.sum_le_sum
    intro u _
    rw [norm_star,norm_mul,mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hFR _ _))
  exact (selectedDualEnergy_le (ER w) S (fun u =>
    star (maskedRowVector maskR B d ⟨w,u⟩ * FR u.val v))).trans
    (mul_le_mul (hER w) hm (by positivity) hKR)

/-- The finite swap for unequal, nonrectangular selected fibres and arbitrary
independent complex arrays. Both divisor masks remain inside the polynomials. -/
theorem expandedSwap_le (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
    (KL KR : ℝ) (hKL : 0 ≤ KL) (hKR : 0 ≤ KR)
    (hEL : ∀ v, selectedNorm (EL v) S ≤ KL) (hER : ∀ w, selectedNorm (ER w) S ≤ KR)
    (hFL : ∀ u w, ‖FL u w‖ ≤ 1) (hFR : ∀ u v, ‖FR u v‖ ≤ 1)
    (hH : ∀ v w, ‖H v w‖ ≤ 1) (hweight : ∀ v w I, ‖weight v w I‖ ≤ 1) (d : D) :
    ‖expandedSwap EL ER S maskL maskR A B FL FR H weight d‖ ≤
      Real.sqrt ((Fintype.card VR : ℝ)*KL*maskedEnergy maskL A d) *
      Real.sqrt ((Fintype.card VL : ℝ)*KR*maskedEnergy maskR B d) := by
  let left : VL × VR × S → ℂ := fun x => leftWord EL S maskL A FL d x.1 x.2.1 x.2.2
  let right : VL × VR × S → ℂ := fun x => rightWord ER S maskR B FR d x.1 x.2.1 x.2.2
  have hleft : (∑ x, ‖left x‖^2) ≤ (Fintype.card VR : ℝ)*KL*maskedEnergy maskL A d := by
    simp only [Fintype.sum_prod_type,left]
    calc
      _ ≤ ∑ v : VL, ∑ w : VR, KL*∑ u : EL v, ‖maskedRowVector maskL A d ⟨v,u⟩‖^2 := by
        apply Finset.sum_le_sum; intro v _
        apply Finset.sum_le_sum; intro w _
        exact leftWord_energy_le EL S maskL A FL KL hKL hEL hFL d v w
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        have hm : (∑ v : VL, ∑ u : EL v, ‖maskedRowVector maskL A d ⟨v,u⟩‖^2) = maskedEnergy maskL A d := by
          rw [← maskedRowVector_energy]
          exact (Fintype.sum_sigma (fun z : Fibre EL => ‖maskedRowVector maskL A d z‖^2)).symm
        rw [← Finset.mul_sum,← Finset.mul_sum,hm]
        ring
  have hright : (∑ x, ‖right x‖^2) ≤ (Fintype.card VL : ℝ)*KR*maskedEnergy maskR B d := by
    simp only [Fintype.sum_prod_type,right]
    calc
      _ ≤ ∑ v : VL, ∑ w : VR, KR*∑ u : ER w, ‖maskedRowVector maskR B d ⟨w,u⟩‖^2 := by
        apply Finset.sum_le_sum; intro v _
        apply Finset.sum_le_sum; intro w _
        exact rightWord_energy_le ER S maskR B FR KR hKR hER hFR d v w
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        have hm : (∑ w : VR, ∑ u : ER w, ‖maskedRowVector maskR B d ⟨w,u⟩‖^2) = maskedEnergy maskR B d := by
          rw [← maskedRowVector_energy]
          exact (Fintype.sum_sigma (fun z : Fibre ER => ‖maskedRowVector maskR B d z‖^2)).symm
        rw [← Finset.mul_sum,hm]
        ring
  calc
    _ ≤ ∑ x : VL × VR × S, ‖left x‖*‖right x‖ := by
      simp only [expandedSwap,Fintype.sum_prod_type]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro v _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro w _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum; intro I _
      simp only [norm_mul,left,right]
      have hp : ‖H v w‖*‖weight v w I‖ ≤ 1 :=
        (mul_le_mul (hH v w) (hweight v w I) (norm_nonneg _) zero_le_one).trans_eq (by ring)
      have hm := mul_le_mul_of_nonneg_right hp
        (mul_nonneg (norm_nonneg (leftWord EL S maskL A FL d v w I))
          (norm_nonneg (rightWord ER S maskR B FR d v w I)))
      nlinarith only [hm]
    _ ≤ Real.sqrt (∑ x, ‖left x‖^2)*Real.sqrt (∑ x, ‖right x‖^2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Summing divisor labels charges only row incidence, not the number of
labels. The two fibre families may have unequal divisor incidences. -/
theorem expandedSwap_masks_le (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
    (μ : D → ℂ) (KL KR DL DR : ℝ)
    (hKL : 0 ≤ KL) (hKR : 0 ≤ KR) (hDL : 0 ≤ DL) (hDR : 0 ≤ DR)
    (hEL : ∀ v, selectedNorm (EL v) S ≤ KL) (hER : ∀ w, selectedNorm (ER w) S ≤ KR)
    (hFL : ∀ u w, ‖FL u w‖ ≤ 1) (hFR : ∀ u v, ‖FR u v‖ ≤ 1)
    (hH : ∀ v w, ‖H v w‖ ≤ 1) (hweight : ∀ v w I, ‖weight v w I‖ ≤ 1)
    (hμ : ∀ d, ‖μ d‖ ≤ 1)
    (hincL : ∀ u, ((Finset.univ.filter fun d => maskL d u).card : ℝ) ≤ DL)
    (hincR : ∀ u, ((Finset.univ.filter fun d => maskR d u).card : ℝ) ≤ DR) :
    ‖∑ d, μ d*expandedSwap EL ER S maskL maskR A B FL FR H weight d‖ ≤
      Real.sqrt ((Fintype.card VR : ℝ)*KL*DL*(∑ u, ‖A u‖^2)) *
      Real.sqrt ((Fintype.card VL : ℝ)*KR*DR*(∑ u, ‖B u‖^2)) := by
  have hleft : (∑ d, (Fintype.card VR : ℝ)*KL*maskedEnergy maskL A d) ≤
      (Fintype.card VR : ℝ)*KL*DL*(∑ u, ‖A u‖^2) := by
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_maskedEnergy_le maskL A DL hincL) (by positivity)).trans_eq (by ring)
  have hright : (∑ d, (Fintype.card VL : ℝ)*KR*maskedEnergy maskR B d) ≤
      (Fintype.card VL : ℝ)*KR*DR*(∑ u, ‖B u‖^2) := by
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_maskedEnergy_le maskR B DR hincR) (by positivity)).trans_eq (by ring)
  calc
    _ ≤ ∑ d, ‖μ d*expandedSwap EL ER S maskL maskR A B FL FR H weight d‖ := norm_sum_le _ _
    _ ≤ ∑ d, Real.sqrt ((Fintype.card VR : ℝ)*KL*maskedEnergy maskL A d)*
        Real.sqrt ((Fintype.card VL : ℝ)*KR*maskedEnergy maskR B d) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hμ d)).trans
        (expandedSwap_le EL ER S maskL maskR A B FL FR H weight KL KR hKL hKR hEL hER hFL hFR hH hweight d)
    _ ≤ Real.sqrt (∑ d, (Fintype.card VR : ℝ)*KL*maskedEnergy maskL A d)*
        Real.sqrt (∑ d, (Fintype.card VL : ℝ)*KR*maskedEnergy maskR B d) :=
      Real.sum_sqrt_mul_sqrt_le _
        (fun d => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKL) (maskedEnergy_nonneg maskL A d))
        (fun d => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKR) (maskedEnergy_nonneg maskR B d))
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The literal coprime pivot-pair form before Möbius expansion. -/
def coprimeSwap (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ) : ℂ :=
  ∑ v, ∑ w, ∑ I : S, H v w*weight v w I*
    ∑ u : EL v, ∑ q : ER w,
      if IsCoprime (Ideal.span {u.val}) (Ideal.span {q.val}) then
        (selectedMatrix (EL v) S I u*(A ⟨v,u⟩*star (FL u.val w)))*
          (star (selectedMatrix (ER w) S I q)*(B ⟨w,q⟩*FR q.val v)) else 0

/-- Exact expansion of the remaining pivot-pivot selector. All cross-colour
selectors are already the natural zeros of `pivotPhase_cross_mask`. -/
theorem coprimeSwap_eq_expanded (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
    (pool : Finset (Ideal O)) (hR : ∀ w, ∀ u : ER w, u.val ≠ 0)
    (hpool : ∀ w, ∀ u : ER w, idealDivisors (Ideal.span {u.val}) ⊆ pool) :
    coprimeSwap EL ER S A B FL FR H weight =
      ∑ d : pool, (UniqueFactorizationMonoid.moebius d.val : ℂ)*
        expandedSwap EL ER S
          (idealDivisorMask pool (fun u : Fibre EL => Ideal.span {u.2.val}))
          (idealDivisorMask pool (fun u : Fibre ER => Ideal.span {u.2.val}))
          A B FL FR H weight d := by
  let mL := idealDivisorMask pool (fun u : Fibre EL => Ideal.span {u.2.val})
  let mR := idealDivisorMask pool (fun u : Fibre ER => Ideal.span {u.2.val})
  have hp (v : VL) (w : VR) (I : S) :
      (∑ u : EL v, ∑ q : ER w,
        if IsCoprime (Ideal.span {u.val}) (Ideal.span {q.val}) then
          (selectedMatrix (EL v) S I u*(A ⟨v,u⟩*star (FL u.val w)))*
            (star (selectedMatrix (ER w) S I q)*(B ⟨w,q⟩*FR q.val v)) else 0) =
      ∑ d : pool, (UniqueFactorizationMonoid.moebius d.val : ℂ)*
        leftWord EL S mL A FL d v w I*rightWord ER S mR B FR d v w I := by
    rw [coprime_bilinear_pool (fun u : EL v => Ideal.span {u.val})
      (fun q : ER w => Ideal.span {q.val})
      (fun q => Ideal.span_singleton_eq_bot.not.mpr (hR w q)) pool (hpool w)]
    rw [← Finset.sum_coe_sort pool]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [leftWord,rightWord,Finset.sum_mul,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only [mL,mR,maskedRowVector,idealDivisorMask]
    split_ifs <;> simp_all <;> ring
  unfold coprimeSwap expandedSwap
  simp_rw [hp,Finset.mul_sum]
  conv_lhs => arg 2; ext v; arg 2; ext w; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext v; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- The actual finite coprime swap, with all ordinary ideal-divisor costs
paid before Cauchy. Its only norm inputs are those of the free colour-one
fibres, using powers one and five through whole conjugation. -/
theorem coprimeSwap_le (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
    (KL KR BL BR ε : ℝ) (hKL : 0 ≤ KL) (hKR : 0 ≤ KR)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hε : 0 < ε)
    (hEL : ∀ v, selectedNorm (EL v) S ≤ KL) (hER : ∀ w, selectedNorm (ER w) S ≤ KR)
    (hFL : ∀ u w, ‖FL u w‖ ≤ 1) (hFR : ∀ u v, ‖FR u v‖ ≤ 1)
    (hH : ∀ v w, ‖H v w‖ ≤ 1) (hweight : ∀ v w I, ‖weight v w I‖ ≤ 1)
    (hnL : ∀ v, ∀ u : EL v, u.val ≠ 0) (hnR : ∀ w, ∀ u : ER w, u.val ≠ 0)
    (hNL : ∀ v, ∀ u : EL v, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BL)
    (hNR : ∀ w, ∀ u : ER w, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BR) :
    ‖coprimeSwap EL ER S A B FL FR H weight‖ ≤
      Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2))*
      Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2)) := by
  let rowL : Fibre EL → Ideal O := fun u => Ideal.span {u.2.val}
  let rowR : Fibre ER → Ideal O := fun u => Ideal.span {u.2.val}
  let pool := rowDivisorPool rowR
  have hpool (w : VR) (u : ER w) : idealDivisors (Ideal.span {u.val}) ⊆ pool := by
    intro d hd
    exact Finset.mem_biUnion.mpr ⟨⟨w,u⟩,Finset.mem_univ _,hd⟩
  rw [coprimeSwap_eq_expanded EL ER S A B FL FR H weight pool hnR hpool]
  apply expandedSwap_masks_le EL ER S (idealDivisorMask pool rowL) (idealDivisorMask pool rowR)
    A B FL FR H weight (fun d => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    KL KR (idealDivisorConstant ε hε*BL^ε) (idealDivisorConstant ε hε*BR^ε)
    hKL hKR (by positivity [idealDivisorConstant_pos ε hε]) (by positivity [idealDivisorConstant_pos ε hε])
    hEL hER hFL hFR hH hweight
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val)
  · intro u
    exact idealDivisorMask_incidence_small_power pool rowL u
      (Ideal.span_singleton_eq_bot.not.mpr (hnL u.1 u.2)) ε hε BL (hNL u.1 u.2)
  · intro u
    exact idealDivisorMask_incidence_small_power pool rowR u
      (Ideal.span_singleton_eq_bot.not.mpr (hnR u.1 u.2)) ε hε BR (hNR u.1 u.2)

/-- The original higher-colour phases are a literal instance of the swap;
no operator norm of powers two, three or four occurs in this bound. -/
theorem fiveColour_pivot_swap_le (higherL : VL → Fin 4 → Ideal O)
    (higherR : VR → Fin 4 → Ideal O) (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
    (KL KR BL BR ε : ℝ) (hKL : 0 ≤ KL) (hKR : 0 ≤ KR)
    (hBL : 0 ≤ BL) (hBR : 0 ≤ BR) (hε : 0 < ε)
    (hEL : ∀ v, selectedNorm (EL v) S ≤ KL) (hER : ∀ w, selectedNorm (ER w) S ≤ KR)
    (hH : ∀ v w, ‖H v w‖ ≤ 1) (hweight : ∀ v w I, ‖weight v w I‖ ≤ 1)
    (hnL : ∀ v, ∀ u : EL v, u.val ≠ 0) (hnR : ∀ w, ∀ u : ER w, u.val ≠ 0)
    (hNL : ∀ v, ∀ u : EL v, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BL)
    (hNR : ∀ w, ∀ u : ER w, ((Ideal.span {u.val}).absNorm : ℝ) ≤ BR) :
    ‖coprimeSwap EL ER S A B (fun u w => pivotPhase u (higherR w))
      (fun u v => pivotPhase u (higherL v)) H weight‖ ≤
      Real.sqrt ((Fintype.card VR : ℝ)*KL*(idealDivisorConstant ε hε*BL^ε)*(∑ u, ‖A u‖^2))*
      Real.sqrt ((Fintype.card VL : ℝ)*KR*(idealDivisorConstant ε hε*BR^ε)*(∑ u, ‖B u‖^2)) :=
  coprimeSwap_le EL ER S A B (fun u w => pivotPhase u (higherR w))
    (fun u v => pivotPhase u (higherL v)) H weight KL KR BL BR ε hKL hKR hBL hBR hε
    hEL hER (fun u w => pivotPhase_norm_le u (higherR w))
    (fun u v => pivotPhase_norm_le u (higherL v)) hH hweight hnL hnR hNL hNR

end FiniteSwap
section SharedSupport
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- On one fixed original radical, every prime is either unshared or assigned
to exactly one of five opposite colours. No independent 25-tuple is summed. -/
def sharedTable (colour : P → Fin 5) (opposite : P → Option (Fin 5)) :
    Fin 5 × Fin 5 → Finset P := fun jk =>
  Finset.univ.filter (fun p => colour p = jk.1 ∧ opposite p = some jk.2)

def unsharedSupport (colour : P → Fin 5) (opposite : P → Option (Fin 5)) (j : Fin 5) : Finset P :=
  Finset.univ.filter (fun p => colour p = j ∧ opposite p = none)

/-- All twenty-five shared cells are mutually disjoint. -/
theorem sharedTable_pairwise_disjoint (colour : P → Fin 5) (opposite : P → Option (Fin 5)) :
    Pairwise (fun jk j'k' => Disjoint (sharedTable colour opposite jk) (sharedTable colour opposite j'k')) := by
  intro jk j'k' hne
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  have ha := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp hp').2
  have h1 : jk.1 = j'k'.1 := ha.1.symm.trans hb.1
  have h2 : jk.2 = j'k'.2 := Option.some.inj (ha.2.symm.trans hb.2)
  exact hne (Prod.ext h1 h2)

/-- Each original colour splits into its unshared part and all five shared
columns, including its diagonal cell. -/
theorem sharedTable_row_partition (colour : P → Fin 5) (opposite : P → Option (Fin 5)) (j : Fin 5) :
    unsharedSupport colour opposite j ∪
      Finset.univ.biUnion (fun k : Fin 5 => sharedTable colour opposite (j,k)) =
      Finset.univ.filter (fun p => colour p = j) := by
  ext p
  simp only [unsharedSupport,sharedTable,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
    true_and,Finset.mem_biUnion]
  cases h : opposite p <;> simp [h]

theorem sharedTable_injective (colour : P → Fin 5) : Function.Injective (sharedTable colour) := by
  intro a b hab
  funext p
  cases ha : a p with
  | none =>
    cases hb : b p with
    | none => rfl
    | some k =>
      have hm : p ∈ sharedTable colour b (colour p,k) := by simp [sharedTable,hb]
      rw [← hab] at hm
      simpa [sharedTable,ha] using hm
  | some k =>
    have hm : p ∈ sharedTable colour a (colour p,k) := by simp [sharedTable,ha]
    rw [hab] at hm
    have hb : b p = some k := (Finset.mem_filter.mp hm).2.2
    exact hb.symm

/-- Exactly six choices per original prime, rather than arbitrary independent
choices for all twenty-five cells. This is a row-incidence count. -/
theorem sharedTable_card (colour : P → Fin 5) :
    (Finset.univ.image (sharedTable colour)).card = 6^(Fintype.card P) := by
  rw [Finset.card_image_of_injective _ (sharedTable_injective colour),Finset.card_univ]
  simp

theorem selected_sharedTable_card_le (colour : P → Fin 5)
    (tables : Finset (Fin 5 × Fin 5 → Finset P))
    (h : ∀ table ∈ tables, ∃ opposite : P → Option (Fin 5), table = sharedTable colour opposite) :
    tables.card ≤ 6^(Fintype.card P) := by
  rw [← sharedTable_card colour]
  apply Finset.card_le_card
  intro table ht
  obtain ⟨opposite,rfl⟩ := h table ht
  exact Finset.mem_image.mpr ⟨opposite,Finset.mem_univ _,rfl⟩
/-- Literal intersections with the five opposite supports are one encoded
shared table whenever those supports are disjoint. This covers all 25 cells,
not merely diagonal gcds or the clean branch. -/
theorem sharedTable_of_disjoint_supports (colour : P → Fin 5) (right : Fin 5 → Finset P)
    (hright : Pairwise (fun j k => Disjoint (right j) (right k))) :
    ∃ opposite : P → Option (Fin 5), ∀ jk,
      sharedTable colour opposite jk = (Finset.univ.filter fun p => colour p = jk.1) ∩ right jk.2 := by
  let opposite : P → Option (Fin 5) := fun p =>
    if h : ∃ k, p ∈ right k then some (Classical.choose h) else none
  have hspec (p : P) (k : Fin 5) : opposite p = some k ↔ p ∈ right k := by
    dsimp only [opposite]
    by_cases h : ∃ k, p ∈ right k
    · rw [dif_pos h,Option.some.injEq]
      have hm := Classical.choose_spec h
      constructor
      · intro he; exact he ▸ hm
      · intro hk
        by_contra hne
        exact Finset.disjoint_left.mp (hright hne) hm hk
    · rw [dif_neg h]
      constructor
      · intro he; cases he
      · intro hk; exact False.elim (h ⟨k,hk⟩)
  refine ⟨opposite,?_⟩
  intro jk
  ext p
  simp only [sharedTable,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter,hspec]

end SharedSupport

/-- Exact shared-table scales, with all twenty-five shared supports retained
through G,H,J,E,F and the actual source puncture R. -/
def sharedDualScale (U V X G H J E F R : ℝ) : ℝ :=
  (U*V)^2*R/(X*G^2*H^2*J*E*F)

def sharedSwapCost (U V X G H J E F R δ : ℝ) : ℝ :=
  X*G/(U*R*Real.sqrt J)*
    Real.sqrt (((U/(G*E))^(1-δ)*(sharedDualScale U V X G H J E F R)^δ)*
      ((U/(G*F))^(1-δ)*(sharedDualScale U V X G H J E F R)^δ))

/-- Inserting the two short-source squarefree bounds pays every shared
stratum. All divisor powers are favorable; no diagonal is subtracted from
an upper envelope. This scalar statement has no analytic norm premise. -/
theorem sharedSwapCost_le (U V X G H J E F R δ : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hX : U*V^2 ≤ X)
    (hG : 1 ≤ G) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hE : 1 ≤ E) (hF : 1 ≤ F) (hR : 1 ≤ R)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) : sharedSwapCost U V X G H J E F R δ ≤ X := by
  have hXp : 0 < X := (by positivity : 0 < U*V^2).trans_le hX
  have hGp : 0 < G := by linarith
  have hHp : 0 < H := by linarith
  have hJp : 0 < J := by linarith
  have hEp : 0 < E := by linarith
  have hFp : 0 < F := by linarith
  have hRp : 0 < R := by linarith
  let Y := sharedDualScale U V X G H J E F R
  let BL := U/(G*E)
  let BR := U/(G*F)
  have hY : 0 < Y := by dsimp [Y,sharedDualScale]; positivity
  have hBL : 0 < BL := by dsimp [BL]; positivity
  have hBR : 0 < BR := by dsimp [BR]; positivity
  have hcost : 0 < sharedSwapCost U V X G H J E F R δ := by
    unfold sharedSwapCost
    positivity
  have hlogY : Real.log Y = 2*Real.log U+2*Real.log V+Real.log R-
      (Real.log X+2*Real.log G+2*Real.log H+Real.log J+Real.log E+Real.log F) := by
    dsimp [Y,sharedDualScale]
    simp [Real.log_mul,Real.log_div,Real.log_pow,hU.ne',hV.ne',hXp.ne',hGp.ne',hHp.ne',hJp.ne',hEp.ne',hFp.ne',hRp.ne']
    <;> ring
  have hlogBL : Real.log BL = Real.log U-Real.log G-Real.log E := by
    dsimp [BL]
    simp [Real.log_mul,Real.log_div,hU.ne',hGp.ne',hEp.ne']
    <;> ring
  have hlogBR : Real.log BR = Real.log U-Real.log G-Real.log F := by
    dsimp [BR]
    simp [Real.log_mul,Real.log_div,hU.ne',hGp.ne',hFp.ne']
    <;> ring
  have hlogCost : Real.log (sharedSwapCost U V X G H J E F R δ) =
      Real.log X+Real.log G-Real.log U-Real.log R-Real.log J/2+
        ((1-δ)*Real.log BL+δ*Real.log Y+(1-δ)*Real.log BR+δ*Real.log Y)/2 := by
    change Real.log (X*G/(U*R*Real.sqrt J)*Real.sqrt ((BL^(1-δ)*Y^δ)*(BR^(1-δ)*Y^δ))) = _
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul hXp.ne' hGp.ne',
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul hU.ne' hRp.ne', Real.log_sqrt hJp.le,
      Real.log_sqrt (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hBL, Real.log_rpow hBR, Real.log_rpow hY]
    ring
  have hlogX : 0 ≤ Real.log X-Real.log U-2*Real.log V := by
    have hh := Real.log_le_log (by positivity : 0 < U*V^2) hX
    rw [Real.log_mul hU.ne' (by positivity),Real.log_pow] at hh
    norm_num at hh
    linarith
  have hlogG := Real.log_nonneg hG
  have hlogH := Real.log_nonneg hH
  have hlogJ := Real.log_nonneg hJ
  have hlogE := Real.log_nonneg hE
  have hlogF := Real.log_nonneg hF
  have hlogR := Real.log_nonneg hR
  have hd0 : 0 ≤ δ := hδ.1
  have hd1 : 0 ≤ 1-δ := by linarith [hδ.2]
  have hfavorable : 0 ≤ δ*(Real.log X-Real.log U-2*Real.log V)+(1-δ)*Real.log R+
      δ*Real.log G+2*δ*Real.log H+(δ+1/2)*Real.log J+(1+δ)/2*(Real.log E+Real.log F) := by positivity
  apply (Real.log_le_log_iff hcost hXp).1
  rw [hlogCost,hlogBL,hlogBR,hlogY]
  nlinarith only [hfavorable]

/-- The usual squarefree envelope has the required short-source form with
an explicit factor two. This uses the same δ on both sides. -/
theorem short_source_envelope_le (B Y δ : ℝ) (hB : 0 < B) (hY : 0 < Y)
    (hYB : Y ≤ B) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Y+B^(1-δ)*Y^δ ≤ 2*(B^(1-δ)*Y^δ) := by
  have heq : Y = Y^(1-δ)*Y^δ := by
    rw [← Real.rpow_add hY]
    simp
  have hle : Y ≤ B^(1-δ)*Y^δ := by
    conv_lhs => rw [heq]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hY.le hYB (by linarith [hδ.2])) (by positivity)
  linarith

/-- The actual conductor, Poisson and puncture scales put the dual source
inside BOTH unequal pivot radii. The condition R≤GH is retained here. -/
theorem sharedDualScale_le_pivots (U V X G H J E F R : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hX : U*V^2 ≤ X)
    (hG : 1 ≤ G) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hE : 1 ≤ E) (hF : 1 ≤ F)
    (hR : 1 ≤ R) (hpuncture : R ≤ G*H) :
    sharedDualScale U V X G H J E F R ≤ U/(G*E) ∧
      sharedDualScale U V X G H J E F R ≤ U/(G*F) := by
  have hXp : 0 < X := (by positivity : 0 < U*V^2).trans_le hX
  have hGp : 0 < G := by linarith
  have hHp : 0 < H := by linarith
  have hJp : 0 < J := by linarith
  have hEp : 0 < E := by linarith
  have hFp : 0 < F := by linarith
  have hRp : 0 < R := by linarith
  have hscale : U*V^2/X ≤ 1 := (div_le_one hXp).2 hX
  have hthird (D : ℝ) (hD : 1 ≤ D) : R/(G*H^2*J*D) ≤ 1 := by
    have hHD : 1 ≤ H*J*D := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hH hJ) hD
    have hm : G*H ≤ G*H*(H*J*D) := le_mul_of_one_le_right (by positivity) hHD
    have hR' : R ≤ G*H^2*J*D := hpuncture.trans (hm.trans_eq (by ring))
    have hDp : 0 < D := by linarith
    exact (div_le_one (by positivity)).2 hR'
  have hbound (D : ℝ) (hD : 1 ≤ D) : (U*V^2/X)*(R/(G*H^2*J*D)) ≤ 1 :=
    (mul_le_mul hscale (hthird D hD) (by positivity) zero_le_one).trans_eq (one_mul 1)
  constructor
  · have heq : sharedDualScale U V X G H J E F R/(U/(G*E)) =
        (U*V^2/X)*(R/(G*H^2*J*F)) := by
      unfold sharedDualScale
      field_simp
      <;> ring
    apply (div_le_one (by positivity : 0 < U/(G*E))).mp
    rw [heq]
    exact hbound F hF
  · have heq : sharedDualScale U V X G H J E F R/(U/(G*F)) =
        (U*V^2/X)*(R/(G*H^2*J*E)) := by
      unfold sharedDualScale
      field_simp
      <;> ring
    apply (div_le_one (by positivity : 0 < U/(G*F))).mp
    rw [heq]
    exact hbound E hE

end
end Qrh.JointDetector.FiveColourNorm

#print axioms Qrh.JointDetector.FiveColourNorm.pivotPhase_cross_mask
#print axioms Qrh.JointDetector.FiveColourNorm.expandedSwap_le

#print axioms Qrh.JointDetector.FiveColourNorm.coprimeSwap_eq_expanded
#print axioms Qrh.JointDetector.FiveColourNorm.fiveColour_pivot_swap_le

#print axioms Qrh.JointDetector.FiveColourNorm.sharedTable_pairwise_disjoint
#print axioms Qrh.JointDetector.FiveColourNorm.sharedTable_card

#print axioms Qrh.JointDetector.FiveColourNorm.sharedTable_of_disjoint_supports
#print axioms Qrh.JointDetector.FiveColourNorm.sharedSwapCost_le

#print axioms Qrh.JointDetector.FiveColourNorm.sharedDualScale_le_pivots
