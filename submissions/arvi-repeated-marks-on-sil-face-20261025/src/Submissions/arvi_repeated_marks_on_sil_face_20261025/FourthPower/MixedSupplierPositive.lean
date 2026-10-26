/- Copyright (c) 2026 Sil. Apache-2.0.
Positive reduction of the actual frozen supplier family. 
The selected scalar and all frozen factors remain literal.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierFourthRow
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceConvolution
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationLocal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.CorrespondencePullback

set_option autoImplicit false
namespace Candidate.FourthPower.MixedSupplierPositive
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss RayFourExpansion CenteredMomentFixedRay CenteredMomentFirstColumns
open CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentLiveDomain
open ConcretePrimeRowBridge ActualEisensteinCubic CubicEisenstein
open ProbePhysical ProbePrimePower CenteredMomentAmplification CenteredMomentAmplificationLocal
open CenteredMomentUnequal CenteredMomentSupportedCorrelation
open MixedCommonRestriction MixedSupplierPartition MixedSupplierSplit
open MixedSupplierReconstruction MixedSupplierKernel MixedSupplierFourthRow
open MixedSelectedCommon (primary_supported)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

/-- Normalized prime Gauss sums include every frequency, including zero
and frequencies divisible by the prime. The latter vanish exactly. -/
theorem prime_gauss_norm_le_one (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (k : O) : ‖gaussRow p hs k‖≤1 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  obtain ⟨hg,hc⟩ := supported_prime_data p hp hs
  have hχ : actualSextic (Ideal.span {p}) hg≠1 := by
    intro he
    have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have hraw : ‖sexticGauss p (supportedElement_ne_zero p hs) k‖^2≤
      (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    by_cases hk : p∣k
    · have hz := primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero
        (actualSextic (Ideal.span {p}) hg) hχ 0 k hk
      simp only [pow_zero,one_mul] at hz
      have he := sexticGauss_prime_power p hp hg 0 k
      simp only [zero_add,pow_one] at he
      rw [he,hz,norm_zero,zero_pow (by decide : 2≠0)]
      exact Nat.cast_nonneg _
    · have hu := gauss_unit_scale_norm p hs k 1
        (hp.irreducible.coprime_iff_not_dvd.mpr hk).symm
      have he := gauss_prime_power_one p hp hg hc 0
      simp only [zero_add,pow_one,ite_true] at he
      have hnorm : ‖sexticGauss p (supportedElement_ne_zero p hs) k‖=
          ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1‖ := by
        simpa only [mul_one,he] using hu
      rw [hnorm,primeGauss_actual_norm_sq p hp hg hc]
  have hN : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have hn : ‖gaussRow p hs k‖^2≤1 := by
    rw [gaussRow,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
      div_pow,Real.sq_sqrt hN.le]
    exact (div_le_one hN).mpr hraw
  nlinarith [norm_nonneg (gaussRow p hs k)]

theorem primary_prime_gauss_norm (P : Id) (hP : Prime P) (k : O) :
    ‖primaryGaussRow P k‖≤1 := by
  by_cases hs : Supported P
  · have hp : Prime (primaryGenerator P) :=
      (Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero P hs)).mp (by
        rw [primary_span_supported P hs]
        exact Ideal.isPrime_of_prime hP)
    rw [primary_supported_eq P hs]
    exact prime_gauss_norm_le_one _ hp (primary_supported P hs) k
  · simp only [primaryGaussRow,dif_neg hs,norm_zero,zero_le_one]

theorem normalized_gauss_coprime_product (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : IsCoprime a b) (k : O) :
    gaussRow (a*b) (supported_mul_elements a b ha hb) k =
      idealRowHom b (Ideal.span {a})*idealRowHom a (Ideal.span {b})*
        gaussRow a ha k*gaussRow b hb k := by
  unfold gaussRow
  rw [sexticGauss_coprime_product a b ha hb hcop k,
    ←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _),Complex.ofReal_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem primary_gauss_coprime_bound (I J : Id) (hc : IsCoprime I J) (k : O)
    (hI : ‖primaryGaussRow I k‖≤1) (hJ : ‖primaryGaussRow J k‖≤1) :
    ‖primaryGaussRow (I*J) k‖≤1 := by
  by_cases hs : Supported (I*J)
  · obtain ⟨hsI,hsJ⟩ := (supported_mul_iff _ _).mp hs
    have hcop : IsCoprime (primaryGenerator I) (primaryGenerator J) := by
      rw [←Ideal.isCoprime_span_singleton_iff,primary_span_supported I hsI,
        primary_span_supported J hsJ]
      exact hc
    have he : primaryGaussRow (I*J) k=
        idealRowHom (primaryGenerator J) I*idealRowHom (primaryGenerator I) J*
          primaryGaussRow I k*primaryGaussRow J k := by
      rw [primary_supported_eq _ hs,primary_supported_eq _ hsI,primary_supported_eq _ hsJ]
      simpa only [MixedSelectedCommon.idealGauss,primaryGenerator_mul,
        primary_span_supported I hsI,primary_span_supported J hsJ] using
        normalized_gauss_coprime_product (primaryGenerator I) (primaryGenerator J)
          (primary_supported I hsI) (primary_supported J hsJ) hcop k
    rw [he,norm_mul,norm_mul,norm_mul]
    exact (mul_le_mul
      (mul_le_mul ((mul_le_mul (idealRowHom_norm _ _) (idealRowHom_norm _ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) hI
        (norm_nonneg _) zero_le_one)
      hJ (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp only [primaryGaussRow,dif_neg hs,norm_zero,zero_le_one]

/-- Injectivity is the exact squarefree input. Unsupported prime factors
are harmless only because the whole primary Gauss row is then zero. -/
theorem prime_product_gauss_norm {ι : Type*} (P : ι→Id)
    (hP : ∀i,Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) (k : O) :
    ‖primaryGaussRow (∏i∈S,P i) k‖≤1 := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty,primaryGaussRow,
        dif_pos CenteredMomentAddedZero.supported_one_ideal,primaryGenerator_one,
        gaussRow,sexticGauss_one,Ideal.span_singleton_one,←Ideal.one_eq_top,
        map_one,Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,div_one,norm_one,le_refl]
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      have hc : IsCoprime (P i) (∏j∈S,P j) := by
        apply IsCoprime.prod_right
        intro j hj
        apply (prime_coprime ⟨P i,hP i⟩ (P j)).mpr
        intro hd
        have heij := hinj ((prime_dvd_prime_iff_eq (hP i) (hP j)).mp hd)
        exact hi (by simpa only [heij] using hj)
      exact primary_gauss_coprime_bound _ _ hc k (primary_prime_gauss_norm _ (hP i) k) ih

/-- No remaining modulus or coprimality hypothesis on k. -/
theorem selected_scalar_norm (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (y : Selected q) (hy : Function.Injective y) (τ : Character) (t : ℝ)
    (k : O) (χ : RayCharacter) :
    ‖selectedScalar q x y τ t k χ‖≤‖selectedWeight q y‖ := by
  by_cases hg : selectedGate q.R (frozenProduct q x) (selectedProduct q y)
  · by_cases hs : Supported (frozenProduct q x*selectedProduct q y)
    · have hf : ‖primaryGaussRow (frozenProduct q x) k‖≤1 :=
        prime_product_gauss_norm (fun i : ↥(q.Lᶜ)=>(x i).val)
          (fun i=>alphabet_prime q.pool q.prime (x i))
          (fun i j he=>hx (Subtype.ext he)) Finset.univ k
      have hD : ‖primaryGaussRow (selectedProduct q y) k‖≤1 :=
        prime_product_gauss_norm (fun j : q.J=>(y j).val)
          (fun j=>alphabet_prime q.pool q.prime (y j))
          (fun i j he=>hy (Subtype.ext he)) Finset.univ k
      have hgN := primary_gauss_coprime_bound _ _ hg.1 k hf hD
      have hh := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ t _ hs.1
      have hr : ‖rayCharacter χ (primaryGenerator (frozenProduct q x*selectedProduct q y))‖≤1 :=
        FiniteRayExpansion.norm_char_le_one χ _
      simp only [selectedScalar,hg,ite_true,one_mul,norm_mul]
      exact (mul_le_of_le_one_right (by positivity) hgN).trans
        ((mul_le_of_le_one_right (by positivity) hr).trans
          (mul_le_of_le_one_right (norm_nonneg _) hh))
    · simp only [selectedScalar,primaryGaussRow,dif_neg hs,mul_zero,norm_zero,norm_nonneg]
  · simp only [selectedScalar,hg,ite_false,zero_mul,norm_zero,norm_nonneg]

/-- Only assignments with a genuinely nonzero original slot product.
No support or coprimality restriction is removed from inside a norm. -/
def activeSelected (q : Data α) : Finset (Selected q) :=
  Finset.univ.filter (fun y=>Function.Injective y ∧ selectedWeight q y≠0)

theorem active_selected_mem (q : Data α) (y : Selected q)
    (hy : y∈activeSelected q) (j : q.J) : (y j).val∈q.pool j.val.val := by
  have hw := (Finset.mem_filter.mp hy).2.2
  have hj := (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
  by_contra hn
  exact hj (by simp only [amplitude,slotAmplitude,if_neg hn])

/-- The Cauchy cardinality is bounded by the actual slot pools, not by
the much larger common marked alphabet used to write finite identities. -/
theorem active_selected_card (q : Data α) :
    (activeSelected q).card≤∏j : q.J,(q.pool j.val.val).card := by
  let e : activeSelected q→(j : q.J)→q.pool j.val.val := fun y j=>
    ⟨(y.val j).val,active_selected_mem q y.val y.property j⟩
  have he : Function.Injective e := by
    intro y z h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact congrArg (fun v : q.pool j.val.val=>(v:Id)) (congrFun h j)
  simpa only [Fintype.card_coe,Fintype.card_pi] using Fintype.card_le_of_injective e he

/-- Unsupported selected products have exactly zero original scalar.
This supplies the support required by PositiveFamily without changing
the common vector or deleting a coefficient from inside a nonzero norm. -/
theorem scalar_supported (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (t : ℝ) (k : O) (χ : RayCharacter)
    (hs : selectedScalar q x y τ t k χ≠0) :
    Supported (frozenProduct q x) ∧ Supported (selectedProduct q y) := by
  have hfd : Supported (frozenProduct q x*selectedProduct q y) := by
    by_contra hn
    exact hs (by simp only [selectedScalar,primaryGaussRow,dif_neg hn,mul_zero])
  exact (supported_mul_iff _ _).mp hfd

/-- The product window comes from the literal nonzero original amplitudes.
The lower and upper slot endpoints are explicit; no dyadic assertion is
silently inferred merely from the marked universe. -/
theorem selected_product_window (q : Data α) (y : Selected q)
    (hy : y∈activeSelected q) (lo hi : α→ℝ) (hlo : ∀i,0≤lo i)
    (hpool : ∀i,∀I∈q.pool i,lo i≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤hi i) :
    (∏j : q.J,lo j.val.val)≤(Ideal.absNorm (selectedProduct q y):ℝ) ∧
      (Ideal.absNorm (selectedProduct q y):ℝ)≤∏j : q.J,hi j.val.val := by
  simp only [selectedProduct,map_prod,Nat.cast_prod]
  constructor
  · exact Finset.prod_le_prod₀ (fun j _=>hlo j.val.val)
      (fun j _=>(hpool j.val.val (y j).val (active_selected_mem q y hy j)).1)
  · exact Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _)
      (fun j _=>(hpool j.val.val (y j).val (active_selected_mem q y hy j)).2)

theorem selected_product_upper (q : Data α) (y : Selected q)
    (hy : y∈activeSelected q) (hi : α→ℝ)
    (hpool : ∀i,∀I∈q.pool i,(Ideal.absNorm I:ℝ)≤hi i) :
    (Ideal.absNorm (selectedProduct q y):ℝ)≤∏j : q.J,hi j.val.val := by
  simp only [selectedProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _)
    (fun j _=>hpool j.val.val (y j).val (active_selected_mem q y hy j))

theorem selected_product_annular_upper (q : Data α) (y : Selected q)
    (hy : y∈activeSelected q)
    (hpool : ∀i,∀I∈q.pool i,(Ideal.absNorm I:ℝ)≤2*q.P i) :
    (Ideal.absNorm (selectedProduct q y):ℝ)≤
      2^(Fintype.card q.J)*∏j : q.J,q.P j.val.val := by
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] using
    selected_product_upper q y hy (fun i=>2*q.P i) hpool

/-- Counts the actual original pools by the baseline ideal lattice bound.
No positive lower slot width or prime-counting asymptotic is required. -/
theorem active_selected_annular_card (q : Data α) (hP : ∀i,0≤q.P i)
    (hpool : ∀i,∀I∈q.pool i,(Ideal.absNorm I:ℝ)≤2*q.P i) :
    ((activeSelected q).card:ℝ)≤256^(Fintype.card q.J)*∏j : q.J,q.P j.val.val := by
  have hcount (i : α) : ((q.pool i).card:ℝ)≤256*q.P i := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count (q.pool i) (2*q.P i)
      (mul_nonneg (by norm_num) (hP i)) (fun I hI=>(q.prime i I hI).ne_zero) (hpool i)
    convert hh using 1 <;> ring
  calc
    _ ≤ ∏j : q.J,((q.pool j.val.val).card:ℝ) := by
      exact_mod_cast active_selected_card q
    _ ≤ ∏j : q.J,256*q.P j.val.val :=
      Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hcount j.val.val)
    _ = _ := by rw [Finset.prod_mul_distrib];simp only [Finset.prod_const,Finset.card_univ]

/-- This is the exact selected-volume normalization of the Cauchy cost.
The later D-average still has its separate genuine 1/W. -/
theorem normalized_selected_card (q : Data α) (hP : ∀i,0<q.P i)
    (hpool : ∀i,∀I∈q.pool i,(Ideal.absNorm I:ℝ)≤2*q.P i) :
    ((activeSelected q).card:ℝ)/(∏j : q.J,q.P j.val.val)≤256^(Fintype.card q.J) := by
  apply (div_le_iff₀ (Finset.prod_pos (fun j _=>hP j.val.val))).mpr
  exact active_selected_annular_card q (fun i=>(hP i).le) hpool

/-- Fifth-freeness is supplied by the actual source masks, never assumed
for a newly chosen common vector. The fixed supplier character stays in it. -/
theorem common_vector_fifth_free (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (ξ : RayCharacter) (v : keptResidual q)
    (hv : commonVector q x seed τ t ξ v≠0) :
    GaussTransfer.FifthFree (primaryGenerator (residualColumn q v.val)) := by
  apply KernelWholeColumns.element_fifth_free
  rw [primary_span_supported _ (kept_supported q v)]
  apply base_fifth_free q x seed v
  intro hz
  exact hv (by simp only [commonVector,fixedCommonCoefficient,hz,zero_mul])

def commonPolynomial (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (ξ : RayCharacter) : O→ℂ :=
  gaussPolynomial Finset.univ
    (fun v : keptResidual q=>primaryGenerator (residualColumn q v.val))
    (fun v=>primary_supported _ (kept_supported q v)) (commonVector q x seed τ t ξ)

def raySum (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) (χ ξ : RayCharacter) : ℂ :=
  ∑y∈activeSelected q,selectedScalar q x y τ t k χ*
    commonPolynomial q x seed τ t ξ ((primaryGenerator (selectedProduct q y))^4*k)

/-- Exact positive summand; no Gauss norm estimate has yet been charged. -/
def rayBudget (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) (χ ξ : RayCharacter) : ℝ :=
  ∑y∈activeSelected q,‖selectedScalar q x y τ t k χ‖^2*
    ‖commonPolynomial q x seed τ t ξ ((primaryGenerator (selectedProduct q y))^4*k)‖^2

theorem fourth_family_active (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) :
    fourthFamily q x seed τ t k =
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
        raySum q x seed τ t k χ ξ := by
  unfold fourthFamily raySum commonPolynomial activeSelected
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hi : Function.Injective y
  · by_cases hw : selectedWeight q y=0
    · simp only [hi,hw,ne_eq,not_true_eq_false,and_false,ite_false,ite_true,
        selectedScalar,mul_zero,zero_mul]
    · simp only [hi,hw,ne_eq,not_false_eq_true,and_self,ite_true]
  · simp only [hi,false_and,ite_false]

theorem ray_budget_nonneg (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) (χ ξ : RayCharacter) :
    0≤rayBudget q x seed τ t k χ ξ := by
  unfold rayBudget
  exact Finset.sum_nonneg (fun _ _=>mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem ray_sum_sq (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) (χ ξ : RayCharacter) :
    ‖raySum q x seed τ t k χ ξ‖^2 ≤
      ((activeSelected q).card:ℝ)*rayBudget q x seed τ t k χ ξ := by
  simpa only [raySum,rayBudget,norm_mul,mul_pow] using
    CubicEisenstein.norm_sum_sq_le_card (activeSelected q)
      (fun y=>selectedScalar q x y τ t k χ*
        commonPolynomial q x seed τ t ξ ((primaryGenerator (selectedProduct q y))^4*k))

/-- Weighted Cauchy charges the actual finite ray mass once, not its square. -/
theorem first_ray_sq (F : RayCharacter→RayCharacter→ℂ) :
    ‖∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*F χ ξ‖^2 ≤
      256*∑χ : RayCharacter,∑ξ : RayCharacter,
        ‖pairCoeff firstPhaseTable χ ξ‖*‖F χ ξ‖^2 := by
  have hc := DescentWeightedCauchy.weighted_cauchy_sq Finset.univ
    (fun p : RayCharacter×RayCharacter=>pairCoeff firstPhaseTable p.1 p.2)
    (fun p=>F p.1 p.2) (fun _=>(1:ℂ))
  simp only [star_one,mul_one,norm_one,one_pow,Fintype.sum_prod_type] at hc
  have hn : 0≤∑χ : RayCharacter,∑ξ : RayCharacter,
      ‖pairCoeff firstPhaseTable χ ξ‖*‖F χ ξ‖^2 := by
    exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg
      (fun _ _=>mul_nonneg (norm_nonneg _) (sq_nonneg _)))
  exact hc.trans ((mul_le_mul_of_nonneg_left firstPhaseTable_mass hn).trans_eq
    (mul_comm _ _))

/-- The entire literal family has a positive bound, with the original
selected Gauss/height/ray prefactors still visible in rayBudget. -/
theorem fourth_family_sq (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) :
    ‖fourthFamily q x seed τ t k‖^2 ≤
      256*((activeSelected q).card:ℝ)*
        ∑χ : RayCharacter,∑ξ : RayCharacter,
          ‖pairCoeff firstPhaseTable χ ξ‖*rayBudget q x seed τ t k χ ξ := by
  rw [fourth_family_active]
  calc
    _ ≤ 256*∑χ : RayCharacter,∑ξ : RayCharacter,
        ‖pairCoeff firstPhaseTable χ ξ‖*‖raySum q x seed τ t k χ ξ‖^2 :=
      first_ray_sq _
    _ ≤ 256*∑χ : RayCharacter,∑ξ : RayCharacter,
        ‖pairCoeff firstPhaseTable χ ξ‖*
          (((activeSelected q).card:ℝ)*rayBudget q x seed τ t k χ ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro χ hχ
      apply Finset.sum_le_sum
      intro ξ hξ
      exact mul_le_mul_of_nonneg_left (ray_sum_sq q x seed τ t k χ ξ) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      ring

/-- A concrete consequence for the ORIGINAL weighted supplier branch.
There is no factorization, fifth-free or source-energy hypothesis. -/
theorem weighted_original_family_sq (q : Data α) (x : Frozen q)
    (hx : Function.Injective x) (τ : Character) (t : ℝ) (k : O) :
    ∃seed : Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ‖frozenWeight q x*originalFamily q x τ t k‖^2 ≤
        ‖frozenWeight q x‖^2 * (256*((activeSelected q).card:ℝ)*
          ∑χ : RayCharacter,∑ξ : RayCharacter,
            ‖pairCoeff firstPhaseTable χ ξ‖*rayBudget q x seed τ t k χ ξ) := by
  obtain ⟨seed,hs,he⟩ := weighted_family_fourth q x hx τ t k
  refine ⟨seed,hs,?_⟩
  rw [he,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_left (fourth_family_sq q x seed τ t k) (sq_nonneg _)

/-- The additional filter removes only whole zero scalar summands. -/
def supportedSelected (q : Data α) : Finset (Selected q) :=
  (activeSelected q).filter (fun y=>Supported (selectedProduct q y))

def selectedProducts (q : Data α) : Finset Id :=
  (supportedSelected q).image (selectedProduct q)

def selectedFiber (q : Data α) (D : Id) : Finset (Selected q) :=
  (supportedSelected q).filter (fun y=>selectedProduct q y=D)

/-- The true positive weight from original amplitudes, independent of k
and the residual columns. No artificial replacement sequence occurs. -/
def groupedWeight (q : Data α) (D : Id) : ℝ :=
  ∑y∈selectedFiber q D,‖selectedWeight q y‖^2

theorem selected_products_supported (q : Data α) (D : Id) (hD : D∈selectedProducts q) :
    Supported D := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hD
  exact (Finset.mem_filter.mp hy).2

theorem grouped_weight_nonneg (q : Data α) (D : Id) : 0≤groupedWeight q D :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

theorem selected_grouping (q : Data α) (F : Id→ℝ) :
    (∑y∈supportedSelected q,‖selectedWeight q y‖^2*F (selectedProduct q y))=
      ∑D∈selectedProducts q,groupedWeight q D*F D := by
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun y hy=>Finset.mem_image.mpr ⟨y,hy,rfl⟩ :
      ∀y∈supportedSelected q,selectedProduct q y∈selectedProducts q)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [groupedWeight,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [(Finset.mem_filter.mp hy).2]

theorem ray_budget_grouped (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (seed : Id) (τ : Character) (t : ℝ) (k : O) (χ ξ : RayCharacter) :
    rayBudget q x seed τ t k χ ξ ≤
      ∑D∈selectedProducts q,groupedWeight q D*
        ‖commonPolynomial q x seed τ t ξ ((primaryGenerator D)^4*k)‖^2 := by
  rw [←selected_grouping]
  unfold rayBudget supportedSelected
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro y hy
  by_cases hs : Supported (selectedProduct q y)
  · rw [if_pos hs]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _)
        (selected_scalar_norm q x hx y (Finset.mem_filter.mp hy).2.1 τ t k χ) 2)
      (sq_nonneg _)
  · have hz : selectedScalar q x y τ t k χ=0 := by
      by_contra hn
      exact hs (scalar_supported q x y τ t k χ hn).2
    simp only [hs,ite_false,hz,norm_zero,zero_pow (by decide : 2≠0),zero_mul,le_refl]

theorem amplitude_norm (q : Data α) (M : α→ℝ) (hM : ∀i,0≤M i)
    (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1) (hW : ∀i z,‖q.Wslot i z‖≤M i)
    (i : α) (p : Alphabet q) : ‖amplitude q i p‖≤M i := by
  unfold amplitude slotAmplitude
  by_cases hp : p.val∈q.pool i
  · rw [if_pos hp,norm_mul]
    have hcoeff : ‖supplierCharacters q.u q.L q.ν i p.val‖≤1 := by
      unfold supplierCharacters KernelHoleCompletion.mixed KernelHoleCompletion.good KernelHoleCompletion.bad
      split_ifs <;> first | exact hν i p.val hp |
        simpa only [norm_zero] using (zero_le_one : (0:ℝ)≤1)
    exact (mul_le_mul hcoeff (hW i _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simpa only [hp,ite_false,norm_zero] using hM i

theorem selected_weight_norm (q : Data α) (M : α→ℝ) (hM : ∀i,0≤M i)
    (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1) (hW : ∀i z,‖q.Wslot i z‖≤M i)
    (y : Selected q) : ‖selectedWeight q y‖≤∏j : q.J,M j.val.val := by
  rw [selectedWeight,norm_prod]
  exact Finset.prod_le_prod₀ (fun j _=>norm_nonneg _)
    (fun j _=>amplitude_norm q M hM hν hW j.val.val (y j))

/-- Literal product fibers have bounded divisor multiplicity. -/
theorem selected_fiber_card (q : Data α) (D : Id) (hD : D≠0) :
    (selectedFiber q D).card≤
      (IdealMobiusDivisorSum.idealDivisors D).card^(Fintype.card q.J) := by
  let e (y : selectedFiber q D) : q.J→IdealMobiusDivisorSum.idealDivisors D := fun j=>
    ⟨(y.val j).val,by
      apply (IdealMobiusDivisorSum.mem_idealDivisors hD).mpr
      have he : selectedProduct q y.val=D := (Finset.mem_filter.mp y.property).2
      exact (congrArg (fun I : Id=>(y.val j).val∣I) he).mp
        (Finset.dvd_prod_of_mem (fun j : q.J=>(y.val j).val) (Finset.mem_univ j))⟩
  have he : Function.Injective e := by
    intro y z h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact congrArg (fun v : IdealMobiusDivisorSum.idealDivisors D=>(v:Id)) (congrFun h j)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective e he

/-- Uniform in the pools and the selected subset; the constant is chosen
using the original finite slot type, before q and before D. -/
theorem selected_fiber_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(q : Data α)(D : Id),D≠0→
      ((selectedFiber q D).card:ℝ)≤C*(Ideal.absNorm D:ℝ)^δ := by
  let n : ℕ := Fintype.card α
  let ε := δ/((n:ℝ)+1)
  have hε : 0<ε := by dsimp only [ε];positivity
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨(1+C)^n,pow_pos (by linarith) _,?_⟩
  intro q D hD
  have hN : 1≤(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hpow : 1≤(Ideal.absNorm D:ℝ)^ε := Real.one_le_rpow hN hε.le
  have hcount : Fintype.card q.J≤n := Fintype.card_le_of_injective
    (fun j : q.J=>j.val.val)
    (fun i j he=>Subtype.ext (Subtype.ext he))
  have hb : 1≤(1+C)*(Ideal.absNorm D:ℝ)^ε := by nlinarith
  have hexp : ε*(n:ℝ)≤δ := by
    have he : ε*((n:ℝ)+1)=δ := by dsimp only [ε];field_simp
    nlinarith
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors D).card:ℝ)^(Fintype.card q.J) := by
      exact_mod_cast selected_fiber_card q D hD
    _ ≤ ((1+C)*(Ideal.absNorm D:ℝ)^ε)^(Fintype.card q.J) := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact (hdiv D hD).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ ≤ ((1+C)*(Ideal.absNorm D:ℝ)^ε)^n := pow_le_pow_right₀ hb hcount
    _ = (1+C)^n*(Ideal.absNorm D:ℝ)^(ε*(n:ℝ)) := by
      rw [mul_pow,←Real.rpow_natCast ((Ideal.absNorm D:ℝ)^ε) n,
        ←Real.rpow_mul (zero_le_one.trans hN)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN hexp) (by positivity)

theorem grouped_weight_bound (q : Data α) (M : α→ℝ) (hM : ∀i,0≤M i)
    (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1) (hW : ∀i z,‖q.Wslot i z‖≤M i) (D : Id) :
    groupedWeight q D≤((selectedFiber q D).card:ℝ)*(∏j : q.J,M j.val.val)^2 := by
  unfold groupedWeight
  calc
    _ ≤ ∑y∈selectedFiber q D,(∏j : q.J,M j.val.val)^2 :=
      Finset.sum_le_sum (fun y _=>pow_le_pow_left₀ (norm_nonneg _)
        (selected_weight_norm q M hM hν hW y) 2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

/-- The actual grouped positive D-average goes through the checked sparse
theorem. Constants precede q, profiles, frequencies, and Hecke heights.
The width cap is the literal product of slot upper endpoints, so choosing
hi=2P retains the factor 2^#J explicitly. -/
theorem actual_grouped_average (ε δ : ℝ) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(q : Data α)(x : Frozen q)(seed : Id)(τ : Character)(t : ℝ)
      (ξ : RayCharacter)(Ks : Finset O)(W K : ℝ)(hi M : α→ℝ),
    0<W → (∀k∈Ks,k≠0) →
    (∀k∈Ks,(Ideal.absNorm (Ideal.span {k}):ℝ)≤K) →
    (∀i,∀I∈q.pool i,(Ideal.absNorm I:ℝ)≤hi i) →
    (∏j : q.J,hi j.val.val)≤2*W →
    (∀i,0≤M i) → (∀i,∀I∈q.pool i,‖q.ν i I‖≤1) →
    (∀i z,‖q.Wslot i z‖≤M i) →
    (∑D∈selectedProducts q,groupedWeight q D*
      ∑k∈Ks,‖commonPolynomial q x seed τ t ξ ((primaryGenerator D)^4*k)‖^2)/W ≤
      ((∏j : q.J,M j.val.val)^2*C*(2*W)^δ*(16*K*W^4)^ε/W)*
        ∑r∈(selectedProducts q×ˢKs).image PositiveFamily.frequency,
          ‖commonPolynomial q x seed τ t ξ r‖^2 := by
  obtain ⟨Cf,hCf,hfiber⟩ := selected_fiber_subpower (α:=α) δ hδ
  obtain ⟨Cp,hCp,hpush⟩ := MixedPhysicalTransfer.sparse_weighted_average ε hε
  refine ⟨Cf*Cp,mul_pos hCf hCp,?_⟩
  intro q x seed τ t ξ Ks W K hi M hW hk hkN hpool hprod hM hν hWM
  have hDN (D : Id) (hD : D∈selectedProducts q) : (Ideal.absNorm D:ℝ)≤2*W := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hD
    exact (selected_product_upper q y (Finset.mem_filter.mp hy).1 hi hpool).trans hprod
  let L : ℝ := (∏j : q.J,M j.val.val)^2*Cf*(2*W)^δ
  have hL : 0≤L := by dsimp only [L];positivity
  have hw (D : Id) (hD : D∈selectedProducts q) : 0≤groupedWeight q D ∧ groupedWeight q D≤L := by
    refine ⟨grouped_weight_nonneg q D,?_⟩
    have hc := hfiber q D (selected_products_supported q D hD).1
    have hh := grouped_weight_bound q M hM hν hWM D
    calc
      _ ≤ ((selectedFiber q D).card:ℝ)*(∏j : q.J,M j.val.val)^2 := hh
      _ ≤ (Cf*(Ideal.absNorm D:ℝ)^δ)*(∏j : q.J,M j.val.val)^2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ ≤ (Cf*(2*W)^δ)*(∏j : q.J,M j.val.val)^2 := by
        gcongr
        exact hDN D hD
      _ = L := by dsimp only [L];ring
  let a := fun v : keptResidual q=>primaryGenerator (residualColumn q v.val)
  let ha := fun v : keptResidual q=>primary_supported _ (kept_supported q v)
  let β := commonVector q x seed τ t ξ
  have hf : ∀v∈(Finset.univ : Finset (keptResidual q)),β v≠0→GaussTransfer.FifthFree (a v) :=
    fun v _ hv=>common_vector_fifth_free q x seed τ t ξ v hv
  have hp := hpush (selectedProducts q) Ks (selected_products_supported q) hk
    (groupedWeight q) (fun _ _=>1) W K L hW hL hw
    (fun _ _ _ _=>⟨zero_le_one,le_refl _⟩) hDN hkN Finset.univ a ha β hf
  have he (D : Id) (k : O) :=
    MixedPhysicalTransfer.sparse_fourth_power Finset.univ a ha β hf (primaryGenerator D) k
  simp_rw [←he] at hp
  simp only [one_mul] at hp
  change (∑D∈selectedProducts q,groupedWeight q D*
    ∑k∈Ks,‖commonPolynomial q x seed τ t ξ ((primaryGenerator D)^4*k)‖^2)/W≤_ at hp
  exact hp.trans_eq (by dsimp only [L,a,ha,β,commonPolynomial];ring)

/-- The common residual seed is fixed before every height and every row,
not chosen separately for each frequency. Cancellation by nonzero f makes
the quotient obtained in FourthRow unique. -/
theorem uniform_weighted_family (q : Data α) (x : Frozen q) (hx : Function.Injective x) :
    ∃seed : Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ∀(τ : Character)(t : ℝ)(k : O),
        frozenWeight q x*originalFamily q x τ t k=
          frozenWeight q x*fourthFamily q x seed τ t k := by
  by_cases hw : frozenWeight q x=0
  · refine ⟨1,by simp only [hw,ne_eq,not_true_eq_false,false_implies],?_⟩
    intro τ t k
    simp only [hw,zero_mul]
  · obtain ⟨seed,hs⟩ := frozen_divides q x hx hw
    refine ⟨seed,fun _=>hs,?_⟩
    intro τ t k
    obtain ⟨s,hs',he⟩ := weighted_family_fourth q x hx τ t k
    have heq : s=seed := mul_left_cancel₀ (frozen_nonzero q x) ((hs' hw).symm.trans hs)
    simpa only [heq] using he

/-- Summed positive reduction of the actual original family. This is the
input for actual_grouped_average; the sole outside Cauchy factor is the
explicit selected cardinality, of size W in the analytic ledger. -/
theorem weighted_original_sum (q : Data α) (x : Frozen q) (hx : Function.Injective x) :
    ∃seed : Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ∀(τ : Character)(t : ℝ)(Ks : Finset O),
      (∑k∈Ks,‖frozenWeight q x*originalFamily q x τ t k‖^2)≤
        ‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
          ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
            ∑D∈selectedProducts q,groupedWeight q D*
              ∑k∈Ks,‖commonPolynomial q x seed τ t ξ ((primaryGenerator D)^4*k)‖^2) := by
  obtain ⟨seed,hs,he⟩ := uniform_weighted_family q x hx
  refine ⟨seed,hs,?_⟩
  intro τ t Ks
  have hpoint (k : O) :
      ‖frozenWeight q x*originalFamily q x τ t k‖^2≤
        ‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
          ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
            ∑D∈selectedProducts q,groupedWeight q D*
              ‖commonPolynomial q x seed τ t ξ ((primaryGenerator D)^4*k)‖^2) := by
    rw [he τ t k,norm_mul,mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply (fourth_family_sq q x seed τ t k).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro χ hχ
    apply Finset.sum_le_sum
    intro ξ hξ
    exact mul_le_mul_of_nonneg_left (ray_budget_grouped q x hx seed τ t k χ ξ)
      (norm_nonneg _)
  calc
    _ ≤ ∑k∈Ks,‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
        ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
          ∑D∈selectedProducts q,groupedWeight q D*
            ‖commonPolynomial q x seed τ t ξ ((primaryGenerator D)^4*k)‖^2) :=
      Finset.sum_le_sum (fun k _=>hpoint k)
    _ = _ := by
      simp only [←Finset.mul_sum]
      congr 2
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [←Finset.mul_sum,Finset.sum_comm]
      apply congrArg (fun z : ℝ=>‖pairCoeff firstPhaseTable χ ξ‖*z)
      apply Finset.sum_congr rfl
      intro D hD
      rw [Finset.mul_sum]

end
end Candidate.FourthPower.MixedSupplierPositive
