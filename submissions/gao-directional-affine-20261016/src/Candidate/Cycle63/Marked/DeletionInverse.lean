import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeletedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Filter Set HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseRawConjugateGates
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open ConcreteTraceCRT InverseMoment InverseInitialProfile InverseInitialRawDictionary
open InverseInitialConjugateEnergy InverseInitialMarkedDictionary
open InverseInitialPhysicalSlots InverseInitialExcludedPeriod InverseInitialPoissonBridge
open InverseInitialEnergyCallerWindow
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- A normalized slot with arbitrary complex prime coefficients. -/
def directPrimeSlot (u : O) (L : Finset (Ideal O)) (β : Ideal O → ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P : ℂ)⁻¹ * ∑ I ∈ L, β I * idealRowHom u I

theorem direct_prime_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : O) (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (U : ℝ) (hU : 0<U) (ell : ι → ℝ) :
    (∏i,directPrimeSlot u (L i) (β i) (U^(ell i))) =
      ((U^(-(∑i,ell i)/2) : ℝ) : ℂ) *
        ∑p ∈ Fintype.piFinset L, (∏i,β i (p i))*idealRowHom u (∏i,p i) := by
  have hnorm (w : ℝ) : (Real.sqrt (U^w) : ℂ)⁻¹ = ((U^(-w/2) : ℝ) : ℂ) := by
    rw [←Complex.ofReal_inv]
    congr 1
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hU.le,←Real.rpow_neg hU.le]
    congr 1
    ring
  simp only [directPrimeSlot,hnorm]
  rw [Finset.prod_mul_distrib,slot_normalization U hU,Finset.prod_univ_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.prod_mul_distrib,map_prod]

/-- The actual inverse polynomial times arbitrary normalized prime slots
has the same finite source as the analytic marked estimate. The detector
base and the coefficients in the slots are independent. -/
theorem deleted_direct_slots_initial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : RowData) (u : NonzeroElement) (L : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (ell : ι → ℝ) (W : ℝ → ℂ)
    (U r bo : ℝ) (hU : 0<U) (hW : ∀x,W x≠0 → x≤bo)
    (hne : ∀i,∀P∈L i,idealCoeff (deletedBase data) P≠0) :
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (U^r) 0 0 *
      (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i))) =
    ∑p : Tuple L, (∏i,β i (p i).val / idealCoeff (deletedBase data) (p i).val) *
      originalTotalPolynomial (originalSource U r bo) (∏i,(p i).val)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u.val := by
  let χ := (data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let η := (idealCoeff (deletedBase data)).toMonoidHom
  have hprod (p : ι → Ideal O) (hp : p∈Fintype.piFinset L) : η (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hne i (p i) (Fintype.mem_piFinset.mp hp i)
  have he := indexed_mark_initial (Fintype.piFinset L) (fun p=>∏i,p i)
    (fun p=>(∏i,β i (p i))/η (∏i,p i)) η χ u.val (actual_deleted_row data u)
    W U r (∑i,ell i) 0 0 hU (idealsUpTo ⌈U^r*bo⌉₊)
    (finite_source_cover W (U^r) bo (Real.rpow_pos_of_pos hU _) hW)
  have hs : (∑p∈Fintype.piFinset L, ((∏i,β i (p i))/η (∏i,p i))*idealCoeff χ (∏i,p i)) =
      ∑p∈Fintype.piFinset L, (∏i,β i (p i))*idealRowHom u.val (∏i,p i) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [actual_deleted_row data u]
    change _ / η (∏i,p i) * (η (∏i,p i)*_) = _
    rw [←mul_assoc,div_mul_cancel₀ _ (hprod p hp)]
  rw [hs] at he
  rw [direct_prime_product _ _ _ _ hU,←mul_assoc,he]
  rw [sum_tuple_original L (fun p=>(∏i,β i (p i)/idealCoeff (deletedBase data) (p i))*
    originalTotalPolynomial (originalSource U r bo) (∏i,p i) η (fun _=>1) W U r (∑i,ell i) u.val)]
  apply Finset.sum_congr rfl
  intro p hp
  have ht : twistedProfile W 0 0 = W := by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht,originalTotal_supported_source _ _ _ (deletedBase_zero_unsupported data)]
  simp only [η,map_prod,Finset.prod_div_distrib]
  rfl

theorem deleted_prime_gates (data : RowData) (P : Ideal O) (hP : Prime P)
    (hlarge : ((deletedBase data).modulus.absNorm : ℝ) < P.absNorm) :
    InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧ Supported P := by
  have hc := ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hP⟩ hlarge
  have hn := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hP.ne_zero hc
  have hne := HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hP.ne_zero hc
  refine ⟨?_,hne,hn,deletedBase_supported data P hne⟩
  by_contra hout
  exact hne (InverseInitialExcludedOverlap.deleted_zero_outside
    (InverseInitialDetectorSource.baseCharacter data) (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data)) P hout)

/-- The full inverse marked source estimate allows arbitrary bounded prime
coefficients. Its constants do not depend on slot characters or heights. -/
theorem deleted_direct_energy (W : ℝ → ℂ) (ao bo : ℝ) (hao : 0<ao)
    (hab : ao≤bo) (hsW : Function.support W⊆Icc ao bo) (hW : ContDiff ℝ ∞ W)
    (εm : ℝ) (hεm : 0<εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤1) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀j∈idealDivisors (∏P∈excluded data,P),
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) → ∀θ : ℝ,
      (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true (childLogTest W θ)
        (U^(shiftedExponent data U r j)) 0 0 *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩ := padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩ := raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩ := eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hdis hratio hβ hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0 : U₀≤U := (le_max_left _ _).trans hU
  have hUp : 0<U := zero_lt_one.trans (hU₀.trans_le hU0)
  have hjshift := (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  have hg (i : ι) (P : Ideal O) (hP : P∈L i) :=
    deleted_prime_gates data P (hp i P hP) ((hlarge i).trans_le
      (by simpa only [one_mul] using
        (le_div_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio i P hP).1))
  let coeff := fun i P => β i P / idealCoeff (deletedBase data) P
  have hc (i : ι) (P : Ideal O) (hP : P∈L i) : ‖coeff i P‖≤1 := by
    dsimp [coeff]
    rw [norm_div,(hg i P hP).2.2.1,div_one]
    exact hβ i P hP
  let marker : ℝ → ℂ := (Icc (1 : ℝ) 2).indicator (fun _=>1)
  have hm : Function.support marker⊆Icc (1 : ℝ) 2 := Set.support_indicator_subset
  have hlive (i : ι) (P : Ideal O) (hP : P∈L i) : marker ((P.absNorm : ℝ)/U^(ell i))≠0 := by
    simp [marker,hratio i P hP]
  let rawRows := rows.image (fun u=>u.val)
  have hrawRows (u : O) (hu : u∈rawRows) : ‖eisEmbedding u‖^2≤U := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact hrows v hv
  have he := henergy U hU0 hK L ell coeff hell hp
    (fun i P hP=>(hg i P hP).2.2.2) hdis hratio hc
    (fun i P hP=>by rw [hqset];exact (hg i P hP).1)
    (fun _=>marker) (fun _=>hm) hlive
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rawRows hrawRows θ
  rw [Finset.sum_image (fun u _ v _ he=>Subtype.ext he)] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [deleted_direct_slots_initial data u L β ell (childLogTest W θ) U
    (shiftedExponent data U r j) bo hUp
    (fun x hx=>(hsW (by intro hz;exact hx (by simp [childLogTest,hz]))).2)
    (fun i P hP=>(hg i P hP).2.1)]

/-- Fixed Euler deletions in the detector cost only a fixed constant.
The slot coefficients remain completely arbitrary throughout. -/
theorem direct_reference_energy (W : ℝ → ℂ) (ao bo : ℝ) (hao : 0<ao)
    (hab : ao≤bo) (hsW : Function.support W⊆Icc ao bo) (hW : ContDiff ℝ ∞ W)
    (εm : ℝ) (hεm : 0<εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤1) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) → ∀θ : ℝ,
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W θ) (U^r) 0 0 *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,henergy⟩ := deleted_direct_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  let divs := idealDivisors (∏P∈excluded data,P)
  refine ⟨((divs.card : ℝ)+1)^2*C,U₀,by positivity,hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hdis hratio hβ hlarge r hr hfirst hsecond rows hrows θ
  have hUone : 1<U := hU₀.trans_le hU
  have hUp : 0<U := zero_lt_one.trans hUone
  have hsupport : ∀x,childLogTest W θ x≠0 → x≤bo := by
    intro x hx
    exact (hsW (by intro hz;exact hx (by simp [childLogTest,hz]))).2
  let mark := fun u : NonzeroElement => ∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i))
  have hd := marked_fixed_deletion data rows (childLogTest W θ) (U^r) 0 0 bo
    (Real.rpow_pos_of_pos hUp _) hsupport mark
  have hjbound (j : Ideal O) (hj : j∈divs) :
      (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true (childLogTest W θ)
        (U^r/(j.absNorm : ℝ)) 0 0 * mark u‖^2) ≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
    have hscale : U^(shiftedExponent data U r j) = U^r/(j.absNorm : ℝ) := by
      rw [shiftedExponent,Real.rpow_sub hUp,Real.rpow_logb hUp hUone.ne'
        (zero_lt_one.trans_le (excluded_divisor_norm data j hj).1)]
    have he := henergy U hU hK L ell β hell hp hdis hratio hβ hlarge r hr
      hfirst hsecond j hj rows hrows θ
    rwa [hscale] at he
  apply hd.trans
  change (divs.card : ℝ) * (∑j∈divs,_) ≤ _
  calc
    _ ≤ (divs.card : ℝ) * ∑j∈divs,C*U^(1+εm)*((1+‖θ‖)^degree)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjbound) (by positivity)
    _ = (divs.card : ℝ)^2*C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr <;> linarith

/-- Actual marked inverse moments at every detector derivative and height,
for arbitrary bounded coefficients on separated prime pools. All analytic
inputs are supplied by the incumbent marked theorem. -/
theorem actual_inverse_marked_energy (εm : ℝ) (hεm : 0<εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤1) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨J,hreference⟩ := direct_reference_energy referenceWindow (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) (referenceWindow.smooth ⊤)
    εm hεm K
  obtain ⟨degree,Cfourier,hCf,hfourier⟩ := DetectorDictionaryInverseMarkedUniform.moving_finite_energy J
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,href⟩ := hreference data
  refine ⟨Cfourier*C,U₀,mul_pos hCf hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hdis hratio hβ hlarge r hr hfirst hsecond rows hrows
    tstar reverse n hn σ hσ height t hh ht
  have hUp : 0<U := zero_lt_one.trans (hU₀.trans_le hU)
  let mark := fun u : NonzeroElement => ∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i))
  have he (v : ℝ) :
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest referenceWindow v)
        (U^r) 0 0 * mark u‖^2) ≤ (C*U^(1+εm))*(1+‖v‖)^(2*J) := by
    convert href U hU hK L ell β hell hp hdis hratio hβ hlarge r hr hfirst hsecond rows hrows v using 1
    rw [show 2*J=J*2 by omega,pow_mul]
  have hb := hfourier rows data.character mark (U^r) (C*U^(1+εm))
    (Real.rpow_pos_of_pos hUp _) (by positivity) he false reverse n hn U hUp tstar r σ hσ t
  have hprofile : (inverseSourceSchwartz false reverse n U tstar r σ t : ℝ→ℂ) =
      HeckeInverseAmplification.twistProfile ((HeckeDetectorRowwisePolynomial.logProfile^[n])
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) σ t := by
    funext x
    simpa only [Bool.false_eq_true,ite_false,
      DetectorDictionaryInverseMarkedUniform.logTest_eq_iterate] using
      inverseSourceSchwartz_apply false reverse n U tstar r σ t x
  simp only [hprofile,HeckeInverseAmplification.polynomial_twistProfile] at hb
  apply hb.trans
  have ht' : ‖t‖≤height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  calc
    Cfourier*(C*U^(1+εm))*(1+‖t‖)^degree ≤
        Cfourier*(C*U^(1+εm))*(1+height)^degree := by gcongr
    _ = _ := by ring

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.deleted_direct_energy
#print axioms OAI.SevenEighths.Deletion26.actual_inverse_marked_energy
