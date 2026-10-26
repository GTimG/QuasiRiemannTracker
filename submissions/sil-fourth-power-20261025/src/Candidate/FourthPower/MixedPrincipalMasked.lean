/- Copyright (c) 2026 Sil. Apache-2.0.
The literal artificial divisibility mask after full-support extraction.
Its projector is collapsed exactly, retaining all frozen valuations.
-/
import Candidate.FourthPower.MixedPrincipalFrozen
import Candidate.FourthPower.MixedDivisorMask

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalMasked
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentLattice CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentAllocatedNaturalRadial
open MixedPrincipalCentered MixedPrincipalPositivePart MixedPrincipalFrozen
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedFixedSupport MixedAllocationSource MixedSourceAssembly MixedDivisorMask
open MixedLiveNormalization
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def maskedRow {ι : Type*} [Fintype ι]
    (χ : Character) (S H : Finset PrimeIdeal) (pool : ι→Finset Id)
    (d : Id×Id) (hd : d.1≠0∧d.2≠0) (D R : Id)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  normalization (X₁*X₂) P*
    ∑v∈Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂),
      if D∣finiteTupleProduct v then tupleWeight (punctureProduct S H) v*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
        idealCoeff χ (finiteTupleProduct v) else 0

theorem masked_row_allocated {ι : Type*} [Fintype ι]
    (χ : Character) (S H : Finset PrimeIdeal) (pool : ι→Finset Id)
    (d : Id×Id) (hd : d.1≠0∧d.2≠0) (D R : Id) (hD : Squarefree D)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    maskedRow χ S H pool d hd D R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      ∑a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
        allocatedRow χ S H pool d hd D R a ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold maskedRow allocatedRow
  rw [←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have he := squarefree_mask_allocation D hD (Finset.univ : Finset (ι⊕Fin 2)) v
  change (if D∣finiteTupleProduct v then (1:ℂ) else 0)=_ at he
  rw [show (∑a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
      tupleWeight (punctureProduct S H) v*allocationTerm D Finset.univ v a*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
        idealCoeff χ (finiteTupleProduct v))=
    tupleWeight (punctureProduct S H) v*
      (∑a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),allocationTerm D Finset.univ v a)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
      idealCoeff χ (finiteTupleProduct v) by simp only [Finset.mul_sum,Finset.sum_mul]]
  rw [←he]
  split_ifs <;> ring

/-- The complete artificial allocation sum is exactly one indicator on
each frozen tuple. In particular no allocation multiplicity is lost. -/
theorem masked_row_frozen {ι : Type*} [Fintype ι]
    (χ : Character) (S H : Finset PrimeIdeal) (pool : ι→Finset Id)
    (hp : ∀i,∀I∈pool i,Prime I) (d : Id×Id) (hd : d.1≠0∧d.2≠0)
    (D R : Id) (hD : Squarefree D)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    maskedRow χ S H pool d hd D R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      ∑B : boundedLabels (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) D,
        (if D∣finiteTupleProduct B.val then
          frozenWeight (punctureProduct S H) B.val*idealCoeff χ (finiteTupleProduct B.val) else 0)*
        frozenRow χ S H pool d hd B.val
          (allocation_data _ D B.val (Finset.mem_filter.mp B.property).1).1 D R
          ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  rw [masked_row_allocated χ S H pool d hd D R hD]
  simp_rw [allocated_row_identity χ S H pool hp d hd D D R hD.ne_zero (dvd_refl D)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  have he := squarefree_mask_allocation D hD (Finset.univ : Finset (ι⊕Fin 2)) B.val
  change (if D∣finiteTupleProduct B.val then (1:ℂ) else 0)=_ at he
  calc
    _ = (frozenWeight (punctureProduct S H) B.val*
        (∑a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),allocationTerm D Finset.univ B.val a)*
        idealCoeff χ (finiteTupleProduct B.val))*
        frozenRow χ S H pool d hd B.val
          (allocation_data _ D B.val (Finset.mem_filter.mp B.property).1).1 D R
          ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by simp only [Finset.mul_sum,Finset.sum_mul]
    _ = _ := by rw [←he];split_ifs <;> ring

/-- Dimension-uniform version of the already established fixed-support
label count. The constant precedes the actual live type and all pools. -/
theorem bounded_labels_uniform (N : ℕ) (hN : 0<N) (δ : ℝ) (hδ : 0<δ) :
    ∃K : ℝ,0<K ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N→
      ∀(S : ι→Finset Id)(D : Id),D≠0→
        ((boundedLabels S D).card:ℝ)≤K*(D.absNorm:ℝ)^δ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  let e := δ/(4*(N:ℝ))
  have he : 0<e := div_pos hδ (by positivity)
  obtain ⟨K,hK,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power e he
  let K' := max 1 K
  have hK' : 0<K' := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨K'^N,pow_pos hK' _,?_⟩
  intro ι _ hi S D hD
  have hd : 1≤(idealDivisors (D^4)).card := by
    exact Finset.one_le_card.mpr ⟨1,(mem_idealDivisors (pow_ne_zero 4 hD)).mpr (one_dvd _)⟩
  have hdR : (1:ℝ)≤(idealDivisors (D^4)).card := by exact_mod_cast hd
  have hbase : ((idealDivisors (D^4)).card:ℝ)≤K'*((D^4).absNorm:ℝ)^e :=
    (hdiv (D^4) (pow_ne_zero 4 hD)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  calc
    _ ≤ ((idealDivisors (D^4)).card:ℝ)^Fintype.card ι := by
      exact_mod_cast bounded_labels_card S D hD
    _ ≤ ((idealDivisors (D^4)).card:ℝ)^N := pow_le_pow_right₀ hdR hi
    _ ≤ (K'*((D^4).absNorm:ℝ)^e)^N := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      simp only [map_pow,Nat.cast_pow]
      rw [←Real.rpow_natCast_mul (Nat.cast_nonneg _)]
      congr 2
      dsimp [e]
      push_cast
      field_simp

theorem prefix_max_le_product {ι : Type*} [Fintype ι]
    (B : Tuple ι) (hB : ∀j,B j≠0) (d : Id×Id) (hd : d.1≠0∧d.2≠0) :
    prefixNormMax (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))≤
      prefixNormMax d*(finiteTupleProduct B).absNorm := by
  have hn : finiteTupleProduct B≠0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  have hb (j : Fin 2) : ((B (Sum.inr j)).absNorm:ℝ)≤(finiteTupleProduct B).absNorm :=
    CenteredExceptionalCount.norm_le_of_dvd hn (Finset.dvd_prod_of_mem B (Finset.mem_univ _))
  unfold prefixNormMax
  apply max_le
  · simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul (le_max_left _ _) (hb 0) (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) (le_max_left _ _))
  · simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul (le_max_right _ _) (hb 1) (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) (le_max_left _ _))

/-- The saving lost to a complete artificial extraction uses exponent
alpha on its FULL norm. After its linear reciprocal cost, 1-alpha remains. -/
theorem shortened_saving (x p q n α : ℝ) (hx : 0<x) (hp : 0<p)
    (hq : 0<q) (hn : 1≤n) (hqp : q≤p*n) (hα : 0≤α) :
    (max 1 (x/q))^(-α)/n≤(max 1 (x/p))^(-α)*n^(-(1-α)) := by
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hmax : max 1 (x/p)/n≤max 1 (x/q) := by
    rw [←max_div_div_right hn0.le]
    apply max_le
    · exact (div_le_self zero_le_one hn).trans (le_max_left _ _)
    · have he : x/p/n=x/(p*n) := by ring
      rw [he]
      exact (div_le_div_of_nonneg_left hx.le hq hqp).trans (le_max_right _ _)
  have hpow := Real.rpow_le_rpow_of_nonpos
    (div_pos (zero_lt_one.trans_le (le_max_left _ _)) hn0) hmax (neg_nonpos.mpr hα)
  apply (div_le_div_of_nonneg_right hpow hn0.le).trans_eq
  rw [Real.div_rpow (zero_le_one.trans (le_max_left _ _)) hn0.le,Real.rpow_neg hn0.le,
    div_inv_eq_mul]
  rw [show (max 1 (x/p))^(-α)*n^α/n=(max 1 (x/p))^(-α)*(n^α*n^(-1:ℝ)) by
    rw [Real.rpow_neg_one];ring,←Real.rpow_add hn0]
  congr 2
  ring

/-- The actual masked row. Full-support extraction is summed here;
there is no analytic row or energy estimate among the hypotheses.
The dimension cap precedes the constant, so this theorem remains uniform
when the live type changes with a genuine common allocation. -/
theorem uniform_masked_principal (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧ ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀Z : ℝ,1≤Z→∀Fhole D R : Id,Fhole≠0→(Fhole.absNorm:ℝ)≤Z^Bcap→Squarefree D→R≠0→
      ∀S H : Finset PrimeIdeal,(∀P∈S,Supported P.val)→(∀P∈H,P.val∣Fhole)→
      ∀(η : Character)(z : O),z≠0→
      (HeckeRowClosure.rowConductorBound η (fixedBadMask*idealGenerator (R*D)) 1 z:ℝ)≤Z^Bcap→
      CenteredExceptionalProfile.FixedInducingRow η Q fixedBadMask 1 z→
      ∀(ι : Type*) [Fintype ι],Fintype.card ι≤N→
      ∀(pool : ι→Finset Id)(ν : ι→Id→ℂ)(Wslot : ι→ℝ→ℂ)(P M : ι→ℝ),
      (∀i,1≤P i)→(∀i,1≤M i)→(∀i,pool i⊆primeValues S)→
      (∀i I,I∈pool i→Prime I)→
      (∀i I,I∈pool i→Supported I∧(I.absNorm:ℝ)≤2*P i)→
      (∀i I,‖ν i I‖≤1)→(∀i x,‖Wslot i x‖≤M i)→
      (∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2)→(∏i,2*P i)≤Z^Bcap→
      ∀(d : Id×Id)(hd : d.1≠0∧d.2≠0),
      ∀t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ,0<L→
      L≤X₁→L≤X₂→L≤Y₁→L≤Y₂→X₁≤U₁→X₂≤U₂→Y₁≤U₁→Y₂≤U₂→
      X₁*X₂=T→Y₁*Y₂=T→
      (∀I,Supported I→((I.absNorm:ℝ)≤b*(U₁/d.1.absNorm)∨
        (I.absNorm:ℝ)≤b*(U₂/d.2.absNorm))→primeSupport I⊆primeValues S)→
      ‖maskedRow (naturalCharacter η z) S H pool d hd D R ν Wslot P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b X₁ X₂ Y₁ Y₂‖≤
        (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*(∏i,M i)*2^Fintype.card ι*
          Real.sqrt (T*∏i,P i)/pairNorm d)*
        (D.absNorm:ℝ)^(δ-(1-α))*(max 1 (L/prefixNormMax d))^(-α) ∧
      ‖maskedRow (naturalCharacter η z) S H pool d hd D R ν Wslot P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b X₁ X₂ Y₁ Y₂‖≤
        (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*(∏i,M i)*2^Fintype.card ι*
          Real.sqrt (T*∏i,P i)/pairNorm d)*(D.absNorm:ℝ)^(δ-1) := by
  obtain ⟨J,control,h00,hprincipal⟩ := uniform_frozen_principal α Bcap a b ε hα hα4 hBcap ha hb hε
  obtain ⟨K,hK,hcount⟩ := bounded_labels_uniform (N+2) (by omega) δ hδ
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hpoint⟩ := hprincipal Q hQ
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ Fhole D R hFhole hFcut hD hR S H hS hH η z hz hcond hex
    ι instι hι pool ν Wslot P M hP hM hpool hp hpn hν hWnorm hW hV d hd
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  let pools := sourcePools pool d hd b X₁ X₂ Y₁ Y₂
  let labels := boundedLabels pools D
  let A := C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
    (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*(∏i,M i)*2^Fintype.card ι*
    Real.sqrt (T*∏i,P i)/pairNorm d
  let saving := (max 1 (L/prefixNormMax d))^(-α)
  have hP0 : ∀i,0<P i := fun i=>zero_lt_one.trans_le (hP i)
  have hM0 : ∀i,0≤M i := fun i=>zero_le_one.trans (hM i)
  have hA : 0≤A := by
    have := sourceControl_nonneg control W₁
    have := sourceControl_nonneg control W₂
    have := Finset.prod_nonneg (fun i (_ : i∈Finset.univ)=>hM0 i)
    have := Finset.prod_nonneg (fun i (_ : i∈Finset.univ)=>mul_nonneg (by norm_num : (0:ℝ)≤256) (hM0 i))
    have := pairNorm_pos hd.1 hd.2
    have hz0 : 0<Z := zero_lt_one.trans_le hZ
    dsimp [A]
    positivity
  have hsave : 0≤saving := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hD0 : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  let E := A*(D.absNorm:ℝ)^(-(1-α))*saving
  have hE : 0≤E := mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hD0.le _)) hsave
  let E₀ := A/(D.absNorm:ℝ)
  have hE₀ : 0≤E₀ := div_nonneg hA hD0.le
  have hterm (B : labels) :
      ‖(if D∣finiteTupleProduct B.val then
          frozenWeight (punctureProduct S H) B.val*idealCoeff (naturalCharacter η z) (finiteTupleProduct B.val) else 0)*
        frozenRow (naturalCharacter η z) S H pool d hd B.val
          (allocation_data pools D B.val (Finset.mem_filter.mp B.property).1).1 D R
          ν Wslot P V₁ V₂ b X₁ X₂ Y₁ Y₂‖≤min E E₀ := by
    let hB := (allocation_data pools D B.val (Finset.mem_filter.mp B.property).1).1
    by_cases hDB : D∣finiteTupleProduct B.val
    · rw [if_pos hDB,norm_mul]
      have hphase : ‖frozenWeight (punctureProduct S H) B.val*
          idealCoeff (naturalCharacter η z) (finiteTupleProduct B.val)‖≤1 := by
        rw [norm_mul]
        have hw : ‖frozenWeight (punctureProduct S H) B.val‖≤1 := by
          unfold frozenWeight
          split_ifs <;> norm_num
        exact (mul_le_mul hw (idealCoeff_norm_le_one _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      apply (mul_le_of_le_one_left (norm_nonneg _) hphase).trans
      have hliveP : (∏i : liveIndices B.val,2*P i.val)≤Z^Bcap := by
        apply le_trans _ hV
        rw [Finset.prod_coe_sort (liveIndices B.val) (fun i=>2*P i)]
        exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>mul_nonneg (by norm_num) (hP0 i).le) (fun i _ _=>by linarith [hP i])
      have hpre (e B₀ : Id) (he : e≠0) (hB₀ : B₀≠0) (U : ℝ) (hU : 0≤U) :
          U/(e*B₀).absNorm≤U/e.absNorm := by
        simp only [map_mul,Nat.cast_mul]
        apply div_le_div_of_nonneg_left hU (zero_lt_one.trans_le (ideal_norm_one_le he))
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (ideal_norm_one_le hB₀)
      have hcover (I : Id) (hI : Supported I)
          (hh : (I.absNorm:ℝ)≤b*(U₁/(d.1*B.val (Sum.inr 0)).absNorm)∨
            (I.absNorm:ℝ)≤b*(U₂/(d.2*B.val (Sum.inr 1)).absNorm)) : primeSupport I⊆primeValues S := by
        apply henclose I hI
        rcases hh with hh|hh
        · exact Or.inl (hh.trans (mul_le_mul_of_nonneg_left
            (hpre d.1 (B.val (Sum.inr 0)) hd.1 (hB _) U₁ ((hL.trans_le hX₁).trans_le hXU₁).le) hb))
        · exact Or.inr (hh.trans (mul_le_mul_of_nonneg_left
            (hpre d.2 (B.val (Sum.inr 1)) hd.2 (hB _) U₂ ((hL.trans_le hX₂).trans_le hXU₂).le) hb))
      have hh := hpoint W₁ W₂ hs₁ hs₂ Z hZ Fhole D R hFhole hFcut hD.ne_zero hR
        S H hS hH η z hz hcond hex ι pool ν Wslot P M hP0 hM hpool hpn hν hWnorm hW B.val hB hliveP d hd
        t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY hcover
      apply hh.trans
      have hslot : (∏i : liveIndices B.val,256*M i.val)≤∏i,256*M i := by
        rw [Finset.prod_coe_sort (liveIndices B.val) (fun i=>256*M i)]
        exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>mul_nonneg (by norm_num) (hM0 i)) (fun i _ _=>by nlinarith [hM i])
      have hG : finiteTupleProduct B.val≠0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
      have hG1 : (1:ℝ)≤(finiteTupleProduct B.val).absNorm := ideal_norm_one_le hG
      have hDG := CenteredExceptionalCount.norm_le_of_dvd hG hDB
      have hs := shortened_saving L (prefixNormMax d)
        (prefixNormMax (d.1*B.val (Sum.inr 0),d.2*B.val (Sum.inr 1)))
        (finiteTupleProduct B.val).absNorm α hL (prefixNormMax_pos d hd)
        (prefixNormMax_pos _ ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩)
        hG1 (prefix_max_le_product B.val hB d hd) hα
      have hpow : ((finiteTupleProduct B.val).absNorm:ℝ)^(-(1-α))≤(D.absNorm:ℝ)^(-(1-α)) :=
        Real.rpow_le_rpow_of_nonpos hD0 hDG (by linarith)
      have hraw : (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i : liveIndices B.val,256*M i.val)*
          Real.sqrt (T*∏i,P i)/pairNorm d)*((∏i,M i)*2^Fintype.card ι)≤A := by
        have hz0 : 0<Z := zero_lt_one.trans_le hZ
        have hcontrols := mul_nonneg (sourceControl_nonneg control W₁) (sourceControl_nonneg control W₂)
        have hprodM := Finset.prod_nonneg (fun i (_ : i∈Finset.univ)=>hM0 i)
        have hd0 := pairNorm_pos hd.1 hd.2
        have hf : 0≤C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
            (1+‖t₁‖+‖t₂‖)^J*Real.sqrt (T*∏i,P i)/pairNorm d*
            (∏i,M i)*2^Fintype.card ι := by positivity
        convert mul_le_mul_of_nonneg_left hslot hf using 1 <;> dsimp [A] <;> ring
      apply le_min
      · calc
          _ = ((C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
            (1+‖t₁‖+‖t₂‖)^J*(∏i : liveIndices B.val,256*M i.val)*
            Real.sqrt (T*∏i,P i)/pairNorm d)*((∏i,M i)*2^Fintype.card ι))*
            ((max 1 (L/prefixNormMax (d.1*B.val (Sum.inr 0),d.2*B.val (Sum.inr 1))))^(-α)/
              (finiteTupleProduct B.val).absNorm) := by ring
          _ ≤ A*((max 1 (L/prefixNormMax (d.1*B.val (Sum.inr 0),d.2*B.val (Sum.inr 1))))^(-α)/
              (finiteTupleProduct B.val).absNorm) := mul_le_mul_of_nonneg_right hraw
            (div_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (zero_le_one.trans hG1))
          _ ≤ A*(saving*((finiteTupleProduct B.val).absNorm:ℝ)^(-(1-α))) :=
            mul_le_mul_of_nonneg_left hs hA
          _ ≤ A*(saving*(D.absNorm:ℝ)^(-(1-α))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hsave) hA
          _ = E := by dsimp [E];ring
      · have hsav : (max 1 (L/prefixNormMax (d.1*B.val (Sum.inr 0),d.2*B.val (Sum.inr 1))))^(-α)≤1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (neg_nonpos.mpr hα)
        have hscalar : 0≤
            (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
              (1+‖t₁‖+‖t₂‖)^J*(∏i : liveIndices B.val,256*M i.val)*
              Real.sqrt (T*∏i,P i)/pairNorm d)*
              (((∏i,M i)*2^Fintype.card ι)/(finiteTupleProduct B.val).absNorm) := by
          have := sourceControl_nonneg control W₁
          have := sourceControl_nonneg control W₂
          have := Finset.prod_nonneg (fun i (_ : i∈Finset.univ)=>hM0 i)
          have := Finset.prod_nonneg (fun (i : liveIndices B.val) (_ : i∈Finset.univ)=>
            mul_nonneg (by norm_num : (0:ℝ)≤256) (hM0 i.val))
          have := pairNorm_pos hd.1 hd.2
          have hz0 : 0<Z := zero_lt_one.trans_le hZ
          positivity
        calc
          _ ≤ (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
              (1+‖t₁‖+‖t₂‖)^J*(∏i : liveIndices B.val,256*M i.val)*
              Real.sqrt (T*∏i,P i)/pairNorm d)*
              (((∏i,M i)*2^Fintype.card ι)/(finiteTupleProduct B.val).absNorm) :=
            mul_le_of_le_one_right hscalar hsav
          _ ≤ A/(finiteTupleProduct B.val).absNorm := by
            convert div_le_div_of_nonneg_right hraw (zero_le_one.trans hG1) using 1 <;> ring
          _ ≤ A/(D.absNorm:ℝ) := div_le_div_of_nonneg_left hA hD0 hDG
    · rw [if_neg hDB,zero_mul,norm_zero]
      exact le_min hE hE₀
  have hsum : ‖maskedRow (naturalCharacter η z) S H pool d hd D R ν Wslot P V₁ V₂ b X₁ X₂ Y₁ Y₂‖≤
      (K*(D.absNorm:ℝ)^δ)*min E E₀ := by
    rw [masked_row_frozen (naturalCharacter η z) S H pool hp d hd D R hD]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑B : labels,min E E₀ := Finset.sum_le_sum (fun B _=>hterm B)
      _ = ((labels.card:ℝ))*min E E₀ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      _ ≤ (K*(D.absNorm:ℝ)^δ)*min E E₀ := mul_le_mul_of_nonneg_right
        (hcount (by simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hι 2) pools D hD.ne_zero)
        (le_min hE hE₀)
  constructor
  · apply hsum.trans
    apply (mul_le_mul_of_nonneg_left (min_le_left E E₀)
      (mul_nonneg hK.le (Real.rpow_nonneg hD0.le _))).trans_eq
    change (K*(D.absNorm:ℝ)^δ)*E=_
    have hp : (D.absNorm:ℝ)^δ*(D.absNorm:ℝ)^(-(1-α))=(D.absNorm:ℝ)^(δ-(1-α)) := by
      rw [←Real.rpow_add hD0]
      congr 1
    dsimp only [E,A,saving]
    calc
      _ = (C*K*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
        (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*(∏i,M i)*2^Fintype.card ι*
        Real.sqrt (T*∏i,P i)/pairNorm d)*
        ((D.absNorm:ℝ)^δ*(D.absNorm:ℝ)^(-(1-α)))*(max 1 (L/prefixNormMax d))^(-α) := by ring
      _ = _ := by rw [hp]
  · apply hsum.trans
    apply (mul_le_mul_of_nonneg_left (min_le_right E E₀)
      (mul_nonneg hK.le (Real.rpow_nonneg hD0.le _))).trans_eq
    have hp : (D.absNorm:ℝ)^δ/(D.absNorm:ℝ)=(D.absNorm:ℝ)^(δ-1) := by
      rw [div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hD0]
      congr 1
    dsimp only [E₀,A]
    calc
      _ = (C*K*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
        (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*(∏i,M i)*2^Fintype.card ι*
        Real.sqrt (T*∏i,P i)/pairNorm d)*((D.absNorm:ℝ)^δ/(D.absNorm:ℝ)) := by ring
      _ = _ := by rw [hp]

/-- Coefficient-free norm summation. This is the existing absolute
ideal Dirichlet convergence theorem at a real exponent greater than one. -/
theorem ideal_power_mass (s : ℝ) (hs : 1<s) :
    ∃C : ℝ,0<C ∧ ∀Ds : Finset Id,(∀D∈Ds,D≠0)→
      (∑D∈Ds,(D.absNorm:ℝ)^(-s))≤C := by
  have hsum := CubicEisenstein.fullIdealWeight_summable_norm (s:ℂ) (by simpa using hs)
  let C := 1+∑'D : Id,‖CubicEisenstein.fullIdealWeight (s:ℂ) D‖
  have hn : 0≤∑'D : Id,‖CubicEisenstein.fullIdealWeight (s:ℂ) D‖ :=
    tsum_nonneg (fun _=>norm_nonneg _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro Ds hDs
  have he : (∑D∈Ds,(D.absNorm:ℝ)^(-s))=
      ∑D∈Ds,‖CubicEisenstein.fullIdealWeight (s:ℂ) D‖ := by
    apply Finset.sum_congr rfl
    intro D hD
    rw [CubicEisenstein.fullIdealWeight,if_neg (hDs D hD)]
    have hd : 0<(D.absNorm:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hDs D hD))
    change _=‖((D.absNorm:ℝ):ℂ)^(-(s:ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hd]
    simp only [Complex.neg_re,Complex.ofReal_re]
  rw [he]
  apply (hsum.sum_le_tsum Ds (fun _ _=>norm_nonneg _)).trans
  dsimp [C]
  linarith

/-- The actual reciprocal exponents of the two masked bounds above
are summable. For alpha=7/10 it suffices to choose delta<3/20.
There is no cap depending on Z and no extra fresh-divisor factor. -/
theorem paired_mask_norm_mass (α δ : ℝ) (hgap : α+2*δ<1) :
    ∃C : ℝ,0<C ∧ ∀(Ds : Finset Id)(μ : Id→ℂ),
      (∀D∈Ds,D≠0)→(∀D∈Ds,‖μ D‖≤1)→
      (∑D∈Ds,‖μ D‖*((D.absNorm:ℝ)^(δ-(1-α))*(D.absNorm:ℝ)^(δ-1)))≤C := by
  obtain ⟨C,hC,hbound⟩ := ideal_power_mass (2-α-2*δ) (by linarith)
  refine ⟨C,hC,?_⟩
  intro Ds μ hDs hμ
  apply le_trans _ (hbound Ds hDs)
  apply Finset.sum_le_sum
  intro D hD
  have hd : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hDs D hD))
  apply (mul_le_of_le_one_left
    (mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _)) (hμ D hD)).trans_eq
  rw [←Real.rpow_add hd]
  congr 1
  ring

end
end Candidate.FourthPower.MixedPrincipalMasked
