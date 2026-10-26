/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first-window support, followed by the real finite exceptional
allocation budget. Zero frequencies are excluded before fourth powers.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstExceptionalNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstExceptionalWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAnnularMajorant CenteredMomentFirstAnnularEnergy
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentFirstMixedAllowance CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open RayFourExpansion CenteredMomentSecondEnergySplit CenteredMomentLattice
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalBudget
open MixedPrincipalCentered MixedCommonCoefficient MixedCommonRestriction
open MixedPrincipalWindow MixedOriginalTail
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstLiveSource MixedFirstExceptionalNormalization MixedSourceAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The annular profile's actual finite support, with zero excluded.
The floor gives the exact real norm cutoff, not an additional mesh loss. -/
def annularRows (n : ℤ) : Finset O := rowNormDisk ⌊2*dyadicScale n⌋₊

theorem mem_annularRows (n : ℤ) (z : O) :
    z∈annularRows n↔z≠0 ∧ normValue z≤2*dyadicScale n := by
  simpa only [annularRows,normValue_eq_embedding] using
    TruncatedPrincipalPoisson.mem_rowNormDisk_floor
      (mul_nonneg (by norm_num : (0:ℝ)≤2) (dyadicScale_pos n).le) z

theorem annular_profile_support (n : ℤ) (z : O)
    (hz : CenteredMomentFirstAnnularMajorant.profile (normValue z/dyadicScale n)≠0) :
    z∈annularRows n := by
  apply (mem_annularRows n z).mpr
  constructor
  · intro he
    subst z
    have hnorm : normValue (0:O)=0 := by simp [normValue_eq_embedding]
    exact hz (by rw [hnorm,zero_div,profile_zero])
  · have hw : weight (normValue z/dyadicScale n)≠0 := by
      intro hw
      exact hz (by rw [profile_apply,hw];rfl)
    exact (div_le_iff₀ (dyadicScale_pos n)).mp (weight_support hw).2

/-- Exact finite sum of the original annular energy. Coefficients and
all their masks are unchanged, and no zero row is admitted. -/
theorem annular_energy_finite {α : Type*} (S : Finset α) (g : α→O)
    (hg : ∀i,Supported (Ideal.span {g i})) (c : α→ℂ) (n : ℤ) :
    (gaussEnergy S g hg c CenteredMomentFirstAnnularMajorant.profile (dyadicScale n)).re=
      ∑z∈annularRows n,‖gaussPolynomial S g hg c z‖^2*
        (CenteredMomentFirstAnnularMajorant.profile (normValue z/dyadicScale n)).re := by
  have hs := gaussEnergy_hasSum_re S g hg c CenteredMomentFirstAnnularMajorant.profile
    (dyadicScale n) (dyadicScale_pos n)
  rw [←hs.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  apply tsum_eq_sum
  intro z hz
  have hp : CenteredMomentFirstAnnularMajorant.profile (normValue z/dyadicScale n)=0 :=
    not_ne_iff.mp (fun hp=>hz (annular_profile_support n z hp))
  rw [hp,Complex.zero_re,mul_zero]

theorem nominal_scale_factor (C D : Id) (E : Finset (CommonIndex C D))
    (K V Z κ : ℝ) (hZ : 1<Z) (n : ℤ) :
    nominalChildScale C D E K V Z κ n=dyadicScale n*
      Z^(max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ) := by
  unfold nominalChildScale
  rw [show Real.logb Z (dyadicScale n)+
      max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ=
      Real.logb Z (dyadicScale n)+
        (max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ) by ring,
    Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos n)]

/-- The factor two is a single profile-support cost, independent of
the number of marked slots and of all common/allocation labels. -/
theorem annular_scale_le (C D : Id) (E : Finset (CommonIndex C D))
    (K V Z κ : ℝ) (hZ : 1<Z) (hpadding : 2≤Z^κ) (n : ℤ) :
    2*dyadicScale n≤nominalChildScale C D E K V Z κ n := by
  rw [nominal_scale_factor C D E K V Z κ hZ n]
  calc
    _≤dyadicScale n*Z^κ := by nlinarith [dyadicScale_pos n]
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le
        (by linarith [le_max_right (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) (0:ℝ)]))
      (dyadicScale_pos n).le

theorem eventually_padding (κ : ℝ) (hκ : 0<κ) : ∀ᶠZ : ℝ in atTop,2≤Z^κ :=
  (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hκ)) 2

/-- These are the precise row-domain/weight/norm inputs of
MixedPhysicalTransfer.sparse_weighted_average, before its K4 map. -/
theorem actual_annular_inputs (C D : Id) (E : Finset (CommonIndex C D))
    (K V Z κ : ℝ) (hZ : 1<Z) (hpadding : 2≤Z^κ) (n : ℤ) :
    ∀z∈annularRows n,z≠0 ∧
      0≤(CenteredMomentFirstAnnularMajorant.profile (normValue z/dyadicScale n)).re ∧
      (CenteredMomentFirstAnnularMajorant.profile (normValue z/dyadicScale n)).re≤1 ∧
      (Ideal.absNorm (Ideal.span {z}):ℝ)≤nominalChildScale C D E K V Z κ n := by
  intro z hz
  have h := (mem_annularRows n z).mp hz
  refine ⟨h.1,profile_nonneg _,profile_le_one _,?_⟩
  exact h.2.trans (annular_scale_le C D E K V Z κ hZ hpadding n)

/-- The actual first block is exactly its nonzero annular rows. This
specialization preserves the literal original source coefficient. -/
theorem actual_block_rows (s : Source ι a b) (ha : 0<a) (η : Character)
    (m A : O) (t : ℝ) (seed : Id) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (Φ : 𝓢(ℝ,ℂ))
    (K Z κ : ℝ) (hZ : 1<Z) (hpadding : 2≤Z^κ) (n : Fin 4→ℤ) :
    block η m A t (MixedPrincipalWindow.sourceColumns s) (MixedPrincipalWindow.sourceCoefficient s ha seed)
      C D hC hD E rows Φ (fun _=>logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=
    block η m A t (MixedPrincipalWindow.sourceColumns s) (MixedPrincipalWindow.sourceCoefficient s ha seed)
      C D hC hD E (activeRows rows n) Φ (fun _=>logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) ∧
    ∀z∈activeRows rows n,z≠0 ∧
      (Ideal.absNorm (Ideal.span {z}):ℝ)≤nominalChildScale C D E K (sourceVolume s) Z κ (n 1) := by
  refine ⟨block_activeRows η m A t _ _ C D hC hD E rows Φ K n,?_⟩
  intro z hz
  refine ⟨activeRows_nonzero rows n z hz,?_⟩
  have hs := (activeRows_norm rows n z hz).2.2.le
  apply hs.trans
  apply le_trans _ (annular_scale_le C D E K (sourceVolume s) Z κ hZ hpadding (n 1))
  linarith [dyadicScale_pos (n 1)]

/-- No new enclosure premise is needed when applying the checked inner
source theorem: the original source record already contains this cover. -/
theorem live_enclosure (s : Source ι a b) : OriginalEnclosure (liveSource s) := by
  intro I hI hi
  exact s.henclose I hI hi

theorem live_dimension (s : Source ι a b) :
    Fintype.card (liveIndices s.B)≤Fintype.card ι := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ

theorem live_fullMarkedCost (s : Source ι a b) : fullMarkedCost (liveSource s)≤fullMarkedCost s := by
  have hprod : (∏i : liveIndices s.B,s.M i.val)≤∏i,s.M i := by
    rw [Finset.prod_coe_sort (liveIndices s.B) s.M]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.hM i)) (fun i _ _=>s.hM i)
  have hprod0 : 0≤∏i : liveIndices s.B,s.M i.val :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i.val))
  have hcard : (1024:ℝ)^Fintype.card (liveIndices s.B)≤1024^Fintype.card ι :=
    pow_le_pow_right₀ (by norm_num) (live_dimension s)
  rw [fullMarkedCost_eq,fullMarkedCost_eq]
  exact mul_le_mul hcard (pow_le_pow_left₀ hprod0 hprod 3) (by positivity) (by positivity)

theorem live_sourceProfile (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Z ε : ℝ) (hZ : 0≤Z) :
    0≤sourceProfile (liveSource s) J control Z ε ∧
      sourceProfile (liveSource s) J control Z ε≤sourceProfile s J control Z ε := by
  have hfactor : 0≤(sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
      (1+‖s.t₁‖+‖s.t₂‖)^J := by
    have := sourceControl_nonneg control s.W₁
    have := sourceControl_nonneg control s.W₂
    positivity
  constructor
  · exact mul_nonneg hfactor (fullMarkedCost_nonneg (liveSource s))
  · exact mul_le_mul_of_nonneg_left (live_fullMarkedCost s) hfactor

/-- The complete original-source fixed factors, before the uniform
genuine-allocation mass. PrefixNormMax remains in referenceExponent. -/
def originalFactor (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q : Id) (Z ε : ℝ) : ℝ :=
  fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ)*slotCost s

def referenceExponent (s : Source ι a b) (η : Character) (K Z Csec ξ κ W : ℝ) : ℝ :=
  Real.logb Z (sourceVolume s)-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z fixedPresentationCost)/6-2*(Real.logb Z s.L-Real.logb Z (prefixNormMax s.d))/3+
    7*Real.logb Z W/3+5*(frequencyLoss Z Csec ξ+κ)/6

theorem originalFactor_nonneg (s : Source ι a b) (ha : 0<a) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε : ℝ) : 0≤originalFactor s J control Q Z ε := by
  have := fixedQCost_nonneg Q
  have := slotCost_nonneg s
  unfold originalFactor
  positivity

def rawAllocationBudget (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (τ : Character) (C D Q : Id) (J : ℕ) (control : Finset (ℕ×ℕ)) (Z ε Kchild W : ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) C).card:ℝ)*
    ∑B : actualAllocations (tuplePools s) C,
      (‖frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
        (sourceVolume (allocatedLiveSource s hb cover C B)*
          savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W))/
        reference τ C D (sourceVolume s) Z

/-- The finite source budget produced by genuine Cauchy, with all live
profile factors and the actual count paid uniformly. No energy estimate
is introduced as a hypothesis; the budget is exactly savedBudget. -/
theorem uniform_raw_allocation_reference (N : ℕ) (δalloc : ℝ) (hδalloc : 0<δalloc) :
    ∃Ccount : ℝ,0<Ccount ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,
    ∀s : Source ι a b,∀ha : 0<a,∀hb : 0≤b,∀cover : OriginalEnclosure s,
    Fintype.card ι≤N →
    ∀(η τ : Character)(C D Q : Id)(hC : Supported C)(hD : Supported D),
    CompletedGauss.primeSupport C=CompletedGauss.primeSupport D → ∀E : Finset (CommonIndex C D),
    ∀(J : ℕ)(control : Finset (ℕ×ℕ))(K Z ε Tsec Csec ξ κ W : ℝ),
    0<K → 1<Z → 0<W → 1≤Csec → 0≤ξ →
    τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} →
    Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K (sourceVolume s) →
    ∀n : ℤ,Retained (frequencyRadius Tsec Z ξ) n →
    rawAllocationBudget s hb cover τ C D Q J control Z ε
      (nominalChildScale C D E K (sourceVolume s) Z κ n) W≤
      Ccount*(C.absNorm:ℝ)^δalloc*originalFactor s J control Q Z ε*
        Z^(referenceExponent s η K Z Csec ξ κ W) := by
  obtain ⟨Ccount,hCcount,hcount⟩ := genuine_count_squared (N+2) δalloc hδalloc
  refine ⟨Ccount,hCcount,?_⟩
  intro ι instι a b s ha hb cover hι η τ C D Q hC hD hCD E J control K Z ε
    Tsec Csec ξ κ W hK hZ hW hCsec hξ hmod hsec n hn
  let Kchild := nominalChildScale C D E K (sourceVolume s) Z κ n
  let F := fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ)
  let Ebudget := originalFactor s J control Q Z ε*Z^(referenceExponent s η K Z Csec ξ κ W)
  have hF : 0≤F := by have := fixedQCost_nonneg Q;dsimp only [F];positivity
  have hEbudget : 0≤Ebudget := mul_nonneg (originalFactor_nonneg s ha J control Q Z ε)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hchild : 0<Kchild := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hterm (B : actualAllocations (tuplePools s) C) :
      (‖frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
        (sourceVolume (allocatedLiveSource s hb cover C B)*
          savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W))/
        reference τ C D (sourceVolume s) Z≤Ebudget := by
    have hp := live_sourceProfile (allocationSource s hb cover C B) J control Z ε
      (zero_lt_one.trans hZ).le
    have hp2 := pow_le_pow_left₀ hp.1 hp.2 2
    have hr := actual_allocation_reference s η τ C D hC hD hCD E B K Z Tsec Csec ξ κ W
      hK hZ hW hCsec hξ hmod hsec n hn
    have hratio : 0≤allocationShape s C B Kchild W/reference τ C D (sourceVolume s) Z := by
      have hB := (allocation_data (tuplePools s) C B.val (Finset.mem_filter.mp B.property).1).1
      have hpair := pairNorm_pos
        (d := (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
        (mul_ne_zero s.hd.1 (hB (Sum.inr 0)))
        (mul_ne_zero s.hd.2 (hB (Sum.inr 1)))
      have hprefix := prefixNormMax_pos
        (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))
        ⟨mul_ne_zero s.hd.1 (hB _),mul_ne_zero s.hd.2 (hB _)⟩
      have hPlive : 0≤∏i : liveIndices B.val,s.P i.val :=
        Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i.val))
      have hv := (sourceVolume_pos s).le
      have hL0 := s.hL
      have hZ0 : 0<Z := zero_lt_one.trans hZ
      unfold allocationShape shape reference
      have := (s.total_pos).le
      positivity
    rw [allocated_raw_budget s ha hb cover C B J control Q Z ε Kchild W]
    calc
      _=F*(sourceProfile (allocatedLiveSource s hb cover C B) J control Z ε)^2*
        (allocationShape s C B Kchild W/reference τ C D (sourceVolume s) Z) := by
          dsimp only [F];ring
      _≤F*(sourceProfile s J control Z ε)^2*
        (allocationShape s C B Kchild W/reference τ C D (sourceVolume s) Z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hF) hratio
      _≤F*(sourceProfile s J control Z ε)^2*
        (slotCost s*Z^(referenceExponent s η K Z Csec ξ κ W)) :=
          mul_le_mul_of_nonneg_left hr (mul_nonneg hF (sq_nonneg _))
      _=Ebudget := by dsimp only [F,Ebudget,originalFactor];ring
  have hdim : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hι 2
  have hc := hcount hdim (tuplePools s) C hC.1
  unfold rawAllocationBudget
  change ((actualAllocations (tuplePools s) C).card:ℝ)*_≤_
  calc
    _≤((actualAllocations (tuplePools s) C).card:ℝ)*
      ∑_B : actualAllocations (tuplePools s) C,Ebudget :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hterm B)) (Nat.cast_nonneg _)
    _=((actualAllocations (tuplePools s) C).card:ℝ)^2*Ebudget := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring
    _≤(Ccount*(C.absNorm:ℝ)^δalloc)*Ebudget := mul_le_mul_of_nonneg_right hc hEbudget
    _=_ := by dsimp only [Ebudget];ring

/-- Restricting the marked slots never enlarges their actual norm cap. -/
theorem live_marked_product (s : Source ι a b) :
    (∏i : liveIndices s.B,2*(liveSource s).P i)≤∏i,2*s.P i := by
  change (∏i : liveIndices s.B,2*s.P i.val)≤_
  rw [Finset.prod_coe_sort (liveIndices s.B) (fun i=>2*s.P i)]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
  · intro i _
    have := s.hP i
    positivity
  · intro i _ _
    have := s.hP i
    linarith

/-- The literal first-allocation contribution of the inner exceptional
part. The one outside fourth-power divisor W appears exactly once. -/
def exceptionalAllocation (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (τ : Character) (χ₀ : RayCharacter) (Q : Id)
    (m : O) (Dart : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (Z Tsecond ξsecond : ℝ) (C D : Id)
    (Hsource : actualAllocations (tuplePools s) C→ℝ) (Kchild W : ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) C).card:ℝ)*
    ∑B : actualAllocations (tuplePools s) C,
      (‖frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
        (‖partEnergy true τ χ₀ Q m t
          (sourceColumns (allocatedLiveSource s hb cover C B))
          (sourceCoefficient (allocatedLiveSource s hb cover C B) ha Dart)
          Φ (16*Kchild*W^4) Tsecond Z ξsecond (Hsource B)‖/W))/
        reference τ C D (sourceVolume s) Z

/-- Application of the checked inner exceptional theorem to the ACTUAL
allocated sources. No pair, count or energy estimate is assumed.

The displayed per-allocation pool and conductor caps are structural
admission conditions. Their eventual derivation from original-source
caps is a subsequent obligation; this theorem does not claim it. -/
theorem uniform_actual_allocation_reference (N : ℕ)
    (α Bcap a b ε δ Bnorm Lrad Cr εsum δalloc : ℝ)
    (hα : (2/3:ℝ)≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr)
    (hεsum : 0<εsum) (hδalloc : 0<δalloc) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃A Csum Ccount : ℝ,0<A ∧ 0<Csum ∧ 0<Ccount ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,
      Fintype.card ι≤N → (s.Fhole.absNorm:ℝ)≤Z^Bcap → (∏i,2*s.P i)≤Z^Bcap →
      ∀(η τ : Character)(C D : Id)(hC : Supported C)(hD : Supported D),
      CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀E : Finset (CommonIndex C D),∀(K Tfirst Cfirst ξfirst κ W : ℝ),
      0<K → 0<W → 1≤Cfirst → 0≤ξfirst →
      τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} →
      Tfirst≤Cfirst*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K (sourceVolume s) →
      ∀(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀Dart : Id,Squarefree Dart → Dart≠0 →
      ∀(t Tsecond ξsecond : ℝ),
      ∀Hsource : actualAllocations (tuplePools s) C→ℝ,0≤Tsecond →
      frequencyRadius Tsecond Z ξsecond≤Cr*Z^Lrad →
      (∀B : actualAllocations (tuplePools s) C,
        frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P≠0 →
        Hsource B≤Z^Bnorm ∧ poolCap (allocatedLiveSource s hb cover C B)≤Z^Bnorm ∧
        familyConductorBudget (allocatedLiveSource s hb cover C B) τ
          (frequencyRadius Tsecond Z ξsecond)≤Z^Bcap) →
      ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n →
      exceptionalAllocation s ha hb cover τ χ₀ Q m Dart t Φ Z Tsecond ξsecond C D Hsource
        (nominalChildScale C D E K (sourceVolume s) Z κ n) W≤
      ((Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*Z^(2*Bnorm*δ)*
        (Csum*Z^εsum/(Dart.absNorm:ℝ)))*
      (Ccount*(C.absNorm:ℝ)^δalloc*originalFactor s J control Q Z ε*
        Z^(referenceExponent s η K Z Cfirst ξfirst κ W)) := by
  obtain ⟨J,control,h00,hkernel⟩ := uniform_actual_exceptional_part N
    α Bcap a b ε δ Bnorm Lrad Cr εsum hα hα4 hBcap ha hb hε hδ hgap
      hBnorm hLrad hCr hεsum
  obtain ⟨Ccount,hCcount,hcount⟩ := uniform_raw_allocation_reference N δalloc hδalloc
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ckernel,hCkernel,hQ⟩ := hkernel Φ
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,hA,hCsum,hpoint⟩ := hQ Q hQ0 hQt hQ72
  refine ⟨A,Csum,Ccount,hA,hCsum,hCcount,?_⟩
  filter_upwards [hpoint] with Z hpoint
  obtain ⟨hZ,hpoint⟩ := hpoint
  refine ⟨hZ,?_⟩
  intro ι instι s cover hι hF hP η τ C D hC hD hCD E K Tfirst Cfirst ξfirst κ W
    hK hW hCfirst hξfirst hmod hfirst χ₀ m hm hml hm2 Dart hDart hDart0
    t Tsecond ξsecond Hsource hTsecond hradius hstruct n hn
  let Kchild := nominalChildScale C D E K (sourceVolume s) Z κ n
  let EnergyFactor := (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
    Z^(2*Bnorm*δ)*(Csum*Z^εsum/(Dart.absNorm:ℝ))
  have hEnergyFactor : 0≤EnergyFactor := by
    have := (heightBase_pos t).le
    dsimp only [EnergyFactor]
    positivity
  have hchild : 0<Kchild := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have href : 0<reference τ C D (sourceVolume s) Z := by
    have hτ := zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
    have hc := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
    have hv := sourceVolume_pos s
    unfold reference
    positivity
  have hterm (B : actualAllocations (tuplePools s) C) :
      (‖frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
        (‖partEnergy true τ χ₀ Q m t
          (sourceColumns (allocatedLiveSource s hb cover C B))
          (sourceCoefficient (allocatedLiveSource s hb cover C B) ha Dart)
          Φ (16*Kchild*W^4) Tsecond Z ξsecond (Hsource B)‖/W))/
        reference τ C D (sourceVolume s) Z≤
      EnergyFactor*((‖frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
        (sourceVolume (allocatedLiveSource s hb cover C B)*
          savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W))/
        reference τ C D (sourceVolume s) Z) := by
    by_cases hf : frozenWeight (punctureProduct s.S s.H) B.val*
        frozenCoefficient B.val C s.R s.ν s.Wslot s.P=0
    · simp only [hf,norm_zero,zero_pow (by decide : 2≠0),zero_mul,zero_div,mul_zero,le_refl]
    obtain ⟨hHsource,hpool,hconductor⟩ := hstruct B hf
    have hdim : Fintype.card (liveIndices B.val)≤N :=
      (live_dimension (allocationSource s hb cover C B)).trans hι
    have hPalloc : (∏i,2*(allocatedLiveSource s hb cover C B).P i)≤Z^Bcap :=
      (live_marked_product (allocationSource s hb cover C B)).trans hP
    have hp := hpoint (liveIndices B.val) (allocatedLiveSource s hb cover C B)
      (live_enclosure (allocationSource s hb cover C B)) hdim hF hPalloc
      hpool τ χ₀ m hm hml hm2 Dart hDart hDart0
      t Kchild W Tsecond ξsecond (Hsource B) hchild hW hTsecond hHsource hradius hconductor
    have hV := sourceVolume_pos (allocatedLiveSource s hb cover C B)
    have hraw : ‖partEnergy true τ χ₀ Q m t
          (sourceColumns (allocatedLiveSource s hb cover C B))
          (sourceCoefficient (allocatedLiveSource s hb cover C B) ha Dart)
          Φ (16*Kchild*W^4) Tsecond Z ξsecond (Hsource B)‖/W≤
        EnergyFactor*(sourceVolume (allocatedLiveSource s hb cover C B)*
          savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W) := by
      calc
        _=sourceVolume (allocatedLiveSource s hb cover C B)*
          (‖partEnergy true τ χ₀ Q m t
            (sourceColumns (allocatedLiveSource s hb cover C B))
            (sourceCoefficient (allocatedLiveSource s hb cover C B) ha Dart)
            Φ (16*Kchild*W^4) Tsecond Z ξsecond (Hsource B)‖/
              sourceVolume (allocatedLiveSource s hb cover C B)/W) := by
                field_simp [hV.ne',hW.ne'] <;> ring
        _≤sourceVolume (allocatedLiveSource s hb cover C B)*
          ((Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
            savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W*
            Z^(2*Bnorm*δ)*(Csum*Z^εsum/(Dart.absNorm:ℝ))) :=
              mul_le_mul_of_nonneg_left hp hV.le
        _=_ := by dsimp only [EnergyFactor];ring
    calc
      _≤(‖frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
          (EnergyFactor*(sourceVolume (allocatedLiveSource s hb cover C B)*
            savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W)))/
          reference τ C D (sourceVolume s) Z :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hraw (sq_nonneg _)) href.le
      _=_ := by ring
  have hbudget := hcount ι a b s ha hb cover hι η τ C D Q hC hD hCD E J control
    K Z ε Tfirst Cfirst ξfirst κ W hK hZ hW hCfirst hξfirst hmod hfirst n hn
  calc
    _≤EnergyFactor*rawAllocationBudget s hb cover τ C D Q J control Z ε Kchild W := by
      unfold exceptionalAllocation rawAllocationBudget
      calc
        _≤((actualAllocations (tuplePools s) C).card:ℝ)*
          ∑B : actualAllocations (tuplePools s) C,
            EnergyFactor*((‖frozenWeight (punctureProduct s.S s.H) B.val*
              frozenCoefficient B.val C s.R s.ν s.Wslot s.P‖^2*
                (sourceVolume (allocatedLiveSource s hb cover C B)*
                  savedBudget (allocatedLiveSource s hb cover C B) J control Q Z ε Kchild W))/
                reference τ C D (sourceVolume s) Z) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hterm B)) (Nat.cast_nonneg _)
        _=_ := by rw [←Finset.mul_sum];ring
    _≤_ := mul_le_mul_of_nonneg_left hbudget hEnergyFactor

end
end Candidate.FourthPower.MixedFirstExceptionalWindow
