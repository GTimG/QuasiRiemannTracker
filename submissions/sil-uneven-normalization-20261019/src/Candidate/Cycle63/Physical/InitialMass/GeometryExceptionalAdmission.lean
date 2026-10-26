import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalBudget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineCaps
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalSourceCaps CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyInputParentCapacity Cycle63InitialSource
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile
open CenteredMomentFirstScale CenteredMomentFirstChildLower
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstExceptionalChildPaid CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstAnnularInput CenteredMomentPrimePool CenteredMomentPrimeElements
open PNT.AnnularPrimeMass
local notation "O" => HeckeFamily.O
local instance geometryExceptionalAdmissionDecidable {α : Type*} : DecidableEq α := Classical.decEq _

section Affine
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryExceptionalAdmissionFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂

/-- The comparison rectangle preserves the product, so its second side is
also above the original quarter-width scale. -/
theorem affine_exceptional_plain_minimum (hZ : 1 < Z) (hM : 0 < M)
    (hlo₁ : (41/100)*M ≤ length Z X₁) (hlo₂ : (41/100)*M ≤ length Z X₂) :
    Z^(M/4) ≤ (inp).X₁ ∧ Z^(M/4) ≤ (inp).X₂ ∧
    Z^(M/4) ≤ (inp).Y₁ ∧ Z^(M/4) ≤ (inp).Y₂ := by
  have hz := zero_lt_one.trans hZ
  have hx₁ : Z^((41/100)*M) ≤ X₁ :=
    (by
      conv_rhs => rw [initial_scale_exact Z X₁ M hZ hM hlo₁]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le hlo₁)
  have hx₂ : Z^((41/100)*M) ≤ X₂ :=
    (by
      conv_rhs => rw [initial_scale_exact Z X₂ M hZ hM hlo₂]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le hlo₂)
  have hp : Z^(M/2) ≤ X₁*X₂ := by
    calc
      _ ≤ Z^((41/100)*M+(41/100)*M) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z^((41/100)*M)*Z^((41/100)*M) := Real.rpow_add hz _ _
      _ ≤ _ := mul_le_mul hx₁ hx₂ (Real.rpow_nonneg hz.le _) hX₁.le
  refine ⟨?_, ?_, le_rfl, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hx₁
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hx₂
  · change Z^(M/4) ≤ X₁*X₂/Z^(M/4)
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
    rw [←Real.rpow_add hz]
    convert hp using 1
    congr 1
    ring
end Affine

theorem eventual_fixed_character_plain_loss (η : Character) (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      (1+Real.logb Z (η.modulus.absNorm:ℝ))/4-loss ≤ (1/4:ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (show 0 < 4*loss by positivity)).eventually
    (eventually_ge_atTop (η.modulus.absNorm:ℝ)), eventually_gt_atTop (1:ℝ)] with Z hη hZ
  refine ⟨hZ, ?_⟩
  have hn : 0 < (η.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hh := (Real.logb_le_iff_le_rpow hZ hn).mpr hη
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_geometry_exceptional_character_cap
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ A : ℝ) (hK : 0<K)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^A) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    ((geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus.absNorm:ℝ) ≤
      fixedPresentationCost*(s.η.modulus.absNorm:ℝ)*(Z^A)^2 := by
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  have hc : (src.C.absNorm:ℝ) ≤ Z^A :=
    (actual_geometry_norm_caps s R seed K Z ξ A hs hz₁ hz₂ hsource j.1.val 0).2
  have hf := fixed_pair_caps s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹ F
  have hr : ((geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus.absNorm:ℝ) ≤
      fixedPresentationCost*(s.η.modulus.absNorm:ℝ)*(src.C.absNorm:ℝ)^2 := by
    cases reflected
    · exact hf.1
    · exact hf.2
  apply hr.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2)
    (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _))

/-- The polynomial exponents are fixed; only the threshold uses the
original number of slots, support endpoints and original character. -/
theorem eventual_actual_geometry_main_exceptional_admission
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K ξ sigma reserve t : ℝ)
      (hK : 0<K), s.η=η → Fintype.card ι≤N → Endpoints b bs bs s →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → volume s≤Z^(2:ℝ) → sourceRadius s≤Z^(3:ℝ) →
      (R.absNorm:ℝ)≤Z → K≤Z → 0≤ξ → ξ≤1 → 0≤sigma → 0≤reserve →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R s.ν s.W s.P≠0 →
      let u := geometryLowFirstChild reflected s R seed K Z ξ hK bin t q
      let F := frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin q.1.val)) Z ξ
      0<F ∧ F≤Z^(8:ℝ) ∧ sourceRadius u≤Z^(41:ℝ) ∧
      (expandedFactor u.η:ℝ)*(R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm*
        (sourceRadius u)^2*(4*F)≤Z^(41:ℝ) := by
  filter_upwards [eventually_source_caps,
    eventually_ge_atTop (geometry N b bs bs),
    eventually_ge_atTop (η.modulus.absNorm:ℝ),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop (b^(2*N))]
    with Z he hgeom hη hcost hbN
  refine ⟨he.1, ?_⟩
  intro reflected s R seed K ξ sigma reserve t hK hsame hn hend hs hz₁ hz₂ hV hrad hR
    hKZ hξ hξ₁ hsigma hreserve bin q hne u F
  have hz := zero_lt_one.trans he.1
  have hc (i : Fin 5) := (actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hrad q.1.val.1.val i).2
  have hI : ((geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)≤Z^(3:ℝ) := by
    cases reflected
    · exact hc 0
    · exact hc 1
  have hχ := actual_geometry_exceptional_character_cap reflected s R seed K Z ξ 3 hK
    hs hz₁ hz₂ hrad bin q.1.val
  have hχ₈ : (u.η.modulus.absNorm:ℝ)≤Z^(8:ℝ) := by
    change ((geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val).modulus.absNorm:ℝ)≤_
    apply hχ.trans
    rw [hsame]
    calc
      _≤Z*Z*(Z^(3:ℝ))^2 := by gcongr
      _=Z^(8:ℝ) := by
        rw [show (Z^(3:ℝ))^2=Z^(3:ℝ)*Z^(3:ℝ) by ring]
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        conv_lhs => arg 1; arg 2; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hI₈ : ((R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)≤Z^(8:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _≤Z*Z^(3:ℝ) := mul_le_mul hR hI (Nat.cast_nonneg _) hz.le
      _=Z^(4:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]
        norm_num
      _≤_ := Real.rpow_le_rpow_of_exponent_le he.1.le (by norm_num)
  have hu₃ : sourceRadius u≤Z^(3:ℝ) := by
    have hh := actual_common_child_source_cap N b bs hb hbs s hn hend
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R q.2
      (geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val) t hne
    have hnI := norm_ge_one _ (allocation_ne s _ q.2)
    calc
      _≤geometry N b bs bs*volume s := hh.trans (div_le_self
        (mul_nonneg ((geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)) (volume_pos s).le) hnI)
      _≤Z*Z^(2:ℝ) := mul_le_mul hgeom hV (volume_pos s).le hz.le
      _=Z^(3:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]; norm_num
  have hu₀ : 0≤sourceRadius u := by
    exact (radius_bound N b bs bs hb hbs hbs u ((live_card_le q.2.val).trans hn)
      (endpoints_child b bs bs s hend _ R q.2 _ t)).1
  have hFpos : 0<F := by
    let hl := geometryFirstLabel s R seed K Z ξ hK bin q.1.val
    have hr := first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hz hl
    change 0 < (b^N*volume s/((if reflected then hl.1.2 else hl.1.1).absNorm:ℝ))^2 /
      firstMainRadius reflected K (volume s) Z ξ sigma reserve hl * Z^(ξ/2)
    have hn : 0 < ((if reflected then hl.1.2 else hl.1.1).absNorm:ℝ) := by
      cases reflected
      · exact norm_pos _ (geometryFirstSource s R seed K Z ξ hK bin q.1.val.1).hC.1
      · exact norm_pos _ (geometryFirstSource s R seed K Z ξ hK bin q.1.val.1).hD.1
    have hbpos := zero_lt_one.trans_le hb
    have hv := volume_pos s
    positivity
  have hF₈ : F≤Z^(8:ℝ) := by
    have hf := actual_geometry_main_cutoff_cap reflected s R seed K Z ξ sigma reserve b 1 N
      hK he.1 (zero_lt_one.trans_le hb) hξ hsigma hreserve
      (by simpa using hKZ) bin q.1.val
    apply hf.trans
    calc
      _≤Z*Z^(1+ξ/2) := mul_le_mul_of_nonneg_right hbN (Real.rpow_nonneg hz.le _)
      _=Z^(1+(1+ξ/2)) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]
      _≤_ := Real.rpow_le_rpow_of_exponent_le he.1.le (by linarith)
  have hu₈ := hu₃.trans (Real.rpow_le_rpow_of_exponent_le he.1.le (show (3:ℝ)≤8 by norm_num))
  have hh := he.2 u.η (R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val)
    (sourceRadius u) F 8 (by norm_num) hu₀ hFpos.le hχ₈ hI₈ hu₈ hF₈
  have hnum : (5*(8:ℝ)+1)=(41:ℝ) := by norm_num
  rw [hnum] at hh
  exact ⟨hFpos,hF₈,hh.1,hh.2⟩

omit [DecidableEq ι] in
/-- This is the minimum gate for the literal retained main source, with
its actual selected ideal and fixed original character. -/
theorem eventual_actual_geometry_main_exceptional_minimum
    (η : Character) (loss : ℝ) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K ξ t : ℝ) (hK : 0<K),
      s.η=η → K≤Z → Z^(1/4:ℝ)≤s.X₁ → Z^(1/4:ℝ)≤s.X₂ →
      Z^(1/4:ℝ)≤s.Y₁ → Z^(1/4:ℝ)≤s.Y₂ →
      ∀ (bin : ℤ×(Fin 5→ℤ)) (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
        Real.logb Z ((geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)-loss ≤
      inputCap Z (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q) := by
  filter_upwards [eventual_fixed_character_plain_loss η loss hloss] with Z hh
  refine ⟨hh.1, ?_⟩
  intro reflected s R seed K ξ t hK hη hKZ hx₁ hx₂ hy₁ hy₂ bin q
  have hk : Real.logb Z K≤1 := by
    have hp : K≤Z^(1:ℝ) := by simpa using hKZ
    exact (Real.logb_le_iff_le_rpow hh.1 hK).mpr hp
  have hL : (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-loss≤1/4 := by
    rw [hη]
    linarith [hh.2]
  have hp := Real.rpow_le_rpow_of_exponent_le hh.1.le hL
  exact actual_child_exceptional_reference_range s _ R q.2 _ t Z _ loss hh.1
    (hp.trans hx₁) (hp.trans hx₂) (hp.trans hy₁) (hp.trans hy₂)

omit [DecidableEq ι] in
/-- Prime extraction subtracts exactly its retained power from the plain
minimum; the source remains the full padded twice-child dictionary. -/
theorem actual_geometry_error_exceptional_minimum
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Z M ξ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (hp : p≠0) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v L loss : ℝ)
    (hL : L-loss≤1/4)
    (hx₁ : Z^(1/4:ℝ)≤s.X₁) (hx₂ : Z^(1/4:ℝ)≤s.X₂)
    (hy₁ : Z^(1/4:ℝ)≤s.Y₁) (hy₂ : Z^(1/4:ℝ)≤s.Y₂) :
    L-Real.logb Z ((geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val).absNorm:ℝ)-
      ((errorIndex i+1:ℕ):ℝ)*Real.logb Z ((Ideal.span {p}).absNorm:ℝ)-loss ≤
    inputCap Z (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v) := by
  have hh := Real.rpow_le_rpow_of_exponent_le hZ.le hL
  exact actual_twice_exceptional_reference_range s _ R q.2 _ t (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) _ (errorActiveAllocation _ _ Bp) υ v Z L loss hZ
    (hh.trans hx₁) (hh.trans hx₂) (hh.trans hy₁) (hh.trans hy₂)

/-- Literal error Fourier admission is obtained from the actual first-label
support and the original volume. No error energy estimate is a premise. -/
theorem eventual_actual_geometry_error_fourier_admission
    (N : ℕ) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (amp ξ reserve _t : ℝ)
      (hZ : 1<Z), Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      sourceRadius s≤Z^(3:ℝ) → |Real.logb Z (volume s)|≤3 →
      0≤amp → amp≤1 → 0≤ξ → ξ≤1 → 0≤reserve → frequencyLoss Z 32 ξ+reserve≤3 →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
        (p : O) (_hp : p≠0) (i : Fin 3),
      0<frequencyRadius (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i) Z ξ ∧
      frequencyRadius (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i) Z ξ≤Z^(24:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop (b^N)] with Z hZ hbZ
  refine ⟨hZ, ?_⟩
  intro reflected s R seed amp ξ reserve t hZ' hs hz₁ hz₂ hsource hV ha ha₁ hξ hξ₁ hr hω bin q p hp i
  let l := geometryFirstLabel s R seed (Z^(1:ℝ)) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val
  let src := geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val.1
  have hcaps := actual_geometry_error_tail_label_caps s R seed 1 Z ξ 3 hZ'
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) hs hz₁ hz₂ hsource bin q.1.val
  have hk : 1≤errorIndex i+1 := Nat.succ_le_succ (Nat.zero_le _)
  have hbox := actual_error_radius_box reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.C src.D=>P.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported _ _ src.hC _).1 src.sameSupport
    Z 1 (volume s) amp (frequencyLoss Z 32 ξ) reserve 3 hZ' (volume_pos s)
    (by norm_num) (by norm_num) (by norm_num) ha (by linarith)
    (frequencyLoss_nonneg Z 32 ξ hZ' (by norm_num) hξ) hr hω hV
    hcaps.1 hcaps.2.1 hcaps.2.2.1 hcaps.2.2.2 p hp (errorIndex i+1) hk
  let rad := geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ' bin q p i
  have hrad : Z^(-15:ℝ)≤rad := by
    have hexp : (-5:ℝ)*3=(-15:ℝ) := by norm_num
    rw [hexp] at hbox
    change Z^(-15:ℝ)≤geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ' bin q p i
    unfold geometryErrorSourceRadius
    rw [actual_geometry_error_tail_radius]
    exact hbox.1
  have hradpos := actual_geometry_error_source_radius_pos reflected s R seed Z 1 amp ξ reserve hZ' bin q p i
  have hI := norm_ge_one _ (allocation_ne s _ q.2)
  have hpN := norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)
  have hpN' : (1:ℝ)≤(normValue p)^(errorIndex i+1) := by
    exact one_le_pow₀ hpN
  have hvol : volume s≤Z^(3:ℝ) :=
    (Real.logb_le_iff_le_rpow hZ' (volume_pos s)).mp (abs_le.mp hV).2
  have hnum : b^N*volume s/
      (((geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val).absNorm:ℝ)*(normValue p)^(errorIndex i+1))≤Z^(4:ℝ) := by
    calc
      _≤b^N*volume s := div_le_self (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le)
        (one_le_mul_of_one_le_of_one_le hI hpN')
      _≤Z*Z^(3:ℝ) := mul_le_mul hbZ hvol (volume_pos s).le (by linarith)
      _=Z^(4:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add (zero_lt_one.trans hZ')]; norm_num
  have hnumpos : 0<b^N*volume s/
      (((geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val).absNorm:ℝ)*(normValue p)^(errorIndex i+1)) := by
    have hi0 := zero_lt_one.trans_le hI
    have hp0 := zero_lt_one.trans_le hpN'
    have hbpos := zero_lt_one.trans_le hb
    have hv := volume_pos s
    positivity
  have hT : geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ' bin q p i≤Z^(23:ℝ) := by
    unfold geometryErrorFourierScale
    calc
      _≤(Z^(4:ℝ))^2/Z^(-15:ℝ) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hnumpos.le hnum 2)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) hrad
      _=Z^(23:ℝ) := by
        rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ').le,←Real.rpow_sub (zero_lt_one.trans hZ')]
        norm_num
  refine ⟨?_, ?_⟩
  · change 0 < geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ' bin q p i*Z^(ξ/2)
    exact mul_pos (div_pos (pow_pos hnumpos _) hradpos)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _)
  · unfold frequencyRadius
    calc
      _≤Z^(23:ℝ)*Z^(ξ/2) := mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (by linarith) _)
      _=Z^(23+ξ/2) := (Real.rpow_add (zero_lt_one.trans hZ') _ _).symm
      _≤_ := Real.rpow_le_rpow_of_exponent_le hZ'.le (by linarith)

section Prime
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryExceptionalAdmissionPrimeFinite : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ)

theorem actual_geometry_exceptional_prime_cap (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (Z amp : ℝ) (hZ : 1<Z) (ha : amp≤3)
    (p : O) (hp : p∈elementPool (primePool rayM H Sbad (1/2) 1 (Z^amp))) :
    p≠0 ∧ ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ) := by
  have hd := elementPool_data _
    (fun Q hQ=>(primePool_data rayM H Sbad hbad (1/2) 1 (Z^amp) Q hQ).1)
    (fun Q hQ=>(primePool_data rayM H Sbad hbad (1/2) 1 (Z^amp) Q hQ).2) p hp
  have hn := norm_bounds_of_mem_annularPrimeIdeals (show (0:ℝ)≤1/2 by norm_num)
    (show (1/2:ℝ)≤1 by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Finset.mem_sdiff.mp hd.2.1).1
  refine ⟨hd.1.ne_zero, ?_⟩
  have hn' : ((Ideal.span {p}).absNorm:ℝ)≤Z^amp := by simpa using hn.2
  exact hn'.trans (Real.rpow_le_rpow_of_exponent_le hZ.le ha)
end Prime

/-- The saved exceptional source receives the literal lifted active error
allocation. Every remaining premise is an arithmetic support or source receipt. -/
theorem eventual_actual_geometry_error_exceptional_admission
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (amp ξ reserve t : ℝ)
      (hZ : 1<Z), s.η=η → Fintype.card ι≤N → Endpoints b bs bs s →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → volume s≤Z^(2:ℝ) → sourceRadius s≤Z^(3:ℝ) →
      |Real.logb Z (volume s)|≤3 → (R.absNorm:ℝ)≤Z →
      0≤amp → amp≤1 → 0≤ξ → ξ≤1 → 0≤reserve → frequencyLoss Z 32 ξ+reserve≤3 →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀ (p : O) (_hp : p≠0), ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ) →
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I) →
      ∀ (i : Fin 3)
        (Bp : actualAllocations (activeInput
          (geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
              ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (χ : RayCharacter) (v : ℝ),
      υ.modulus.absNorm≤radicalBound (childCharacter
        (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) χ)
          fixedBadMask p (errorMovingExponent (errorIndex i)) →
      let u := geometryErrorChild reflected s R seed Z 1 ξ t hZ bin q p i Bp υ v
      let F := frequencyRadius (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i) Z ξ
      0<F ∧ F≤Z^(25:ℝ) ∧ sourceRadius u≤Z^(126:ℝ) ∧
      (expandedFactor u.η:ℝ)*
        ((R*geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)).absNorm*
        (sourceRadius u)^2*(4*F)≤Z^(126:ℝ) := by
  filter_upwards [eventually_source_caps,
    eventual_actual_geometry_error_fourier_admission (ι:=ι) N b hb,
    eventually_ge_atTop (geometry N b bs bs), eventually_ge_atTop (η.modulus.absNorm:ℝ),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop rayCost]
    with Z he hfourier hgeom hη hcost hray
  refine ⟨he.1, ?_⟩
  intro reflected s R seed amp ξ reserve t hZ hsame hn hend hs hz₁ hz₂ hV hsource hlogV hR
    ha ha₁ hξ hξ₁ hreserve hω bin q hne p hp hpN hslot i Bp υ χ v hυ u F
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let I := geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK bin q.1.val
  let τ := geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hK bin q.1.val
  have hz := zero_lt_one.trans hZ
  have hc := actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂ hsource q.1.val.1.val
  have hI : (I.absNorm:ℝ)≤Z^(3:ℝ) := by
    cases reflected
    · exact (hc 0).2
    · exact (hc 1).2
  have hτ := actual_geometry_exceptional_character_cap reflected s R seed (Z^(1:ℝ)) Z ξ 3 hK
    hs hz₁ hz₂ hsource bin q.1.val
  have hτ₈ : (τ.modulus.absNorm:ℝ)≤Z^(8:ℝ) := by
    apply hτ.trans
    rw [hsame]
    calc
      _≤Z*Z*(Z^(3:ℝ))^2 := by gcongr
      _=Z^(8:ℝ) := by
        rw [show (Z^(3:ℝ))^2=Z^(3:ℝ)*Z^(3:ℝ) by ring]
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        conv_lhs => arg 1; arg 2; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hυ₁₂ : (u.η.modulus.absNorm:ℝ)≤Z^(12:ℝ) := by
    have hh := radical_once_cap τ υ χ p hp (errorMovingExponent (errorIndex i)) hυ
    change (υ.modulus.absNorm:ℝ)≤_
    apply hh.trans
    calc
      _≤Z*Z^(8:ℝ)*Z^(3:ℝ) := by gcongr
      _=Z^(12:ℝ) := by
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hk₇ : errorIndex i+1≤7 := by rcases error_extracted_index_cases i with h|h|h <;> omega
  have hp₇ : ((Ideal.span {p}).absNorm:ℝ)^(errorIndex i+1)≤Z^(21:ℝ) := by
    calc
      _≤(Z^(3:ℝ))^(errorIndex i+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hpN _
      _≤(Z^(3:ℝ))^7 := pow_le_pow_right₀ (Real.one_le_rpow hZ.le (by norm_num)) hk₇
      _=Z^(21:ℝ) := by rw [←Real.rpow_mul_natCast hz.le]; norm_num
  have hpuncture : (((R*I)*(Ideal.span {p})^(errorIndex i+1)).absNorm:ℝ)≤Z^(25:ℝ) := by
    rw [map_mul,map_mul,map_pow,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow]
    calc
      _≤(Z*Z^(3:ℝ))*Z^(21:ℝ) := by gcongr
      _=Z^(25:ℝ) := by
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hcchild := twice_caps N b bs bs hb hbs hbs s hn hend I R q.2 τ t hne
    (Ideal.span {p}) (Ideal.span_singleton_eq_bot.not.mpr hp) (errorIndex i+1) hslot
    (errorActiveAllocation _ _ Bp) υ v
  have hrad : sourceRadius u≤Z^(3:ℝ) := by
    have hh : sourceRadius u≤geometry N b bs bs*volume s/
        ((I.absNorm:ℝ)*((Ideal.span {p}).absNorm:ℝ)^(errorIndex i+1)) := by
      convert hcchild.2.2.2 using 1
      · rfl
      · simp only [CenteredMomentAmplificationChildInput.volume,mul_div_assoc]
    have hden := one_le_mul_of_one_le_of_one_le (norm_ge_one I (allocation_ne s I q.2))
      (one_le_pow₀ (n:=errorIndex i+1) (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)))
    calc
      _≤geometry N b bs bs*volume s := hh.trans (div_le_self
        (mul_nonneg ((geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)) (volume_pos s).le) hden)
      _≤Z*Z^(2:ℝ) := mul_le_mul hgeom hV (volume_pos s).le hz.le
      _=Z^(3:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]; norm_num
  have hu₀ : 0≤sourceRadius u := by
    have ht := endpoints_child b bs bs s hend I R q.2 τ t
    have htt := endpoints_child b bs bs (child s I R q.2 τ t) ht _ (R*I)
      (errorActiveAllocation _ _ Bp) υ v
    exact (radius_bound N b bs bs hb hbs hbs u
      ((live_card_le (errorActiveAllocation _ _ Bp).val).trans ((live_card_le q.2.val).trans hn)) htt).1
  have hf := hfourier.2 reflected s R seed amp ξ reserve t hZ hs hz₁ hz₂ hsource hlogV
    ha ha₁ hξ hξ₁ hreserve hω bin q p hp i
  have hu₂₅ := hrad.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (3:ℝ)≤25 by norm_num))
  have hυ₂₅ := hυ₁₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (12:ℝ)≤25 by norm_num))
  have hF₂₅ := hf.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (24:ℝ)≤25 by norm_num))
  have hh := he.2 u.η ((R*I)*(Ideal.span {p})^(errorIndex i+1)) (sourceRadius u) F 25
    (by norm_num) hu₀ hf.1.le hυ₂₅ hpuncture hu₂₅ hF₂₅
  have hnum : 5*(25:ℝ)+1=126 := by norm_num
  rw [hnum] at hh
  exact ⟨hf.1,hF₂₅,hh.1,hh.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_exceptional_plain_minimum
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_fixed_character_plain_loss
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_exceptional_character_cap
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_main_exceptional_admission

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_main_exceptional_minimum
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_error_exceptional_minimum
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_error_fourier_admission

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_exceptional_prime_cap
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_error_exceptional_admission
