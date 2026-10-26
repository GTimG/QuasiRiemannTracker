import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorTail
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialSourceReduction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
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

end Affine

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
original number of slots and the support endpoints. The parent's conductor,
puncture and radial scale enter through their polynomial caps. -/
theorem eventual_actual_geometry_main_exceptional_admission
    (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K ξ sigma reserve t : ℝ)
      (hK : 0<K), (s.η.modulus.absNorm:ℝ)≤Z^(2:ℝ) → Fintype.card ι≤N → Endpoints b bs bs s →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → volume s≤Z^(2:ℝ) → sourceRadius s≤Z^(3:ℝ) →
      (R.absNorm:ℝ)≤Z^(20:ℝ) → K≤Z^(2:ℝ) → 0≤ξ → ξ≤1 → 0≤ sigma → 0≤ reserve →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin),
      frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val) R s.ν s.W s.P≠0 →
      let u := geometryLowFirstChild reflected s R seed K Z ξ hK bin t q
      let F := frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin q.1.val)) Z ξ
      0<F ∧ F≤Z^(8:ℝ) ∧ sourceRadius u≤Z^(116:ℝ) ∧
      (expandedFactor u.η:ℝ)*(R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm*
        (sourceRadius u)^2*(4*F)≤Z^(116:ℝ) := by
  filter_upwards [eventually_source_caps,
    eventually_ge_atTop (geometry N b bs bs),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop (b^(2*N))]
    with Z he hgeom hcost hbN
  refine ⟨he.1, ?_⟩
  intro reflected s R seed K ξ sigma reserve t hK hη hn hend hs hz₁ hz₂ hV hrad hR
    hKZ hξ hξ₁ hsigma hreserve bin q hne u F
  have hz := zero_lt_one.trans he.1
  have hc (i : Fin 5) := (actual_geometry_norm_caps s R seed K Z ξ 3 hs hz₁ hz₂ hrad q.1.val.1.val i).2
  have hI : ((geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)≤Z^(3:ℝ) := by
    cases reflected
    · exact hc 0
    · exact hc 1
  have hχ := actual_geometry_exceptional_character_cap reflected s R seed K Z ξ 3 hK
    hs hz₁ hz₂ hrad bin q.1.val
  have hχ₂₃ : (u.η.modulus.absNorm:ℝ)≤Z^(23:ℝ) := by
    change ((geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val).modulus.absNorm:ℝ)≤_
    apply hχ.trans
    calc
      _≤Z*Z^(2:ℝ)*(Z^(3:ℝ))^2 := by gcongr
      _=Z^(9:ℝ) := by
        rw [show (Z^(3:ℝ))^2=Z^(3:ℝ)*Z^(3:ℝ) by ring]
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
      _≤_ := Real.rpow_le_rpow_of_exponent_le he.1.le (by norm_num)
  have hI₂₃ : ((R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val).absNorm:ℝ)≤Z^(23:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _≤Z^(20:ℝ)*Z^(3:ℝ) := mul_le_mul hR hI (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _=Z^(23:ℝ) := by
        rw [←Real.rpow_add hz]
        norm_num
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
  have hu₀ : 0≤ sourceRadius u := by
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
    have hf := actual_geometry_main_cutoff_cap reflected s R seed K Z ξ sigma reserve b 2 N
      hK he.1 (zero_lt_one.trans_le hb) hξ hsigma hreserve hKZ bin q.1.val
    apply hf.trans
    calc
      _≤Z*Z^(2+ξ/2) := mul_le_mul_of_nonneg_right hbN (Real.rpow_nonneg hz.le _)
      _=Z^(1+(2+ξ/2)) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add hz]
      _≤_ := Real.rpow_le_rpow_of_exponent_le he.1.le (by linarith)
  have hu₂₃ := hu₃.trans (Real.rpow_le_rpow_of_exponent_le he.1.le (show (3:ℝ)≤23 by norm_num))
  have hF₂₃ := hF₈.trans (Real.rpow_le_rpow_of_exponent_le he.1.le (show (8:ℝ)≤23 by norm_num))
  have hh := he.2 u.η (R*geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val)
    (sourceRadius u) F 23 (by norm_num) hu₀ hFpos.le hχ₂₃ hI₂₃ hu₂₃ hF₂₃
  have hnum : (5*(23:ℝ)+1)=(116:ℝ) := by norm_num
  rw [hnum] at hh
  exact ⟨hFpos,hF₈,hh.1,hh.2⟩

/-- Literal error Fourier admission is obtained from the actual first-label
support and the original volume. No error energy estimate is a premise. -/
theorem eventual_actual_geometry_error_fourier_admission
    (N : ℕ) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (M amp ξ reserve _t : ℝ)
      (hZ : 1<Z), Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      sourceRadius s≤Z^(3:ℝ) → |Real.logb Z (volume s)|≤3 → 0≤M → M≤2 →
      0≤amp → amp≤1 → 0≤ξ → ξ≤1 → 0≤ reserve → frequencyLoss Z 32 ξ+reserve≤3 →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
        (p : O) (_hp : p≠0) (i : Fin 3),
      0<frequencyRadius (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ bin q p i) Z ξ ∧
      frequencyRadius (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ bin q p i) Z ξ≤Z^(24:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop (b^N)] with Z hZ hbZ
  refine ⟨hZ, ?_⟩
  intro reflected s R seed M amp ξ reserve t hZ' hs hz₁ hz₂ hsource hV hM hM₂ ha ha₁ hξ hξ₁ hr hω bin q p hp i
  let l := geometryFirstLabel s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val.1
  have hcaps := actual_geometry_error_tail_label_caps s R seed M Z ξ 3 hZ'
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) hs hz₁ hz₂ hsource bin q.1.val
  have hk : 1≤errorIndex i+1 := Nat.succ_le_succ (Nat.zero_le _)
  have hbox := actual_error_radius_box reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex src.C src.D=>P.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported _ _ src.hC _).1 src.sameSupport
    Z M (volume s) amp (frequencyLoss Z 32 ξ) reserve 3 hZ' (volume_pos s)
    (by norm_num) hM (by linarith) ha (by linarith)
    (frequencyLoss_nonneg Z 32 ξ hZ' (by norm_num) hξ) hr hω hV
    hcaps.1 hcaps.2.1 hcaps.2.2.1 hcaps.2.2.2 p hp (errorIndex i+1) hk
  let rad := geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ' bin q p i
  have hrad : Z^(-15:ℝ)≤ rad := by
    have hexp : (-5:ℝ)*3=(-15:ℝ) := by norm_num
    rw [hexp] at hbox
    change Z^(-15:ℝ)≤geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ' bin q p i
    unfold geometryErrorSourceRadius
    rw [actual_geometry_error_tail_radius]
    exact hbox.1
  have hradpos := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ' bin q p i
  have hI := norm_ge_one _ (allocation_ne s _ q.2)
  have hpN := norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hp)
  have hpN' : (1:ℝ)≤(normValue p)^(errorIndex i+1) := by
    exact one_le_pow₀ hpN
  have hvol : volume s≤Z^(3:ℝ) :=
    (Real.logb_le_iff_le_rpow hZ' (volume_pos s)).mp (abs_le.mp hV).2
  have hnum : b^N*volume s/
      (((geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val).absNorm:ℝ)*(normValue p)^(errorIndex i+1))≤Z^(4:ℝ) := by
    calc
      _≤b^N*volume s := div_le_self (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le)
        (one_le_mul_of_one_le_of_one_le hI hpN')
      _≤Z*Z^(3:ℝ) := mul_le_mul hbZ hvol (volume_pos s).le (by linarith)
      _=Z^(4:ℝ) := by
        conv_lhs => arg 1; rw [←Real.rpow_one Z]
        rw [←Real.rpow_add (zero_lt_one.trans hZ')]; norm_num
  have hnumpos : 0<b^N*volume s/
      (((geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) bin q.1.val).absNorm:ℝ)*(normValue p)^(errorIndex i+1)) := by
    have hi0 := zero_lt_one.trans_le hI
    have hp0 := zero_lt_one.trans_le hpN'
    have hbpos := zero_lt_one.trans_le hb
    have hv := volume_pos s
    positivity
  have hT : geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ' bin q p i≤Z^(23:ℝ) := by
    unfold geometryErrorFourierScale
    calc
      _≤(Z^(4:ℝ))^2/Z^(-15:ℝ) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hnumpos.le hnum 2)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ') _) hrad
      _=Z^(23:ℝ) := by
        rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ').le,←Real.rpow_sub (zero_lt_one.trans hZ')]
        norm_num
  refine ⟨?_, ?_⟩
  · change 0 < geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ' bin q p i*Z^(ξ/2)
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
    (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ (reflected : Bool) (s : Input ι) (R seed : Ideal O) (M amp ξ reserve t : ℝ)
      (hZ : 1<Z), (s.η.modulus.absNorm:ℝ)≤Z^(2:ℝ) → Fintype.card ι≤N → Endpoints b bs bs s →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → volume s≤Z^(2:ℝ) → sourceRadius s≤Z^(3:ℝ) →
      |Real.logb Z (volume s)|≤3 → (R.absNorm:ℝ)≤Z^(20:ℝ) → 0≤M → M≤2 →
      0≤amp → amp≤1 → 0≤ξ → ξ≤1 → 0≤ reserve → frequencyLoss Z 32 ξ+reserve≤3 →
      ∀ (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀ (p : O) (_hp : p≠0), ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ) →
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I) →
      ∀ (i : Fin 3)
        (Bp : actualAllocations (activeInput
          (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
              ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (χ : RayCharacter) (v : ℝ),
      υ.modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) χ)
          fixedBadMask p (errorMovingExponent (errorIndex i)) →
      let u := geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v
      let F := frequencyRadius (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b N hZ bin q p i) Z ξ
      0<F ∧ F≤Z^(25:ℝ) ∧ sourceRadius u≤Z^(221:ℝ) ∧
      (expandedFactor u.η:ℝ)*
        ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)).absNorm*
        (sourceRadius u)^2*(4*F)≤Z^(221:ℝ) := by
  filter_upwards [eventually_source_caps,
    eventual_actual_geometry_error_fourier_admission (ι:=ι) N b hb,
    eventually_ge_atTop (geometry N b bs bs),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop rayCost]
    with Z he hfourier hgeom hcost hray
  refine ⟨he.1, ?_⟩
  intro reflected s R seed M amp ξ reserve t hZ hη hn hend hs hz₁ hz₂ hV hsource hlogV hR hM hM₂
    ha ha₁ hξ hξ₁ hreserve hω bin q hne p hp hpN hslot i Bp υ χ v hυ u F
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin q.1.val
  have hz := zero_lt_one.trans hZ
  have hc := actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource q.1.val.1.val
  have hI : (I.absNorm:ℝ)≤Z^(3:ℝ) := by
    cases reflected
    · exact (hc 0).2
    · exact (hc 1).2
  have hτ := actual_geometry_exceptional_character_cap reflected s R seed (Z^M) Z ξ 3 hK
    hs hz₁ hz₂ hsource bin q.1.val
  have hτ₉ : (τ.modulus.absNorm:ℝ)≤Z^(9:ℝ) := by
    apply hτ.trans
    calc
      _≤Z*Z^(2:ℝ)*(Z^(3:ℝ))^2 := by gcongr
      _=Z^(9:ℝ) := by
        rw [show (Z^(3:ℝ))^2=Z^(3:ℝ)*Z^(3:ℝ) by ring]
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hυ₁₃ : (u.η.modulus.absNorm:ℝ)≤Z^(13:ℝ) := by
    have hh := radical_once_cap τ υ χ p hp (errorMovingExponent (errorIndex i)) hυ
    change (υ.modulus.absNorm:ℝ)≤_
    apply hh.trans
    calc
      _≤Z*Z^(9:ℝ)*Z^(3:ℝ) := by gcongr
      _=Z^(13:ℝ) := by
        conv_lhs => arg 1; arg 1; rw [←Real.rpow_one Z]
        repeat rw [←Real.rpow_add hz]
        norm_num
  have hk₇ : errorIndex i+1≤7 := by rcases error_extracted_index_cases i with h|h|h <;> omega
  have hp₇ : ((Ideal.span {p}).absNorm:ℝ)^(errorIndex i+1)≤Z^(21:ℝ) := by
    calc
      _≤(Z^(3:ℝ))^(errorIndex i+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hpN _
      _≤(Z^(3:ℝ))^7 := pow_le_pow_right₀ (Real.one_le_rpow hZ.le (by norm_num)) hk₇
      _=Z^(21:ℝ) := by rw [←Real.rpow_mul_natCast hz.le]; norm_num
  have hpuncture : (((R*I)*(Ideal.span {p})^(errorIndex i+1)).absNorm:ℝ)≤Z^(44:ℝ) := by
    rw [map_mul,map_mul,map_pow,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow]
    calc
      _≤(Z^(20:ℝ)*Z^(3:ℝ))*Z^(21:ℝ) := by gcongr
      _=Z^(44:ℝ) := by
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
  have hu₀ : 0≤ sourceRadius u := by
    have ht := endpoints_child b bs bs s hend I R q.2 τ t
    have htt := endpoints_child b bs bs (child s I R q.2 τ t) ht _ (R*I)
      (errorActiveAllocation _ _ Bp) υ v
    exact (radius_bound N b bs bs hb hbs hbs u
      ((live_card_le (errorActiveAllocation _ _ Bp).val).trans ((live_card_le q.2.val).trans hn)) htt).1
  have hf := hfourier.2 reflected s R seed M amp ξ reserve t hZ hs hz₁ hz₂ hsource hlogV hM hM₂
    ha ha₁ hξ hξ₁ hreserve hω bin q p hp i
  have hu₄₄ := hrad.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (3:ℝ)≤44 by norm_num))
  have hυ₄₄ := hυ₁₃.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (13:ℝ)≤44 by norm_num))
  have hF₂₅ := hf.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (24:ℝ)≤25 by norm_num))
  have hF₄₄ := hf.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (24:ℝ)≤44 by norm_num))
  have hh := he.2 u.η ((R*I)*(Ideal.span {p})^(errorIndex i+1)) (sourceRadius u) F 44
    (by norm_num) hu₀ hf.1.le hυ₄₄ hpuncture hu₄₄ hF₄₄
  have hnum : 5*(44:ℝ)+1=221 := by norm_num
  rw [hnum] at hh
  exact ⟨hf.1,hF₂₅,hh.1,hh.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
