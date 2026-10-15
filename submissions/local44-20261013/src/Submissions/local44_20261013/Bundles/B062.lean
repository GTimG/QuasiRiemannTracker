/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B001
import Submissions.local44_20261013.Bundles.B026
import Submissions.local44_20261013.Bundles.B053
import Submissions.local44_20261013.Bundles.B059
import Submissions.local44_20261013.Bundles.B060
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

/- BEGIN ORIGINAL MODULE Analytic.JointCommonVolume ; sha256 9047b1590decc13beeb20759b23eedf2781776160eeb9badf43faa41eee3ac4f -/
section



/-! Literal common-volume loss on nonzero source allocations. The only
extra factor is the fixed support constant of the original slots. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentAmplificationChildSourceCaps
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_second_common_volume_le (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0) :
    secondCommonVolume s C B ≤
      (max 1 s.upper)^Fintype.card ι*volume s.toData/(C.absNorm : ℝ) := by
  exact common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _)
    s le_rfl (le_max_right _ _) C R B s.η s.t hne

theorem actual_second_common_volume_log (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (secondCommonVolume s C B) ≤
      Real.logb Z (volume s.toData)-Real.logb Z (C.absNorm : ℝ)+
        (Fintype.card ι : ℝ)*Real.logb Z (max 1 s.upper) := by
  have hN : (0 : ℝ) < C.absNorm :=
    zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B))
  have hb : 0 < max 1 s.upper := zero_lt_one.trans_le (le_max_left _ _)
  have hv := volume_pos s.toData
  have hh := Real.logb_le_logb_of_le hZ (secondCommonVolume_pos s C B)
    (actual_second_common_volume_le s C R B hne)
  rw [Real.logb_div (mul_pos (pow_pos hb _) hv).ne' hN.ne',
    Real.logb_mul (pow_pos hb _).ne' hv.ne',Real.logb_pow] at hh
  linarith

theorem actual_second_common_volume_exponent (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z A c loss : ℝ) (hZ : 1 < Z)
    (hv : volume s.toData ≤ Z^A) (hC : (C.absNorm : ℝ) = Z^c)
    (hprofile : (max 1 s.upper)^Fintype.card ι ≤ Z^loss) :
    Real.logb Z (secondCommonVolume s C B) ≤ A-c+loss := by
  have hz := zero_lt_one.trans hZ
  have hV := volume_pos s.toData
  have hCpos := Real.rpow_pos_of_pos hz c
  have hbound := actual_second_common_volume_le s C R B hne
  rw [hC] at hbound
  have hh : secondCommonVolume s C B ≤ Z^(A-c+loss) := by
    apply hbound.trans
    calc
      _ ≤ Z^loss*Z^A/Z^c := by gcongr
      _ = _ := by
        rw [←Real.rpow_add hz,←Real.rpow_sub hz]
        congr 1
        ring
  have hl := Real.logb_le_logb_of_le hZ (secondCommonVolume_pos s C B) hh
  simpa only [Real.logb_rpow hz hZ.ne'] using hl

#print axioms actual_second_common_volume_le
#print axioms actual_second_common_volume_log
#print axioms actual_second_common_volume_exponent
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonVolume -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalLocalContribution ; sha256 9ab9a4326b8e81d1476ea2134c80c7ccece5b932f39b7caf9f28367c61b20a8b -/
section


/-! Actual exceptional first children, with source-derived normalization,
profile control and the local negative exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstChildProfileControl CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondExceptionalUniformSource CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondEnergySplit
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open ConcretePrimeRowBridge RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointExceptionalLocalDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance jointExceptionalLocalDecEq2 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

lemma normalized_exceptional_allocation_power
    (energy coeff V q NC seed Z allow ε γ B saving : ℝ)
    (hZ : 1 < Z) (hcoeff : 0 ≤ coeff) (hV : 0 < V) (hq : 0 < q)
    (hNC : 0 < NC) (hseed : 0 ≤ seed) (hε : 0 ≤ ε)
    (hcap : NC ≤ Z^B) (hbudget : B*ε+γ ≤ -saving)
    (he : energy ≤ coeff*NC^(ε-1)*(q*(V/NC)*Z^allow)*Z^γ/seed) :
    energy/(q*(V/NC^2)*Z^allow) ≤ coeff*Z^(-saving)/seed := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have href : 0 < q*(V/NC^2)*Z^allow := by positivity
  have hh := div_le_div_of_nonneg_right he href.le
  apply hh.trans
  have hpow : NC^ε*Z^γ ≤ Z^(-saving) := by
    calc
      _ ≤ (Z^B)^ε*Z^γ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hNC.le hcap hε) (Real.rpow_nonneg hz.le _)
      _ = Z^(B*ε+γ) := by rw [←Real.rpow_mul hz.le,←Real.rpow_add hz]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hbudget
  calc
    _ = (coeff/seed)*(NC^ε*Z^γ) := by
      rw [Real.rpow_sub hNC,Real.rpow_one]
      field_simp
      <;> ring
    _ ≤ (coeff/seed)*Z^(-saving) :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg hcoeff hseed)
    _ = _ := by ring


/-- A fixed negative reserve for the literal allocated exceptional contribution.
All profile constants are selected before the original first labels. -/
theorem actual_local_main_exceptional_contribution
    {Slot : Type*} [Fintype Slot]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (lo hi : Slot → ℝ) (b : ℝ) (hb : 1 ≤ b) (Bcap Bfirst : ℝ)
    (hBcap : 0 ≤ Bcap) (hBfirst : 0 ≤ Bfirst) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
      ∃ Cfixed : ℝ, 0 < Cfixed ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input Slot) (p : Profiles wlo whi),
      (∀ i, s.lo i = lo i) → (∀ i, s.hi i = hi i) →
      s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
      ∀ (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C = primeSupport D →
      ∀ U : Finset (CommonIndex C D),
      E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U} →
      ∀ (K omega M : ℝ), 0 < K →
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D} →
      ∀ (Rmask seed : Ideal O) (t : ℝ),
      s.upper ≤ b →
      1 ≤ M → M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M →
      (C.absNorm : ℝ) ≤ Z^Bfirst → omega ≤ 1/100 →
      Z^(M/4) ≤ s.X₁ → Z^(M/4) ≤ s.X₂ → Z^(M/4) ≤ s.Y₁ → Z^(M/4) ≤ s.Y₂ →
      Rmask ≠ 0 → Squarefree seed → seed ≠ 0 →
      let V := CenteredMomentAmplificationChildInput.volume s
      let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
        (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
      (∀ B : actualAllocations s.pools (commonPart C D),
        frozenCoefficient B.val (commonPart C D) Rmask s.ν s.W s.P ≠ 0 →
        let d := child s (commonPart C D) Rmask B τ t
        (∀ i, 1 ≤ d.P i) ∧ 0 ≤ sourceRadius d ∧ sourceRadius d ≤ Z^Bcap) →
      (τ.modulus.absNorm : ℝ) ≤ Z^Bcap → ((Rmask*commonPart C D).absNorm : ℝ) ≤ Z^Bcap →
      ∀ (ray : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
      ∀ Tsec ξ : ℝ, 0 < frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ ≤ Z^Bcap →
      allocatedMainExceptionalEnergy s (commonPart C D) Rmask seed τ t b Z Q ray m Rmain Tsec ξ /
        ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ)^2)*Z^(allowance C D Z)) ≤
        Cfixed*p.control S^2*(1+‖t‖)^(2*J)*mass s^6*
          Z^(-2/25 : ℝ)/(seed.absNorm : ℝ) := by
  let θ := 1/(10000*(5*Bcap+1))
  let εalloc := 1/(1000*(Bfirst+1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hεalloc : 0 < εalloc := by dsimp [εalloc]; positivity
  obtain ⟨J,S,hS,hsource⟩ := actual_local_main_exceptional_allocated
    wlo whi hwlo hwhi lo hi b hb (1/10000) (1/10000) θ Bcap εalloc
    (by norm_num) (by norm_num) hθ hBcap hεalloc
  refine ⟨J,S,hS,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Cfixed,hCfixed,hsource⟩ := hsource Q hQ hQt hQ72
  refine ⟨Cfixed,hCfixed,?_⟩
  filter_upwards [hsource] with Z hsource
  refine ⟨hsource.1,?_⟩
  intro s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
    Rmask seed t hupper hM hwidth hvolume hCcap homega hX₁ hX₂ hY₁ hY₂
    hRmask hseed hseed0 V Rmain hcaps hτ hRnorm ray m hm hml hm2 Tsec ξ hfreq hfreqcap
  have hh := hsource.2 s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
    Rmask seed t hupper hM hwidth hvolume hX₁ hX₂ hY₁ hY₂ hRmask hseed hseed0
    hcaps hτ hRnorm ray m hm hml hm2 Tsec ξ hfreq hfreqcap
  have heps : Bfirst*εalloc ≤ 1/1000 := by
    dsimp [εalloc]
    rw [mul_one_div]
    apply (div_le_iff₀ (show 0 < 1000*(Bfirst+1) by positivity)).mpr
    nlinarith
  have htheta : 2*(5*Bcap+1)*θ = 1/5000 := by
    dsimp [θ]
    field_simp
    <;> ring
  have hbudget : Bfirst*εalloc+
      (2*(1/10000)+2*(1/10000)+2*(5*Bcap+1)*θ-93/1000+5*omega/6) ≤ -(2/25 : ℝ) := by
    rw [htheta]
    linarith
  simpa only [neg_div] using normalized_exceptional_allocation_power _
    (Cfixed*p.control S^2*(1+‖t‖)^(2*J)*mass s^6) V
    (τ.modulus.absNorm : ℝ) (C.absNorm : ℝ) (seed.absNorm : ℝ) Z (allowance C D Z)
    εalloc _ Bfirst (2/25) hsource.1 (by positivity)
    (CenteredMomentAmplificationChildInput.volume_pos s) (norm_pos _ τ.modulus_ne_bot)
    (norm_pos _ hC.1) (Nat.cast_nonneg _) hεalloc.le hCcap hbudget hh

#print axioms actual_local_main_exceptional_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalLocalContribution -/

/- BEGIN ORIGINAL MODULE Analytic.JointFourierPolynomial ; sha256 5504d59c38e5d3e3deafe320d0b21d7023cd938892b2bc9d663a72e28ee5128a -/
section


/-! A bounded three-variable Fourier region and a coarse global bound
give a global polynomial majorant. Its degree is fixed before the scale. -/
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.Local44.Analytic

theorem three_variable_polynomial_extension (ν B target : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∀ (Z Ch Ct : ℝ), 1 ≤ Z → 0 ≤ Ch → 0 ≤ Ct →
      ∀ F : ℝ → ℝ → ℝ → ℝ,
      (∀ θ u v, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν → F θ u v ≤ Ch*Z^target) →
      (∀ θ u v, F θ u v ≤ Ct*Z^B) →
      ∀ θ u v, F θ u v ≤ (Ch+Ct)*Z^target*(1+‖θ‖)^N*(1+‖u‖)^N*(1+‖v‖)^N := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((B-target)/ν)
  have hbudget : B ≤ target+ν*(N : ℝ) := by
    have hh := (div_lt_iff₀ hν).mp hN
    nlinarith
  refine ⟨N,?_⟩
  intro Z Ch Ct hZ hCh hCt F hlocal hcoarse θ u v
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hpow (q : ℝ) (hq : Z^ν < ‖q‖) : Z^B ≤ Z^target*(1+‖q‖)^N := by
    calc
      _ ≤ Z^(target+ν*(N : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hbudget
      _ = Z^target*(Z^ν)^N := by
        rw [Real.rpow_add hZpos,Real.rpow_mul hZpos.le,Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg hZpos.le _) (by linarith) N) (by positivity)
  have hone (q : ℝ) : 1 ≤ (1+‖q‖)^N := one_le_pow₀ (by linarith [norm_nonneg q])
  have hpos (q : ℝ) : 0 ≤ (1+‖q‖)^N := by positivity
  let product := (1+‖θ‖)^N*(1+‖u‖)^N*(1+‖v‖)^N
  have hpone : 1 ≤ product := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hone θ) (hone u)) (hone v)
  have hpθ : (1+‖θ‖)^N ≤ product :=
    (le_mul_of_one_le_right (hpos θ) (hone u)).trans
      (le_mul_of_one_le_right (mul_nonneg (hpos θ) (hpos u)) (hone v))
  have hpu : (1+‖u‖)^N ≤ product :=
    (le_mul_of_one_le_left (hpos u) (hone θ)).trans
      (le_mul_of_one_le_right (mul_nonneg (hpos θ) (hpos u)) (hone v))
  have hpv : (1+‖v‖)^N ≤ product := le_mul_of_one_le_left (hpos v)
    (one_le_mul_of_one_le_of_one_le (hone θ) (hone u))
  have htail (q : ℝ) (hq : Z^ν < ‖q‖) (hqp : (1+‖q‖)^N ≤ product) :
      F θ u v ≤ (Ch+Ct)*Z^target*product := by
    calc
      _ ≤ Ct*Z^B := hcoarse θ u v
      _ ≤ Ct*(Z^target*(1+‖q‖)^N) := mul_le_mul_of_nonneg_left (hpow q hq) hCt
      _ ≤ (Ch+Ct)*(Z^target*product) := mul_le_mul
        (by linarith) (mul_le_mul_of_nonneg_left hqp (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  have hh : F θ u v ≤ (Ch+Ct)*Z^target*product := by
    by_cases hθ : ‖θ‖ ≤ Z^ν
    · by_cases hu : ‖u‖ ≤ Z^ν
      · by_cases hv : ‖v‖ ≤ Z^ν
        · exact (hlocal θ u v hθ hu hv).trans
            ((mul_le_mul_of_nonneg_right (by linarith : Ch ≤ Ch+Ct) (by positivity)).trans
              (le_mul_of_one_le_right (by positivity) hpone))
        · exact htail v (lt_of_not_ge hv) hpv
      · exact htail u (lt_of_not_ge hu) hpu
    · exact htail θ (lt_of_not_ge hθ) hpθ
  convert hh using 1
  dsimp [product]
  ring

theorem three_variable_polynomial_extension_lower (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∀ target : ℝ, lower ≤ target → ∀ (Z Ch Ct : ℝ), 1 ≤ Z → 0 ≤ Ch → 0 ≤ Ct →
      ∀ F : ℝ → ℝ → ℝ → ℝ,
      (∀ θ u v, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν → F θ u v ≤ Ch*Z^target) →
      (∀ θ u v, F θ u v ≤ Ct*Z^B) →
      ∀ θ u v, F θ u v ≤ (Ch+Ct)*Z^target*(1+‖θ‖)^N*(1+‖u‖)^N*(1+‖v‖)^N := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((B-lower)/ν)
  refine ⟨N,?_⟩
  intro target htarget
  have hbudget : B ≤ target+ν*(N : ℝ) := by
    have hh := (div_lt_iff₀ hν).mp hN
    nlinarith
  intro Z Ch Ct hZ hCh hCt F hlocal hcoarse θ u v
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hpow (q : ℝ) (hq : Z^ν < ‖q‖) : Z^B ≤ Z^target*(1+‖q‖)^N := by
    calc
      _ ≤ Z^(target+ν*(N : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hbudget
      _ = Z^target*(Z^ν)^N := by
        rw [Real.rpow_add hZpos,Real.rpow_mul hZpos.le,Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg hZpos.le _) (by linarith) N) (by positivity)
  have hone (q : ℝ) : 1 ≤ (1+‖q‖)^N := one_le_pow₀ (by linarith [norm_nonneg q])
  have hpos (q : ℝ) : 0 ≤ (1+‖q‖)^N := by positivity
  let product := (1+‖θ‖)^N*(1+‖u‖)^N*(1+‖v‖)^N
  have hpone : 1 ≤ product := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hone θ) (hone u)) (hone v)
  have hpθ : (1+‖θ‖)^N ≤ product :=
    (le_mul_of_one_le_right (hpos θ) (hone u)).trans
      (le_mul_of_one_le_right (mul_nonneg (hpos θ) (hpos u)) (hone v))
  have hpu : (1+‖u‖)^N ≤ product :=
    (le_mul_of_one_le_left (hpos u) (hone θ)).trans
      (le_mul_of_one_le_right (mul_nonneg (hpos θ) (hpos u)) (hone v))
  have hpv : (1+‖v‖)^N ≤ product := le_mul_of_one_le_left (hpos v)
    (one_le_mul_of_one_le_of_one_le (hone θ) (hone u))
  have htail (q : ℝ) (hq : Z^ν < ‖q‖) (hqp : (1+‖q‖)^N ≤ product) :
      F θ u v ≤ (Ch+Ct)*Z^target*product := by
    calc
      _ ≤ Ct*Z^B := hcoarse θ u v
      _ ≤ Ct*(Z^target*(1+‖q‖)^N) := mul_le_mul_of_nonneg_left (hpow q hq) hCt
      _ ≤ (Ch+Ct)*(Z^target*product) := mul_le_mul
        (by linarith) (mul_le_mul_of_nonneg_left hqp (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  have hh : F θ u v ≤ (Ch+Ct)*Z^target*product := by
    by_cases hθ : ‖θ‖ ≤ Z^ν
    · by_cases hu : ‖u‖ ≤ Z^ν
      · by_cases hv : ‖v‖ ≤ Z^ν
        · exact (hlocal θ u v hθ hu hv).trans
            ((mul_le_mul_of_nonneg_right (by linarith : Ch ≤ Ch+Ct) (by positivity)).trans
              (le_mul_of_one_le_right (by positivity) hpone))
        · exact htail v (lt_of_not_ge hv) hpv
      · exact htail u (lt_of_not_ge hu) hpu
    · exact htail θ (lt_of_not_ge hθ) hpθ
  convert hh using 1
  dsimp [product]
  ring

#print axioms three_variable_polynomial_extension
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFourierPolynomial -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLedger ; sha256 86318407f226da8e412cbca33e286c2ae6dff1ccba0c1418967df422ead51fc9 -/
section



/-! Close the actual second-transform outside exponent against the one
joint population/product exponent. The ledger contains no second count of
first labels and no divisibility assumption for the second projector. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open LocalMoment

lemma min_add_positive_difference (c d : ℝ) : min c d+max (c-d) 0 = c := by
  by_cases h : c ≤ d
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]
  · have hd := le_of_not_ge h
    rw [min_eq_right hd, max_eq_left (sub_nonneg.mpr hd)]
    ring

theorem joint_high_full_exponent (δ A c d p R R₀ E Bc L b₂ g₂ t₂ ω loss : ℝ)
    (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4) (hA : A ≤ 883/1000)
    (hp : 0 ≤ p) (hpc : p ≤ c) (hpd : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hE : 0 ≤ E) (hBc : 0 ≤ Bc)
    (hL : L ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (hg₂ : g₂ ≤ b₂) (ht₂ : 0 ≤ t₂) :
    (A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+ω)+
      (unmarkedDensity δ*(1-R-max (c-d) 0+L-6*(3/500))+
        (p-R-E+R₀)+δ*(A-c-b₂)+loss) ≤
      p+A-c+R+E+Bc-144011/54900000+ω+loss := by
  have hres := local_high_ledger_reserve δ A (min c d) (max (c-d) 0) p R R₀ E Bc L b₂ g₂ t₂
    hδ hδ' hA (le_max_right _ _) hp (le_min hpc hpd) hRp hR₀ hE hBc hL hb₂ hg₂ ht₂
  have hc := min_add_positive_difference c d
  rw [hc] at hres
  nlinarith

/-- Once all small losses use at most half the strict reserve, the
normalized high contribution is below its target by a fixed power. -/
theorem joint_high_rpow_bound (Z C Y δ A c d p R R₀ E Bc L b₂ g₂ t₂ ω loss : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4) (hA : A ≤ 883/1000)
    (hp : 0 ≤ p) (hpc : p ≤ c) (hpd : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hE : 0 ≤ E) (hBc : 0 ≤ Bc)
    (hL : L ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (hg₂ : g₂ ≤ b₂) (ht₂ : 0 ≤ t₂)
    (hloss : ω+loss ≤ 144011/109800000)
    (hY : Y ≤ C*Z^(unmarkedDensity δ*(1-R-max (c-d) 0+L-6*(3/500))+
      (p-R-E+R₀)+δ*(A-c-b₂)+loss)) :
    Z^(A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+ω)*Y ≤
      C*Z^(p+A-c+R+E+Bc-144011/109800000) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hpow := joint_high_full_exponent δ A c d p R R₀ E Bc L b₂ g₂ t₂ ω loss
    hδ hδ' hA hp hpc hpd hRp hR₀ hE hBc hL hb₂ hg₂ ht₂
  calc
    _ ≤ Z^(A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+ω)*
        (C*Z^(unmarkedDensity δ*(1-R-max (c-d) 0+L-6*(3/500))+
          (p-R-E+R₀)+δ*(A-c-b₂)+loss)) :=
      mul_le_mul_of_nonneg_left hY (Real.rpow_nonneg hz.le _)
    _ = C*Z^((A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+ω)+
        (unmarkedDensity δ*(1-R-max (c-d) 0+L-6*(3/500))+
          (p-R-E+R₀)+δ*(A-c-b₂)+loss)) := by
      rw [Real.rpow_add hz (A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+ω)
        (unmarkedDensity δ*(1-R-max (c-d) 0+L-6*(3/500))+
          (p-R-E+R₀)+δ*(A-c-b₂)+loss)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC

#print axioms joint_high_full_exponent
#print axioms joint_high_rpow_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLedger -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondFibers ; sha256 2731ec247d25a041b94480d01ab48d55a6221a23152a1645cd03fa4a4f104455 -/
section



/-! The retained X/Y energies become four literal positive-row products.
Their dependent finite fibers retain both common allocations and both
second-projector allocations; zero products are removed exactly. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRowEnergy CenteredMomentCommonAllocationSum CenteredMomentDivisorRetained
local notation "O" => HeckeFamily.O

/-- The two actual comparison rectangles, with all original coefficients. -/
def secondRetainedPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (e : Bool) (z : O) : ℂ :=
  allocatedPositiveRow s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((I.absNorm : ℝ)/s.P i)) s.P L a
    s.W₁ s.W₂ (if e then s.X₁ else s.Y₁) (if e then s.X₂ else s.Y₂)

theorem secondRetainedEnergy_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    secondRetainedEnergy s L a z = ∑ e : Bool, ‖secondRetainedPositive s L a e z‖^2 := by
  simp [Fintype.sum_bool, secondRetainedPositive, secondRetainedEnergy]

theorem secondRetainedEnergy_sqrt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Source ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    Real.sqrt (secondRetainedEnergy s L a z) ≤
      ∑ e : Bool, ‖secondRetainedPositive s L a e z‖ := by
  rw [secondRetainedEnergy_eq_sum, Fintype.sum_bool, Fintype.sum_bool]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (norm_nonneg (secondRetainedPositive s L a true z))
    (norm_nonneg (secondRetainedPositive s L a false z))]

def secondAllocationScalar {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation L (Finset.univ : Finset (κ ⊕ Fin 2))) : ℝ :=
  (1/Real.sqrt (formalReductionFactor L a s.P*formalReductionFactor L b v.P)) *
    (Real.sqrt (secondExtractionNumerator s.M s.b₁ s.b₂ L a) *
      Real.sqrt (secondExtractionNumerator v.M v.b₁ v.b₂ L b))

theorem secondAllocationScalar_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation L (Finset.univ : Finset (κ ⊕ Fin 2))) :
    0 ≤ secondAllocationScalar s v L a b := by
  unfold secondAllocationScalar
  positivity

/-- Exactly four X/Y products suffice for the two retained energies. -/
theorem secondRetainedPair_le_four {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : Data ι) (v : Data κ)
    (L : Ideal O) (z w : O) :
    secondRetainedPairBound s v L z w ≤
      ∑ a ∈ s.toSource.active L, ∑ b ∈ v.toSource.active L,
        ∑ e : Bool, ∑ f : Bool, secondAllocationScalar s v L a b *
          (‖secondRetainedPositive s.toSource L a e z‖ *
            ‖secondRetainedPositive v.toSource L b f w‖) := by
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  have hn₁ : 0 ≤ secondExtractionNumerator s.M s.b₁ s.b₂ L a := by
    unfold secondExtractionNumerator
    positivity
  have hn₂ : 0 ≤ secondExtractionNumerator v.M v.b₁ v.b₂ L b := by
    unfold secondExtractionNumerator
    positivity
  calc
    _ = secondAllocationScalar s v L a b *
        (Real.sqrt (secondRetainedEnergy s.toSource L a z) *
          Real.sqrt (secondRetainedEnergy v.toSource L b w)) := by
      rw [Real.sqrt_mul hn₁, Real.sqrt_mul hn₂]
      unfold secondAllocationScalar
      ring
    _ ≤ secondAllocationScalar s v L a b *
        ((∑ e : Bool, ‖secondRetainedPositive s.toSource L a e z‖) *
          (∑ f : Bool, ‖secondRetainedPositive v.toSource L b f w‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul
        (secondRetainedEnergy_sqrt_le s.toSource L a z)
        (secondRetainedEnergy_sqrt_le v.toSource L b w)
        (Real.sqrt_nonneg _) (by positivity)) (secondAllocationScalar_nonneg s v L a b)
    _ = _ := by simp only [Fintype.sum_bool]; ring

namespace CommonSecondKernelLabel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev LeftSecondAllocation (s : CommonSecondKernelLabel ι) (B : s.LeftAllocation) :=
  Allocation s.projector (Finset.univ :
    Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2))

abbrev RightSecondAllocation (s : CommonSecondKernelLabel ι) (F : s.RightAllocation) :=
  Allocation s.projector (Finset.univ :
    Finset (CenteredMomentCommonProfile.liveIndices F.val ⊕ Fin 2))

/-- A branch consists of two actual common allocations, two second
projector allocations, and the independent X/Y choices. -/
abbrev RetainedFiber (s : CommonSecondKernelLabel ι) :=
  (B : s.LeftAllocation) × (F : s.RightAllocation) ×
    (a : s.LeftSecondAllocation B) × (b : s.RightSecondAllocation F) × (e : Bool) × Bool

def retainedFiber (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) : Finset s.RetainedFiber :=
  Finset.univ.sigma (fun B => Finset.univ.sigma (fun F =>
    ((s.leftData B t₁).toSource.active s.projector).sigma (fun a =>
      ((s.rightData F t₂).toSource.active s.projector).sigma (fun b =>
        (Finset.univ : Finset Bool).sigma (fun e => (Finset.univ : Finset Bool))))))

def fiberWeight (s : CommonSecondKernelLabel ι) (t₁ t₂ H₁ H₂ : ℝ)
    (q : s.RetainedFiber) : ℝ :=
  (‖s.leftWeight q.1 H₁‖*‖s.rightWeight q.2.1 H₂‖) *
    secondAllocationScalar (s.leftData q.1 t₁) (s.rightData q.2.1 t₂) s.projector
      q.2.2.1 q.2.2.2.1

def fiberLeft (s : CommonSecondKernelLabel ι) (t : ℝ) (z : O)
    (q : s.RetainedFiber) : ℂ :=
  secondRetainedPositive (s.leftData q.1 t).toSource s.projector q.2.2.1 q.2.2.2.2.1 z

def fiberRight (s : CommonSecondKernelLabel ι) (t : ℝ) (z : O)
    (q : s.RetainedFiber) : ℂ :=
  secondRetainedPositive (s.rightData q.2.1 t).toSource s.projector q.2.2.2.1 q.2.2.2.2.2 (-z)

def fiberValue (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O)
    (q : s.RetainedFiber) : ℝ := ‖s.fiberLeft t₁ z q‖*‖s.fiberRight t₂ z q‖

def liveRetainedFiber (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O) :
    Finset s.RetainedFiber :=
  (s.retainedFiber t₁ t₂).filter (fun q => s.fiberValue t₁ t₂ z q ≠ 0)

theorem fiberWeight_nonneg (s : CommonSecondKernelLabel ι) (t₁ t₂ H₁ H₂ : ℝ)
    (q : s.RetainedFiber) : 0 ≤ s.fiberWeight t₁ t₂ H₁ H₂ q :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (secondAllocationScalar_nonneg _ _ _ _ _)

theorem fiberValue_nonneg (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O)
    (q : s.RetainedFiber) : 0 ≤ s.fiberValue t₁ t₂ z q :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem liveRetainedFiber_nonzero (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O)
    (q : s.RetainedFiber) (hq : q ∈ s.liveRetainedFiber t₁ t₂ z) :
    s.fiberLeft t₁ z q ≠ 0 ∧ s.fiberRight t₂ z q ≠ 0 := by
  have h := (Finset.mem_filter.mp hq).2
  simpa only [fiberValue, ne_eq, mul_eq_zero, norm_eq_zero, not_or] using h

theorem retainedPair_le_fiber (s : CommonSecondKernelLabel ι)
    (t₁ t₂ : ℝ) (z : O) (H₁ H₂ : ℝ) :
    s.retainedPair t₁ t₂ z H₁ H₂ ≤
      ∑ q ∈ s.retainedFiber t₁ t₂, s.fiberWeight t₁ t₂ H₁ H₂ q*s.fiberValue t₁ t₂ z q := by
  unfold retainedPair
  simp only [retainedFiber, Finset.sum_sigma,
    fiberWeight, fiberValue, fiberLeft, fiberRight]
  apply Finset.sum_le_sum
  intro B hB
  apply Finset.sum_le_sum
  intro F hF
  have hh := mul_le_mul_of_nonneg_left
    (secondRetainedPair_le_four (s.leftData B t₁) (s.rightData F t₂) s.projector z (-z))
    (mul_nonneg (norm_nonneg (s.leftWeight B H₁)) (norm_nonneg (s.rightWeight F H₂)))
  simpa only [Finset.mul_sum, mul_assoc] using hh

theorem retainedPair_le_liveFiber (s : CommonSecondKernelLabel ι)
    (t₁ t₂ : ℝ) (z : O) (H₁ H₂ : ℝ) :
    s.retainedPair t₁ t₂ z H₁ H₂ ≤
      ∑ q ∈ s.liveRetainedFiber t₁ t₂ z,
        s.fiberWeight t₁ t₂ H₁ H₂ q*s.fiberValue t₁ t₂ z q := by
  rw [liveRetainedFiber, Finset.sum_filter]
  convert s.retainedPair_le_fiber t₁ t₂ z H₁ H₂ using 1
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : s.fiberValue t₁ t₂ z q = 0 <;> simp [h]

end CommonSecondKernelLabel
#print axioms secondRetainedPair_le_four
#print axioms CommonSecondKernelLabel.retainedPair_le_liveFiber
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondFibers -/

/- BEGIN ORIGINAL MODULE Analytic.SmallSlotEnergy ; sha256 37e51576a344dc7aad9e4bea0505bd7369f9e932b7be4256ccb9ac5ee4bef52c -/
section




/-! Removing bounded-scale prime slots preserves the literal low-bin row
restriction. This step precedes low-bin removal against the incumbent. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentInductionEnergy CenteredMomentEnergyState CenteredMomentEnergyCapacityRemoval
local notation "O" => HeckeFamily.O

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

theorem positive_row_remove_small_slots (W : Slot → ℝ → ℂ) (A B : Slot → ℝ) (lo hi : ℝ)
    (hA : ∀ j, 0 < A j) (hWs : ∀ j, Function.support (W j) ⊆ Icc (A j) (B j))
    (hW : ∀ j, Continuous (W j)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset Slot) (η : Character) (ν : Slot → Character)
      (m Arow z : O) (P σ v : Slot → ℝ) (t : ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ),
      (∀ j ∈ S, 1 ≤ P j) → (∀ j ∈ S, lo ≤ σ j ∧ σ j ≤ hi) → 0 < X₁ → 0 < X₂ →
      let pool := fun j => primePool M H (B j) (P j)
      let coeff := fun j I => idealCoeff (ν j) I*annularWeight (W j) (P j) (σ j) (v j) I
      ‖positiveSlotRow η m Arow z W₁ W₂ (fun j : S => pool j) (fun j : S => coeff j)
        (fun j : S => P j) t X₁ X₂‖ ≤
      C*‖positiveSlotRow η m Arow z W₁ W₂
        (fun j : ↥(S ∩ largePrimeSlots A B P) => pool j) (fun j : ↥(S ∩ largePrimeSlots A B P) => coeff j)
        (fun j : ↥(S ∩ largePrimeSlots A B P) => P j) t X₁ X₂‖ := by
  obtain ⟨C,hC,hremove⟩ := normalized_prime_slots_remove_small M H W A B lo hi hA hWs hW
  refine ⟨C,hC,?_⟩
  intro S η ν m Arow z P σ v t W₁ W₂ X₁ X₂ hP hσ hX₁ hX₂ pool coeff
  rw [positive_row_normalized_pair (ι := ↥S) η m Arow z W₁ W₂ _ _ _ t X₁ X₂ hX₁ hX₂
    (fun j => zero_le_one.trans (hP j j.property)),
    positive_row_normalized_pair (ι := ↥(S ∩ largePrimeSlots A B P)) η m Arow z W₁ W₂ _ _ _ t X₁ X₂ hX₁ hX₂
    (fun j => zero_le_one.trans (hP j (Finset.mem_inter.mp j.property).1))]
  have hprod (T : Finset Slot) :
      (∏ j : T, CenteredMomentWholeSlotDeletion.normalizedSlot η m Arow z
        (pool j) (coeff j) t (P j)) =
      ∏ j ∈ T, CenteredMomentWholeSlotDeletion.normalizedSlot η m Arow z
        (pool j) (coeff j) t (P j) :=
    Finset.prod_coe_sort T (fun j =>
      CenteredMomentWholeSlotDeletion.normalizedSlot η m Arow z (pool j) (coeff j) t (P j))
  rw [hprod S, hprod (S ∩ largePrimeSlots A B P)]
  simp only [norm_mul]
  have hp := hremove S η ν m Arow z P σ v t hP hσ
  dsimp only at hp
  have hb := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (norm_nonneg ((Real.sqrt X₁ : ℂ)⁻¹*rowTwistedSum η m Arow z W₁ t X₁))
      (norm_nonneg ((Real.sqrt X₂ : ℂ)⁻¹*rowTwistedSum η m Arow z W₂ t X₂)))
  simpa only [norm_mul, mul_assoc, mul_left_comm, mul_comm, pool, coeff] using hb

theorem restricted_energy_remove_small_slots (W : Slot → ℝ → ℂ) (A B : Slot → ℝ) (lo hi : ℝ)
    (hA : ∀ j, 0 < A j) (hWs : ∀ j, Function.support (W j) ⊆ Icc (A j) (B j))
    (hW : ∀ j, Continuous (W j)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Z Bmask radial : ℝ} (s : NaturalState Z Bmask radial)
      (low : O → Prop) (S : Finset Slot) (ν : Slot → Character)
      (P σ v : Slot → ℝ) (t : ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ),
      (∀ j ∈ S, 1 ≤ P j) → (∀ j ∈ S, lo ≤ σ j ∧ σ j ≤ hi) → 0 < X₁ → 0 < X₂ →
      let pool := fun j => primePool M H (B j) (P j)
      let coeff := fun j I => idealCoeff (ν j) I*annularWeight (W j) (P j) (σ j) (v j) I
      energy s.character s.mask 1 t W₁ W₂ (fun j : S => pool j) (fun j : S => coeff j)
        (fun j : S => P j) X₁ X₂ (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      C*energy s.character s.mask 1 t W₁ W₂
        (fun j : ↥(S ∩ largePrimeSlots A B P) => pool j) (fun j : ↥(S ∩ largePrimeSlots A B P) => coeff j)
        (fun j : ↥(S ∩ largePrimeSlots A B P) => P j) X₁ X₂
          (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale := by
  obtain ⟨C,hC,hremove⟩ := positive_row_remove_small_slots M H W A B lo hi hA hWs hW
  refine ⟨C^2, one_le_pow₀ hC, ?_⟩
  intro Z Bmask radial s low S ν P σ v t W₁ W₂ X₁ X₂ hP hσ hX₁ hX₂ pool coeff
  have hsum (T : Finset Slot) := compact_radial_summable
    (fun z => positiveSlotRow s.character s.mask 1 z W₁ W₂
      (fun j : T => pool j) (fun j : T => coeff j) (fun j : T => P j) t X₁ X₂)
    (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale radial
    s.radial.scale_pos s.radial_support
  unfold energy
  rw [← tsum_mul_left]
  apply (hsum S).tsum_le_tsum _ ((hsum (S ∩ largePrimeSlots A B P)).mul_left (C^2))
  intro z
  by_cases hz : s.radial.keep z ∧ low z
  · simp only [hz.1, hz.2, and_self, ite_true]
    have hn := hremove S s.character ν s.mask 1 z P σ v t W₁ W₂ X₁ X₂ hP hσ hX₁ hX₂
    dsimp only at hn
    have hb := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [mul_pow] at hb
    exact (mul_le_mul_of_nonneg_right hb (s.radial.nonneg z)).trans_eq (by
      dsimp only [pool, coeff]
      ring)
  · simp only [hz, ite_false, mul_zero, le_refl]

#print axioms restricted_energy_remove_small_slots
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.SmallSlotEnergy -/
