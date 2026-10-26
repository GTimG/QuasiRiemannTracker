import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometryPayment
import Candidate.Cycle63.Physical.SecondZero.Source
import Candidate.Uneven.MainCellGeometry
import Candidate.Uneven.MainZeroScalar
import Candidate.Cycle63.Physical.SecondZero.Caps
import Candidate.Cycle63.Physical.TerminalLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy
import Candidate.Cycle63.Physical.NominalRadius
import Candidate.Cycle63.Physical.InitialMass.SecondHighPayment
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondSplit

/- Original module: Candidate.Uneven.MainZeroRadius. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.MainReconstruction
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentFiniteProfileExceptional
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationErrorEnergy EisensteinSchwartzPoisson
variable {plane : Plane}
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

/-- Actual normalized second-zero source at a physical radius. -/
def radiusTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι)
    (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ‖((K : ℂ)*paperRadialFourier W 0)*
    sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) s.η s.t‖/volume s.toData

lemma radiusTerm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    0 ≤ radiusTerm s R seed W K := div_nonneg (norm_nonneg _) (volume_pos _).le

lemma radiusTerm_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hKL : K ≤ L) : radiusTerm s R seed W K ≤ radiusTerm s R seed W L := by
  have hL : 0 ≤ L := hK.trans hKL
  unfold radiusTerm
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK,abs_of_nonneg hL]
  gcongr
  exact (volume_pos s.toData).le

/-- The side-reference and amplifier normalization is explicit. The nominal
radius gate is geometric, not an assumed estimate for the zero source. -/
theorem actual_main_second_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (lo hi : ℝ), 0 < lo → 0 ≤ hi →
    ∀ (s : Input ι) (p : Profiles lo hi), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a c d Bc Rw E K0 nominalLoss δ reserve B s₀ : ℝ), 1 < Z →
    widthLo ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Sil.Uneven.MainSource.total plane beta → a ≤ M*Sil.Uneven.MainSource.amp plane beta →
    0 ≤ c → 0 ≤ d → 0 ≤ Bc → K0 ≤ 2*A-c-d+Rw+E-M+nominalLoss →
    volume s.toData ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    Z^(-a-(A-c+Rw+E+Bc))*
      radiusTerm s R seed W (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤
    C*zeroControl s p ε*‖paperRadialFourier W 0‖*
      Z^(-M*(227876729/3446640000)+nominalLoss+δ+reserve+ε*B-s₀) := by
  obtain ⟨C,hC,hbound⟩ := actual_second_zero_power N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E
    K0 nominalLoss δ reserve B s₀ hZ hb hM hA ha hc hd hBc hK0 hvol hseedN
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hh := hbound hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z
    (K0+max (d-c) 0+2*(3*a)+δ+reserve) B s₀ hZ.le hvol hseedN
  have hmin : max (d-c) 0-d = -min c d := by
    by_cases h : c ≤ d
    · rw [max_eq_left (sub_nonneg.mpr h),min_eq_left h]; ring
    · rw [max_eq_right (by linarith),min_eq_right (by linarith)]; ring
  have he : -a-(A-c+Rw+E+Bc)+(K0+max (d-c) 0+2*(3*a)+δ+reserve+ε*B-s₀) ≤
      -M*(227876729/3446640000)+nominalLoss+δ+reserve+ε*B-s₀ := by
    have hs := second_zero_excess_bound (plane:=plane) hb hM hA ha hc hd hBc
    linarith
  have hf : 0 ≤ C*zeroControl s p ε*‖paperRadialFourier W 0‖ :=
    mul_nonneg (mul_nonneg hC.le (zeroControl_nonneg _ _ _)) (norm_nonneg _)
  calc
    _ ≤ Z^(-a-(A-c+Rw+E+Bc))*(C*zeroControl s p ε*‖paperRadialFourier W 0‖*
        Z^(K0+max (d-c) 0+2*(3*a)+δ+reserve+ε*B-s₀)) := by
      exact mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le _)
    _ = (C*zeroControl s p ε*‖paperRadialFourier W 0‖)*
        Z^(-a-(A-c+Rw+E+Bc)+(K0+max (d-c) 0+2*(3*a)+δ+reserve+ε*B-s₀)) := by
      rw [Real.rpow_add hz]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le he) hf

/-- Enlarged extracted radii remain below the main radius for every actual
extracted prime power 1, 6, or 7. No source monotonicity is presumed. -/
lemma actual_error_radius_le_main (Z d K0 c a δ reserve : ℝ) (hZ : 1 < Z)
    (ha : 0 ≤ a) (q : O) (hq : q ≠ 0) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    errorCommonRadius Z d K0 c (3*a) δ reserve q k ≤
      mainCommonRadius Z d K0 c (3*a) δ reserve := by
  have hl := Real.logb_nonneg hZ (normValue_ge_one q hq)
  have hm : errorMoving q Z k ≤ 2*errorRemoval q Z k := by
    rcases hk with rfl|rfl|rfl <;> simp [errorMoving,errorRemoval] <;> linarith
  unfold errorCommonRadius mainCommonRadius
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hx := max_le_max_right (0:ℝ) (show d-c-2*errorRemoval q Z k+errorMoving q Z k ≤ d-c by linarith)
  linarith

lemma actual_error_cost_le_one (q : O) (hq : q ≠ 0) (n : ℕ) : localErrorCost q n ≤ 1 := by
  have hq1 := normValue_ge_one q hq
  have hq0 := normValue_pos q hq
  have hi : (normValue q)⁻¹ ≤ 1 := (inv_le_one₀ hq0).mpr hq1
  have hn : 0 ≤ (normValue q)⁻¹ := inv_nonneg.mpr hq0.le
  unfold localErrorCost
  change (if n=5 then (1-(normValue q)⁻¹)^2 else (normValue q)⁻¹) ≤ 1
  split_ifs <;> nlinarith

/-- The literal squared extraction scalar is paid together with its physical
radius, retaining every twice-child coefficient, mask, and height phase. -/
lemma actual_extracted_second_zero_le_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (Z d K0 c a δ reserve : ℝ) (hZ : 1 < Z) (ha : 0 ≤ a)
    (q : O) (hq : q ≠ 0) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    localErrorCost q (k-1)*radiusTerm s R seed W
      (errorCommonRadius Z d K0 c (3*a) δ reserve q k) ≤
      radiusTerm s R seed W (mainCommonRadius Z d K0 c (3*a) δ reserve) := by
  have hrad := actual_error_radius_le_main Z d K0 c a δ reserve hZ ha q hq k hk
  have hp : 0 ≤ errorCommonRadius Z d K0 c (3*a) δ reserve q k :=
    Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  exact (mul_le_of_le_one_left (radiusTerm_nonneg _ _ _ _ _)
    (actual_error_cost_le_one q hq (k-1))).trans (radiusTerm_mono s R seed W hp hrad)


end
end OAI.SevenEighths.MainReconstruction
end

/- Original module: Candidate.Uneven.MainZeroUniform. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.MainReconstruction
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization EisensteinSchwartzPoisson
variable {plane : Plane}
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Fixed envelope chosen before allocations, characters, and all heights. -/
def controlEnvelope (N : ℕ) (Cs bs hi ε : ℝ) : ℝ :=
  4*Cs^(2*N)*(1+bs^N*hi*hi)^(1+ε)

lemma controlEnvelope_pos (N : ℕ) (Cs bs hi ε : ℝ) (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) :
    0 < controlEnvelope N Cs bs hi ε := by
  have hc : 0 < Cs := zero_lt_one.trans_le hCs
  have hb : 0 ≤ bs^N := pow_nonneg (zero_le_one.trans hbs) _
  have hr : 0 < 1+bs^N*hi*hi := by nlinarith [mul_nonneg hb (sq_nonneg hi)]
  unfold controlEnvelope
  exact mul_pos (mul_pos (by norm_num) (pow_pos hc _)) (Real.rpow_pos_of_pos hr _)

lemma zeroControl_fixed {ι : Type*} [Fintype ι] (N : ℕ) (Cs bs ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε)
    (s : Input ι) (hcard : Fintype.card ι ≤ N)
    (hM : ∀ i, s.M i ≤ Cs) (hs : s.upper ≤ bs) {lo hi : ℝ} (p : Profiles lo hi) :
    zeroControl s p ε ≤ controlEnvelope N Cs bs hi ε*(p.control {(0,0)})^2 := by
  have hpc := Profiles.control_nonneg p {(0,0)}
  have hm0 (i : ι) : 0 ≤ s.M i := zero_le_one.trans (s.M_ge_one i)
  have hmp : (∏ i,s.M i) ≤ Cs^N := by
    calc
      _ ≤ ∏ _i : ι,Cs := Finset.prod_le_prod₀ (fun i _ => hm0 i) (fun i _ => hM i)
      _ = Cs^(Fintype.card ι) := by simp
      _ ≤ Cs^N := pow_le_pow_right₀ hCs hcard
  have hhp : (∏ i,max 0 (s.hi i)) ≤ bs^N := by
    calc
      _ ≤ ∏ _i : ι,bs := Finset.prod_le_prod₀ (fun i _ => le_max_left _ _)
        (fun i _ => max_le (zero_le_one.trans hbs) ((s.upper_ge i).trans hs))
      _ = bs^(Fintype.card ι) := by simp
      _ ≤ bs^N := pow_le_pow_right₀ hbs hcard
  have hpr : (1+(∏ i,max 0 (s.hi i))*hi*hi)^(1+ε) ≤ (1+bs^N*hi*hi)^(1+ε) := by
    apply Real.rpow_le_rpow _ _ (by linarith)
    · have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_left 0 (s.hi i))
      nlinarith [mul_nonneg hp (sq_nonneg hi)]
    · have hh := mul_le_mul_of_nonneg_right hhp (sq_nonneg hi)
      nlinarith
  have hsq : (2*p.control {(0,0)}*(∏ i,s.M i))^2 ≤ (2*p.control {(0,0)}*Cs^N)^2 := by
    apply pow_le_pow_left₀ (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hm0 i)))
    exact mul_le_mul_of_nonneg_left hmp (by positivity)
  unfold zeroControl controlEnvelope
  calc
    _ ≤ (2*p.control {(0,0)}*Cs^N)^2*(1+bs^N*hi*hi)^(1+ε) :=
      mul_le_mul hsq hpr (Real.rpow_nonneg (by
        have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_left 0 (s.hi i))
        nlinarith [mul_nonneg hp (sq_nonneg hi)]) _) (sq_nonneg _)
    _ = _ := by rw [pow_mul]; ring



/-- One constant absorbs the actual fixed source caps for both radius branches. -/
theorem uniform_radius_certificates (N : ℕ) (Cs bs hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
    ∀ lo : ℝ, 0 < lo → 0 ≤ hi → ∀ (s : Input ι) (p : Profiles lo hi),
    (∀ i,s.M i ≤ Cs) → s.upper ≤ bs → s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a c d Bc Rw E K0 nominalLoss δ reserve B s₀ : ℝ), 1 < Z →
    widthLo ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Sil.Uneven.MainSource.total plane beta → a ≤ M*Sil.Uneven.MainSource.amp plane beta →
    0 ≤ c → 0 ≤ d → 0 ≤ Bc → K0 ≤ 2*A-c-d+Rw+E-M+nominalLoss →
    volume s ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    let bound := C*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*(227876729/3446640000)+nominalLoss+δ+reserve+ε*B-s₀)
    Z^(-a-(A-c+Rw+E+Bc))*radiusTerm s R seed W
      (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤ bound ∧
    ∀ (q : O), q ≠ 0 → ∀ k : ℕ, k=1 ∨ k=6 ∨ k=7 → 0 ≤ a →
    Z^(-a-(A-c+Rw+E+Bc))*(localErrorCost q (k-1)*radiusTerm s R seed W
      (errorCommonRadius Z d K0 c (3*a) δ reserve q k)) ≤ bound := by
  obtain ⟨C,hC,hbound⟩ := actual_main_second_zero (plane:=plane) N ε hε
  refine ⟨C*controlEnvelope N Cs bs hi ε,
    mul_pos hC (controlEnvelope_pos N Cs bs hi ε hCs hbs),?_⟩
  intro ι _ hcard lo hlo hhi s p hM hs h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E K0
    nominalLoss δ reserve B s₀ hZ hb hM0 hA ha hc hd hBc hK0 hvol hseedN
  have hm := hbound hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E
    K0 nominalLoss δ reserve B s₀ hZ hb hM0 hA ha hc hd hBc hK0 hvol hseedN
  have hf := zeroControl_fixed N Cs bs ε hCs hbs hε s hcard hM hs p
  have hout : Z^(-a-(A-c+Rw+E+Bc))*radiusTerm s R seed W
      (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤
      (C*controlEnvelope N Cs bs hi ε)*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*(227876729/3446640000)+nominalLoss+δ+reserve+ε*B-s₀) := by
    apply hm.trans
    have hh := mul_le_mul_of_nonneg_left hf hC.le
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (norm_nonneg (paperRadialFourier W 0)))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le
        (-M*(227876729/3446640000)+nominalLoss+δ+reserve+ε*B-s₀))
    simpa only [mul_assoc] using hh'
  refine ⟨hout,?_⟩
  intro q hq k hk ha0
  exact (mul_le_mul_of_nonneg_left
    (actual_extracted_second_zero_le_main s R seed W Z d K0 c a δ reserve hZ ha0 q hq k hk)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans hout

lemma ideal_log_nonneg (I : Ideal O) (hI : I ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ Real.logb Z (I.absNorm : ℝ) := by
  apply Real.logb_nonneg hZ
  have hn : 0 < I.absNorm := by exact_mod_cast norm_pos I hI
  exact_mod_cast Nat.succ_le_iff.mpr hn



end
end OAI.SevenEighths.MainReconstruction
end

/- Original module: Candidate.Uneven.MainZero. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.MainReconstruction
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle63Moment
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow CenteredMomentSourceMass EisensteinSchwartzPoisson
open Cycle63SecondZero
variable {plane : Plane}
local notation "O" => HeckeFamily.O

lemma original_zero_radiusTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖originalSecondZero s R seed W K‖/volume s = radiusTerm s R seed W K := by
  rfl

def firstZeroReference (reflected : Bool) (Z A a : ℝ) (l : FirstSourceLabel) : ℝ :=
  a+A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)

def firstZeroSaving (reflected : Bool) (Z M A ξ reserve padding ε s₀ : ℝ)
    (l : FirstSourceLabel) : ℝ :=
  -M*(227876729/3446640000)+frequencyLoss Z 32 ξ+reserve+
    ε*(A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+padding)-s₀

/-- The literal zero term at the enlarged main radius, with the first
projector and actual child normalization retained in both orientations. -/
theorem actual_first_label_main_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (reflected : Bool) (l : FirstSourceLabel), Supported l.1.1 → Supported l.1.2 →
    CompletedGauss.primeSupport l.1.1 = CompletedGauss.primeSupport l.1.2 →
    ∀ (R seed : Ideal O), seed ≠ 0 →
    ∀ (B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character) (t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P ≠ 0 →
    ∀ (W : 𝓢(ℝ,ℂ)) (Z beta M A a ξ reserve padding s₀ : ℝ), 1 < Z →
    widthLo ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Sil.Uneven.MainSource.total plane beta → a ≤ M*Sil.Uneven.MainSource.amp plane beta →
    volume s = Z^A → bs^N ≤ Z^padding → Z^s₀ ≤ (seed.absNorm:ℝ) →
    let u := child s (if reflected then l.1.2 else l.1.1) R B χ t
    Z^(-firstZeroReference reflected Z A a l)*
      (‖originalSecondZero u (R*(if reflected then l.1.2 else l.1.1)) seed W
        (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l)‖/volume u) ≤
      C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        Z^(firstZeroSaving reflected Z M A ξ reserve padding ε s₀ l) := by
  obtain ⟨C₀,hC₀,hbound⟩ := uniform_radius_certificates (plane:=plane) N Cs bs hi ε hCs hbs hε
  refine ⟨C₀,hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ reflected l hC hD heq R seed hseed B χ t hB
    W Z beta M A a ξ reserve padding s₀ hZ hb hM hA ha hV hgeo hseedN
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let Rw := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let e := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
  have hselected : (if reflected then l.1.2 else l.1.1) ≠ 0 := by
    cases reflected <;> first | exact hC.1 | exact hD.1
  have hother : (if reflected then l.1.1 else l.1.2) ≠ 0 := by
    cases reflected <;> first | exact hD.1 | exact hC.1
  have hcn : Z^c ≤ ((if reflected then l.1.2 else l.1.1).absNorm:ℝ) := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (norm_pos _ hselected)]
  have hv := actual_common_volume_cap N bs hbs s hn hs _ R B χ t hB Z A c padding hZ
    hgeo (le_of_eq hV) hcn
  have hh := hbound hv.1 lo hlo hhi (child s _ R B χ t) p
    (fun i => hm i.val) hs hp₁ hp₂ (R*(if reflected then l.1.2 else l.1.1)) seed hseed
    W Z beta M A a c d 0 Rw e (2*A-c-d+Rw+e-M) 0 (frequencyLoss Z 32 ξ) reserve
    (A-c+padding) s₀ hZ hb hM hA ha
    (ideal_log_nonneg _ hselected Z hZ) (ideal_log_nonneg _ hother Z hZ)
    (by norm_num) (by simp) hv.2 hseedN
  have hr : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l =
      mainCommonRadius Z d (2*A-c-d+Rw+e-M) c (3*a) (frequencyLoss Z 32 ξ) reserve := by
    rw [hV,actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ]
    unfold mainCommonRadius
    congr 1
    dsimp only [c,d,Rw,e]
    ring
  dsimp only
  rw [hr,original_zero_radiusTerm]
  convert hh.1 using 1 <;>
    dsimp only [firstZeroReference,firstZeroSaving,c,d,Rw,e,radiusTerm] <;>
    congr 2 <;> ring

/-- Remove only the displayed positive reference power; the normalized
child volume is still literal. -/
lemma reference_power_remove (Z ref saving x bound : ℝ) (hZ : 0 < Z)
    (h : Z^(-ref)*x ≤ bound*Z^saving) : x ≤ bound*Z^(ref+saving) := by
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le ref)
  have he : Z^ref*Z^(-ref) = 1 := by rw [←Real.rpow_add hZ]; simp
  apply (show x ≤ Z^ref*bound*Z^saving by simpa only [←mul_assoc,he,one_mul] using hh).trans_eq
  rw [Real.rpow_add hZ]
  ring

end
end OAI.SevenEighths.MainReconstruction
end
