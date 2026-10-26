/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.SecondZero.Radius
import Submissions.hailey_collet_1252270103.Cycle61.Physical.NominalRadius

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61SecondZero
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization EisensteinSchwartzPoisson
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

lemma child_zeroControl_fixed {ι : Type*} [Fintype ι] (N : ℕ) (Cs bs ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hM : ∀ i,s.M i ≤ Cs) (hs : s.upper ≤ bs)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    {lo hi : ℝ} (p : Profiles lo hi) :
    zeroControl (child s C R B τ t) p ε ≤ controlEnvelope N Cs bs hi ε*(p.control {(0,0)})^2 :=
  zeroControl_fixed N Cs bs ε hCs hbs hε _ ((live_card_le B.val).trans hcard)
    (fun i => hM i.val) hs p

lemma twice_zeroControl_fixed {ι : Type*} [Fintype ι] (N : ℕ) (Cs bs ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hM : ∀ i,s.M i ≤ Cs) (hs : s.upper ≤ bs)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ) (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) {lo hi : ℝ} (p : Profiles lo hi) :
    zeroControl (twiceChild s C R B τ t Q k Bp υ v) p ε ≤
      controlEnvelope N Cs bs hi ε*(p.control {(0,0)})^2 :=
  zeroControl_fixed N Cs bs ε hCs hbs hε _
    ((live_card_le Bp.val).trans ((live_card_le B.val).trans hcard))
    (fun i => hM i.val.val) hs p

/-- One constant absorbs the actual fixed source caps for both radius branches. -/
theorem uniform_radius_certificates (N : ℕ) (Cs bs hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
    ∀ lo : ℝ, 0 < lo → 0 ≤ hi → ∀ (s : Input ι) (p : Profiles lo hi),
    (∀ i,s.M i ≤ Cs) → s.upper ≤ bs → s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a c d Bc Rw E K0 nominalLoss δ reserve B s₀ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle61.Arithmetic.totalA beta → a ≤ M*Cycle61.Arithmetic.amp beta →
    0 ≤ c → 0 ≤ d → 0 ≤ Bc → K0 ≤ 2*A-c-d+Rw+E-M+nominalLoss →
    volume s ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    let bound := C*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*(8754683599/120632400000)+nominalLoss+δ+reserve+ε*B-s₀)
    Z^(-a-(A-c+Rw+E+Bc))*radiusTerm s R seed W
      (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤ bound ∧
    ∀ (q : O), q ≠ 0 → ∀ k : ℕ, k=1 ∨ k=6 ∨ k=7 → 0 ≤ a →
    Z^(-a-(A-c+Rw+E+Bc))*(localErrorCost q (k-1)*radiusTerm s R seed W
      (errorCommonRadius Z d K0 c (3*a) δ reserve q k)) ≤ bound := by
  obtain ⟨C,hC,hbound⟩ := actual_main_second_zero N ε hε
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
      Z^(-M*(8754683599/120632400000)+nominalLoss+δ+reserve+ε*B-s₀) := by
    apply hm.trans
    have hh := mul_le_mul_of_nonneg_left hf hC.le
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (norm_nonneg (paperRadialFourier W 0)))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le
        (-M*(8754683599/120632400000)+nominalLoss+δ+reserve+ε*B-s₀))
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

/-- Actual common child, with its inherited fixed controls and the genuine
nominal radius; no nominal-width or child-volume estimate is assumed. -/
theorem actual_uniform_common_second_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hε : 0 < ε) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ {ι : Type*} [Fintype ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (C D E R seed : Ideal O), C ≠ 0 → D ≠ 0 → E ≠ 0 → seed ≠ 0 →
    IdealMobiusDivisorSum.primeSupport C = IdealMobiusDivisorSum.primeSupport D →
    ∀ (B : actualAllocations s.pools C) (τ : Character) (t : ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a Bc δ reserve padding s₀ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle61.Arithmetic.totalA beta → a ≤ M*Cycle61.Arithmetic.amp beta → 0 ≤ Bc →
    bs^N ≤ Z^padding → volume s ≤ Z^A → Z^s₀ ≤ (seed.absNorm : ℝ) →
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let Rw := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    let e := Real.logb Z (E.absNorm : ℝ)
    let K0 := nominalLog C D E (Z^M) (volume s) Z
    Z^(-a-(A-c+Rw+e+Bc))*radiusTerm (child s C R B τ t) (R*C) seed W
      (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤
    Kc*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*(8754683599/120632400000)+δ+reserve+ε*(A-c+padding)-s₀) := by
  obtain ⟨Kc,hKc,hbound⟩ := uniform_radius_certificates N Cs bs hi ε hCs hbs hε
  refine ⟨Kc,hKc,?_⟩
  intro ι _ s hcard hM hs p h₁ h₂ C D E R seed hC hD hE hseed heq B τ t hne W
    Z beta M A a Bc δ reserve padding s₀ hZ hb hM0 hA ha hBc hgeo hvol hseedN
  have hz := zero_lt_one.trans hZ
  have hCN : Z^(Real.logb Z (C.absNorm : ℝ)) ≤ (C.absNorm : ℝ) := by
    rw [Real.rpow_logb hz hZ.ne' (norm_pos C hC)]
  have hv := actual_common_volume_cap N bs hbs s hcard hs C R B τ t hne
    Z A (Real.logb Z (C.absNorm : ℝ)) padding hZ hgeo hvol hCN
  have hn := Cycle61NominalRadius.actual_nominal_le C D E hC hD hE heq
    (volume s) Z M A (CenteredMomentAmplificationChildInput.volume_pos s) hZ hvol
  have hh := hbound hv.1 lo hlo hhi (child s C R B τ t) p
    (fun i => hM i.val) hs h₁ h₂ (R*C) seed hseed W Z beta M A a
    (Real.logb Z (C.absNorm : ℝ)) (Real.logb Z (D.absNorm : ℝ)) Bc
    (Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)) (Real.logb Z (E.absNorm : ℝ))
    (nominalLog C D E (Z^M) (volume s) Z) 0 δ reserve
    (A-Real.logb Z (C.absNorm : ℝ)+padding) s₀ hZ hb hM0 hA ha
    (ideal_log_nonneg C hC Z hZ) (ideal_log_nonneg D hD Z hZ) hBc (by simpa using hn) hv.2 hseedN
  simpa only [add_zero,radiusTerm] using hh.1

/-- Actual twice child at the extracted radius, retaining extraction cost,
seed, masks, and independent original and child heights. -/
theorem actual_uniform_twice_second_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hε : 0 < ε) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ {ι : Type*} [Fintype ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (C D E R seed : Ideal O), C ≠ 0 → D ≠ 0 → E ≠ 0 → seed ≠ 0 →
    IdealMobiusDivisorSum.primeSupport C = IdealMobiusDivisorSum.primeSupport D →
    ∀ (B : actualAllocations s.pools C) (τ : Character) (t : ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ (q : O), q ≠ 0 → ∀ k : ℕ, k=1 ∨ k=6 ∨ k=7 →
    (∀ i,∀ I ∈ (child s C R B τ t).slots i,IsCoprime (Ideal.span {q}) I) →
    ∀ (Bp : actualAllocations (child s C R B τ t).pools ((Ideal.span {q})^k))
    (υ : Character) (v : ℝ) (W : 𝓢(ℝ,ℂ))
    (Z beta M A a Bc δ reserve padding s₀ b₁ b₂ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle61.Arithmetic.totalA beta → a ≤ M*Cycle61.Arithmetic.amp beta →
    0 ≤ a → 0 ≤ Bc → 1 ≤ b₁ → 1 ≤ b₂ → Endpoints bs b₁ b₂ s →
    geometry N bs b₁ b₂ ≤ Z^padding → volume s ≤ Z^A → Z^s₀ ≤ (seed.absNorm : ℝ) →
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let Rw := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    let e := Real.logb Z (E.absNorm : ℝ)
    let K0 := nominalLog C D E (Z^M) (volume s) Z
    Z^(-a-(A-c+Rw+e+Bc))*(localErrorCost q (k-1)*
      radiusTerm (twiceChild s C R B τ t (Ideal.span {q}) k Bp υ v)
        ((R*C)*(Ideal.span {q})^k) seed W (errorCommonRadius Z d K0 c (3*a) δ reserve q k)) ≤
    Kc*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
      Z^(-M*(8754683599/120632400000)+δ+reserve+
        ε*(A-c-errorRemoval q Z k+padding)-s₀) := by
  obtain ⟨Kc,hKc,hbound⟩ := uniform_radius_certificates N Cs bs hi ε hCs hbs hε
  refine ⟨Kc,hKc,?_⟩
  intro ι _ s hcard hM hs p h₁ h₂ C D E R seed hC hD hE hseed heq B τ t hne q hq k hk hslot
    Bp υ v W Z beta M A a Bc δ reserve padding s₀ b₁ b₂ hZ hb hM0 hA ha ha0 hBc hb₁ hb₂ he hgeo hvol hseedN
  have hz := zero_lt_one.trans hZ
  have hQ : Ideal.span {q} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hq
  have hCN : Z^(Real.logb Z (C.absNorm : ℝ)) ≤ (C.absNorm : ℝ) := by
    rw [Real.rpow_logb hz hZ.ne' (norm_pos C hC)]
  have hQN : Z^(errorRemoval q Z k) ≤ ((Ideal.span {q}).absNorm : ℝ)^k := by
    unfold errorRemoval
    rw [mul_comm,Real.rpow_mul hz.le,Real.rpow_natCast,
      Real.rpow_logb hz hZ.ne' (normValue_pos q hq)]
    exact le_rfl
  have hv := actual_twice_volume_cap N bs b₁ b₂ hbs hb₁ hb₂ s hcard he C R B τ t hne
    (Ideal.span {q}) hQ k hslot Bp υ v Z A (Real.logb Z (C.absNorm : ℝ))
    (errorRemoval q Z k) padding hZ hgeo hvol hCN hQN
  have hn := Cycle61NominalRadius.actual_nominal_le C D E hC hD hE heq
    (volume s) Z M A (CenteredMomentAmplificationChildInput.volume_pos s) hZ hvol
  have hh := hbound hv.1 lo hlo hhi (twiceChild s C R B τ t (Ideal.span {q}) k Bp υ v) p
    (fun i => hM i.val.val) hs h₁ h₂ ((R*C)*(Ideal.span {q})^k) seed hseed W Z beta M A a
    (Real.logb Z (C.absNorm : ℝ)) (Real.logb Z (D.absNorm : ℝ)) Bc
    (Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)) (Real.logb Z (E.absNorm : ℝ))
    (nominalLog C D E (Z^M) (volume s) Z) 0 δ reserve
    (A-Real.logb Z (C.absNorm : ℝ)-errorRemoval q Z k+padding) s₀ hZ hb hM0 hA ha
    (ideal_log_nonneg C hC Z hZ) (ideal_log_nonneg D hD Z hZ) hBc (by simpa using hn) hv.2.2.1 hseedN
  simpa only [add_zero,radiusTerm] using hh.2 q hq k hk ha0

end
end OAI.SevenEighths.Cycle61SecondZero
#print axioms OAI.SevenEighths.Cycle61SecondZero.zeroControl_fixed
#print axioms OAI.SevenEighths.Cycle61SecondZero.child_zeroControl_fixed
#print axioms OAI.SevenEighths.Cycle61SecondZero.twice_zeroControl_fixed
#print axioms OAI.SevenEighths.Cycle61SecondZero.uniform_radius_certificates
#print axioms OAI.SevenEighths.Cycle61SecondZero.controlEnvelope_pos
#print axioms OAI.SevenEighths.Cycle61SecondZero.ideal_log_nonneg
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_uniform_common_second_zero
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_uniform_twice_second_zero
