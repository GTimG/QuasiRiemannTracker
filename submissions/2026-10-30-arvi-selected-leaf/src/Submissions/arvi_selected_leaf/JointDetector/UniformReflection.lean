/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.SquarefreeReflection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.DyadBudget

/-! Uniform scalar absorption for the CLOSED actual squarefree reflection.
Only finite counting and real inequalities are added here; no analytic
reflection or amplifier estimate is an input. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

/-- The scalar tail estimate only needs a positive radius; this includes
nonempty descendant annuli whose radius is between one half and one. -/
theorem physical_tail_budget_le_pos_radius
    (Z P B L ε N n C₀ Crows : ℝ) (A : ℕ)
    (hZ : 2 ≤ Z) (hP : 0 ≤ P) (hB : 0 < B) (hBU : B ≤ Z ^ P)
    (hL : 0 < L) (hLlo : Z ^ (-P) ≤ L) (hLhi : L ≤ Z ^ P)
    (hrows : n ≤ Crows * B) (hCrows : 0 ≤ Crows) (hC₀ : 0 ≤ C₀)
    (hA : N + 7 * P ≤ ε * (A : ℝ)) :
    (L / B) * n * C₀ /
        ((min 1 (L / (4 * B ^ 2))) ^ 2 * (1 + Z ^ ε) ^ A) ≤
      16 * Crows * C₀ * Z ^ (-N) := by
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hB0 : 0 < B := hB
  let U := Z ^ P
  have hU1 : 1 ≤ U := by
    dsimp [U]
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ1 hP
  have hU0 : 0 < U := by linarith
  have hBU' : B ≤ U := hBU
  have hLhi' : L ≤ U := hLhi
  have hLlo' : 1 / U ≤ L := by
    simpa only [U, Real.rpow_neg hZ0.le, one_div] using hLlo
  let M := 4 * U ^ 3
  have hM1 : 1 ≤ M := by
    have := one_le_pow₀ hU1 (n := 3)
    dsimp [M]
    linarith
  have hM0 : 0 < M := by linarith
  have hlow : 1 / M ≤ min 1 (L / (4 * B ^ 2)) := by
    apply le_min
    · exact (div_le_iff₀ hM0).2 (by simpa using hM1)
    · calc
        1 / M = (1 / U) / (4 * U ^ 2) := by dsimp [M]; field_simp
        _ ≤ L / (4 * B ^ 2) := by
          apply div_le_div₀ hL.le hLlo' (by positivity)
          gcongr
  let δ := min 1 (L / (4 * B ^ 2))
  have hδ0 : 0 < δ := lt_min zero_lt_one (by positivity)
  have hMδ : 1 ≤ M * δ := by
    have := (div_le_iff₀ hM0).1 hlow
    simpa only [δ, mul_comm] using this
  have hMδsq : 1 ≤ M ^ 2 * δ ^ 2 := by
    have := one_le_pow₀ hMδ (n := 2)
    simpa only [mul_pow, one_pow] using this
  have hpref : (L / B) * n ≤ Crows * U := by
    calc
      _ ≤ (L / B) * (Crows * B) := mul_le_mul_of_nonneg_left hrows (by positivity)
      _ = Crows * L := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hLhi' hCrows
  have hnum : (L / B) * n * C₀ / δ ^ 2 ≤ (Crows * U * C₀) * M ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hδ0)).2
    calc
      _ ≤ Crows * U * C₀ := mul_le_mul_of_nonneg_right hpref hC₀
      _ ≤ (Crows * U * C₀) * (M ^ 2 * δ ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hMδsq
          (show 0 ≤ Crows * U * C₀ by positivity)
      _ = _ := by ring
  have hpow : U ^ 7 / (Z ^ ε) ^ A ≤ Z ^ (-N) := by
    have hU7 : U ^ 7 = Z ^ (7 * P) := by
      dsimp [U]
      rw [← Real.rpow_mul_natCast hZ0.le]
      congr 1
      norm_num
      ring
    rw [hU7, ← Real.rpow_mul_natCast hZ0.le, ← Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  calc
    _ = ((L / B) * n * C₀ / δ ^ 2) / (1 + Z ^ ε) ^ A := by dsimp [δ]; ring
    _ ≤ ((Crows * U * C₀) * M ^ 2) / (1 + Z ^ ε) ^ A :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((Crows * U * C₀) * M ^ 2) / (Z ^ ε) ^ A := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) A
    _ = (16 * Crows * C₀) * (U ^ 7 / (Z ^ ε) ^ A) := by dsimp [M]; ring
    _ ≤ (16 * Crows * C₀) * Z ^ (-N) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)



local instance : Fintype Oˣ := by
  letI : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

theorem badSector_count_le_dyadic (T : ℝ) :
    ((BadFrequencySectors.boundedKeys T).card : ℝ) ≤
      (Fintype.card Oˣ : ℝ) * (columnDyadicLength T + 1 : ℝ)^2 := by
  have hc : Nat.ceil T ≤ 2^columnDyadicLength T := by
    apply Nat.ceil_le.mpr
    exact_mod_cast columnDyadicLength_cover T
  have hl : Nat.log 2 (Nat.ceil T) ≤ columnDyadicLength T := by
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [Nat.log_pow (by decide : 1 < 2)] using hh
  have hh : (Nat.log 2 (Nat.ceil T) + 1 : ℝ) ≤ (columnDyadicLength T + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hl 1
  unfold BadFrequencySectors.boundedKeys
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
    Finset.card_range, Nat.cast_mul]
  calc
    _ = (Fintype.card Oˣ : ℝ) * (Nat.log 2 (Nat.ceil T) + 1 : ℝ)^2 := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (Nat.cast_nonneg _)

/-- The unit/bad-place sectors and source dyads together cost an arbitrary
small ambient power, uniformly over every polynomially bounded cutoff. -/
theorem badSector_dyadic_small_power (P ε : ℝ) (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 1 ≤ Z → 0 < T → T ≤ Z^P →
      ((BadFrequencySectors.boundedKeys T).card : ℝ) * (columnDyadicLength T + 1 : ℕ) ≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := InverseReflectedPhase.actual_dyad_count_budget P ε hP hε
  refine ⟨(Fintype.card Oˣ : ℝ)*C, mul_pos (by exact_mod_cast Fintype.card_pos) hC,?_⟩
  intro Z T hZ hT hTZ
  calc
    _ ≤ ((Fintype.card Oˣ : ℝ)*(columnDyadicLength T+1 : ℝ)^2) * (columnDyadicLength T+1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_right (badSector_count_le_dyadic T)
          (show 0 ≤ ((columnDyadicLength T + 1 : ℕ) : ℝ) by positivity)
    _ = (Fintype.card Oˣ : ℝ) * ((columnDyadicLength T+1 : ℝ)*(columnDyadicLength T+1 : ℝ)^2) := by ring
    _ ≤ (Fintype.card Oˣ : ℝ)*(C*Z^ε) :=
      mul_le_mul_of_nonneg_left (hbound Z T T hZ hT hT hTZ hTZ) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem badSector_small_power (P ε : ℝ) (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 1 ≤ Z → 0 < T → T ≤ Z^P →
      ((BadFrequencySectors.boundedKeys T).card : ℝ) ≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩ := badSector_dyadic_small_power P ε hP hε
  refine ⟨C,hC,?_⟩
  intro Z T hZ hT hTZ
  apply le_trans _ (hbound Z T hZ hT hTZ)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast Nat.succ_pos (columnDyadicLength T))

/-- Actual primary row counting, including nonempty radii below one. -/
theorem primaryRows_card_le (rows : Finset O) (B : ℝ) (hB : 0 ≤ B)
    (hn : ∀ r ∈ rows, r ≠ 0) (hp : ∀ r ∈ rows, lambda^2 ∣ r-1)
    (hN : ∀ r ∈ rows, (Ideal.absNorm (Ideal.span {r}) : ℝ) ≤ 2*B) :
    (rows.card : ℝ) ≤ 256*B := by
  by_cases hs : rows.Nonempty
  · obtain ⟨r,hr⟩ := hs
    have hspan (z : O) (hz : z ∈ rows) : (Ideal.span {z} : Ideal O) ≠ ⊥ := by
      exact fun h => hn z hz (Ideal.span_singleton_eq_bot.mp h)
    have hone : 1 ≤ 2*B := by
      have hnorm : (1 : ℝ) ≤ (Ideal.absNorm (Ideal.span {r}) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hspan r hr (Ideal.absNorm_eq_zero_iff.mp h))
      exact hnorm.trans (hN r hr)
    have hinj : Set.InjOn (fun z : O => (Ideal.span {z} : Ideal O)) rows := by
      intro z hz w hw he
      have h := congrArg primaryGenerator he
      simpa only [primaryGenerator_span z (hn z hz) (hp z hz), primaryGenerator_span w (hn w hw) (hp w hw)] using h
    have hc := DescentFiberCost.finite_ideal_count_real
      (rows.image fun z => (Ideal.span {z} : Ideal O)) (2*B) hone
      (by intro I hI; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI; exact hspan z hz)
      (by intro I hI; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI; exact hN z hz)
    rw [Finset.card_image_iff.mpr hinj] at hc
    linarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.cast_zero]
    positivity

theorem quotientRows_card_le (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (D : Ideal O) (hD : D ≠ 0) (B : ℝ) (hB : 0 ≤ B)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) :
    ((selectedQuotientRows F D).card : ℝ) ≤ 256*(B/(Ideal.absNorm D : ℝ)) := by
  apply primaryRows_card_le _ _ (div_nonneg hB (Nat.cast_nonneg _))
    (fun r hr => (selectedQuotientRows_spec F hF D ⟨r,hr⟩).1)
    (fun r hr => (selectedQuotientRows_spec F hF D ⟨r,hr⟩).2.1)
  exact fun r hr => (selectedQuotientRows_norm F hF D hD B hN ⟨r,hr⟩).2

/-- Uniform decay of the explicit COMPLETE-mode tail cost. In particular,
shrinking descendant radii do not require an unweighted unit error. -/
theorem modeTailCost_small_power (rows : Finset O) (Z P B L ε N Ctail : ℝ)
    (d : O) (A : ℕ) (hZ : 2 ≤ Z) (hP : 0 ≤ P) (hB : 0 < B)
    (hBU : B ≤ Z^P) (hLlo : Z^(-P) ≤ L/‖eisEmbedding d‖^2)
    (hLhi : L/‖eisEmbedding d‖^2 ≤ Z^P) (hrows : (rows.card : ℝ) ≤ 256*B)
    (hCtail : 0 ≤ Ctail) (hA : N+7*P ≤ ε*(A : ℝ)) :
    modeTailCost rows L B (Z^ε) Ctail d A ≤ 4096*Ctail*Z^(-N) := by
  have hz : 0 < Z := by linarith
  convert physical_tail_budget_le_pos_radius Z P B (L/‖eisEmbedding d‖^2) ε N
    (rows.card : ℝ) Ctail 256 A hZ hP hB hBU
    ((Real.rpow_pos_of_pos hz (-P)).trans_le hLlo) hLlo hLhi hrows (by norm_num) hCtail hA using 1 <;> norm_num [modeTailCost]


def simpleModeProfile (rows : Finset O) (L B H : ℝ) (d : O) : ℝ :=
  let T := modeFrequencyCutoff L B H d
  L/‖eisEmbedding d‖^2 + ((L/‖eisEmbedding d‖^2)/B) *
    selectedNorm rows (selectedFrequencyPool (reflectionFrequencies T) T)

/-- Uniform small-power absorption of a COMPLETE reflected mode on fixed
polynomial scales. The zero and far terms are both paid by `L/Norm(d)`,
while the finite near term is the actual descendant operator norm. -/
theorem modeBudget_uniform (W : 𝓢(ℝ, ℂ)) (P η ε Cnear Ctail : ℝ)
    (hP : 0 ≤ P) (hη : 0 < η) (hε : 0 < ε) (hεbudget : P*ε ≤ η/2)
    (hCn : 0 ≤ Cnear) (hCt : 0 ≤ Ctail) :
    ∃ C : ℝ, 0 < C ∧ ∀ (rows : Finset O) (Z L B s : ℝ) (d : O) (A : ℕ),
      2 ≤ Z → 0 < L → 0 < B → d ≠ 0 → B ≤ Z^P → 2*B ≤ Z^P →
      Z^(-P) ≤ L/‖eisEmbedding d‖^2 → L/‖eisEmbedding d‖^2 ≤ Z^P →
      modeFrequencyCutoff L B (Z^s) d ≤ Z^P →
      (rows.card : ℝ) ≤ 256*B → 8*P ≤ s*(A : ℝ) →
      modeBudget rows W L B (Z^s) Cnear Ctail d ε hε A ≤
        C*Z^η*simpleModeProfile rows L B (Z^s) d := by
  obtain ⟨Cd,hCd,hdyad⟩ := badSector_dyadic_small_power P (η/2) hP (by positivity)
  let Cn := Cd*Cnear*idealDivisorConstant ε hε
  have hCn' : 0 ≤ Cn := mul_nonneg (mul_nonneg hCd.le hCn) (idealDivisorConstant_pos ε hε).le
  let C := ‖paperRadialFourier W 0‖+4096*Ctail+Cn+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro rows Z L B s d A hZ hL hB hd hBU h2BU hLlo hLhi hTU hrows hA
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hdN : 0 < ‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  let T := modeFrequencyCutoff L B (Z^s) d
  have hT : 0 < T := by dsimp [T,modeFrequencyCutoff]; positivity
  let K := selectedNorm rows (selectedFrequencyPool (reflectionFrequencies T) T)
  have hK : 0 ≤ K := sq_nonneg _
  let V := (L/‖eisEmbedding d‖^2)/B*K
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hdiv : (2*B)^ε ≤ Z^(η/2) := by
    calc
      _ ≤ (Z^P)^ε := Real.rpow_le_rpow (by positivity) h2BU hε.le
      _ = Z^(P*ε) := (Real.rpow_mul hz.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 hεbudget
  have hnear : modeNearCost rows L B (Z^s) Cnear d ε hε ≤ Cn*Z^η*V := by
    have hc := hdyad Z T hz1 hT hTU
    have hdiv' := mul_le_mul_of_nonneg_left hdiv (idealDivisorConstant_pos ε hε).le
    calc
      _ = (((BadFrequencySectors.boundedKeys T).card : ℝ)*(columnDyadicLength T+1 : ℕ)) *
          Cnear*(idealDivisorConstant ε hε*(2*B)^ε)*V := by
        dsimp [modeNearCost,T,V,K]
        field_simp
        <;> ring
      _ ≤ (Cd*Z^(η/2))*Cnear*(idealDivisorConstant ε hε*Z^(η/2))*V := by
        gcongr
        exact mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε)
      _ = Cn*(Z^(η/2)*Z^(η/2))*V := by dsimp [Cn]; ring
      _ = _ := by rw [← Real.rpow_add hz]; congr 2 <;> ring
  have htail := modeTailCost_small_power rows Z P B L s P Ctail d A hZ hP hB hBU
    hLlo hLhi hrows hCt (by linarith)
  have ht : modeTailCost rows L B (Z^s) Ctail d A ≤ 4096*Ctail*(L/‖eisEmbedding d‖^2) :=
    htail.trans (mul_le_mul_of_nonneg_left hLlo (by positivity))
  have hzη : 1 ≤ Z^η := Real.one_le_rpow hz1 hη.le
  have hpr1 : L/‖eisEmbedding d‖^2 ≤ simpleModeProfile rows L B (Z^s) d := by
    change _ ≤ L/‖eisEmbedding d‖^2+V
    linarith
  have hpr2 : V ≤ simpleModeProfile rows L B (Z^s) d := by
    change _ ≤ L/‖eisEmbedding d‖^2+V
    linarith [div_nonneg hL.le hdN.le]
  have hpr0 : 0 ≤ simpleModeProfile rows L B (Z^s) d := (by positivity : 0 ≤ L/‖eisEmbedding d‖^2).trans hpr1
  have hzpr : simpleModeProfile rows L B (Z^s) d ≤ Z^η*simpleModeProfile rows L B (Z^s) d :=
    le_mul_of_one_le_left hpr0 hzη
  calc
    _ ≤ (L/‖eisEmbedding d‖^2)*‖paperRadialFourier W 0‖ + Cn*Z^η*V +
        4096*Ctail*(L/‖eisEmbedding d‖^2) := add_le_add (add_le_add le_rfl hnear) ht
    _ ≤ (‖paperRadialFourier W 0‖+Cn+4096*Ctail)*(Z^η*simpleModeProfile rows L B (Z^s) d) := by
      have h1 := mul_le_mul_of_nonneg_left (hpr1.trans hzpr) (norm_nonneg (paperRadialFourier W 0))
      have h2 := mul_le_mul_of_nonneg_left hpr2 (mul_nonneg hCn' (Real.rpow_nonneg hz.le η))
      have h3 := mul_le_mul_of_nonneg_left (hpr1.trans hzpr) (show 0 ≤ 4096*Ctail by positivity)
      nlinarith
    _ ≤ _ := by dsimp [C]; nlinarith [mul_nonneg (Real.rpow_nonneg hz.le η) hpr0]


theorem inputSectorScale_one_le (k : Oˣ × ℕ × ℕ) : 1 ≤ inputSectorScale k := by
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))

theorem inputSectorScale_upper (L : ℝ) (hL : 1 ≤ L) (k : Oˣ × ℕ × ℕ)
    (hk : k ∈ BadFrequencySectors.boundedKeys L) : inputSectorScale k ≤ (2*L)^4 := by
  have ha : k.2.1 ≤ Nat.log 2 (Nat.ceil L) := Nat.le_of_lt_succ
    (Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hk).2).1)
  have hb : k.2.2 ≤ Nat.log 2 (Nat.ceil L) := Nat.le_of_lt_succ
    (Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hk).2).2)
  have hn : Nat.ceil L ≠ 0 := by
    have : (1 : ℝ) ≤ Nat.ceil L := hL.trans (Nat.le_ceil L)
    exact_mod_cast (by linarith : (0 : ℝ) < Nat.ceil L).ne'
  have hpow : (2 : ℝ)^Nat.log 2 (Nat.ceil L) ≤ Nat.ceil L := by
    exact_mod_cast Nat.pow_log_le_self 2 hn
  have hceil : (Nat.ceil L : ℝ) ≤ 2*L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ L by linarith)
    linarith
  calc
    inputSectorScale k ≤ (4 : ℝ)^Nat.log 2 (Nat.ceil L) * (4 : ℝ)^Nat.log 2 (Nat.ceil L) := by
      unfold inputSectorScale
      apply mul_le_mul _ (pow_le_pow_right₀ (by norm_num) hb) (by positivity) (by positivity)
      exact (pow_le_pow_left₀ (by norm_num) (by norm_num) k.2.1).trans (pow_le_pow_right₀ (by norm_num) ha)
    _ = ((2 : ℝ)^Nat.log 2 (Nat.ceil L))^4 := by
      have he : (4 : ℝ)^Nat.log 2 (Nat.ceil L) = ((2 : ℝ)^Nat.log 2 (Nat.ceil L))^2 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      rw [he]
      ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (hpow.trans hceil) 4

/-- All source-mask norms are bounded by the actual fixed bad factor times
the original gcd norm; there is no unrestricted divisor parameter. -/
theorem maskDivisor_norm_le (D : Ideal O) (hD : Admissible D)
    (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D)) :
    1 ≤ (Ideal.absNorm e : ℝ) ∧
      (Ideal.absNorm e : ℝ) ≤ (Ideal.absNorm reflectionBadIdeal : ℝ)*(Ideal.absNorm D : ℝ) := by
  have hdiv := (mem_idealDivisors (commonMaskIdeal_squarefree D).ne_zero).mp he
  have he0 : e ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hdiv
    exact (commonMaskIdeal_squarefree D).ne_zero hdiv
  refine ⟨?_,?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => he0 (Ideal.absNorm_eq_zero_iff.mp h))
  · rw [reflectionBadIdeal, ← Nat.cast_mul, ← commonMaskIdeal_norm D hD]
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (fun h => (commonMaskIdeal_squarefree D).ne_zero (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hdiv)

/-- A scalar coordinate of the reflection: `R` includes BOTH the source
mask ideal and the retained bad-place powers of the original source. -/
def reflectedSourceRatio (e : Ideal O) (k : Oˣ × ℕ × ℕ) : ℝ :=
  (Ideal.absNorm e : ℝ)*inputSectorScale k

theorem reflectedSourceRatio_range (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (L B : ℝ) (hL : 1 ≤ L)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ 2*B)
    (D : Ideal O) (hD : D ∈ gcdPool (fun I : F => I.val))
    (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D))
    (k : Oˣ × ℕ × ℕ) (hk : k ∈ BadFrequencySectors.boundedKeys L) :
    1 ≤ reflectedSourceRatio e k ∧ reflectedSourceRatio e k ≤
      32*(Ideal.absNorm reflectionBadIdeal : ℝ)*B*L^4 := by
  have hd := selectedGcd_spec F hF (2*B) hN D hD
  have heN := maskDivisor_norm_le D hd.1 e he
  refine ⟨one_le_mul_of_one_le_of_one_le heN.1 (inputSectorScale_one_le k),?_⟩
  calc
    _ ≤ ((Ideal.absNorm reflectionBadIdeal : ℝ)*(2*B))*((2*L)^4) := by
      apply mul_le_mul (heN.2.trans (mul_le_mul_of_nonneg_left hd.2 (Nat.cast_nonneg _)))
        (inputSectorScale_upper L hL k hk) (inputSectorScale_pos k).le
      exact mul_nonneg (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hd.2)
    _ = _ := by ring


def uniformReflectionScale (P : ℝ) : ℝ := 8*P+4

/-- Every scalar range used in uniform mode absorption follows from the
ORIGINAL polynomial row/source range and the actual divisor/sector labels. -/
theorem reflection_polynomial_ranges (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (Z P L B s : ℝ)
    (hZ : 4 ≤ Z) (hP : 0 ≤ P)
    (hbad : 32*(Ideal.absNorm reflectionBadIdeal : ℝ) ≤ Z)
    (hL : 1 ≤ L) (hLU : L ≤ Z^P) (hB : 1 ≤ B) (hBU : B ≤ Z^P)
    (hs : s ≤ 1) (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ 2*B)
    (D : Ideal O) (hD : D ∈ gcdPool (fun I : F => I.val))
    (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D))
    (k : Oˣ × ℕ × ℕ) (hk : k ∈ BadFrequencySectors.boundedKeys L) :
    let b := B/(Ideal.absNorm D : ℝ)
    let l := L/inputSectorScale k
    let d := idealGenerator e
    0 < b ∧ 0 < l ∧ d ≠ 0 ∧ b ≤ Z^(uniformReflectionScale P) ∧
      2*b ≤ Z^(uniformReflectionScale P) ∧
      Z^(-(uniformReflectionScale P)) ≤ l/‖eisEmbedding d‖^2 ∧
      l/‖eisEmbedding d‖^2 ≤ Z^(uniformReflectionScale P) ∧
      modeFrequencyCutoff l b (Z^s) d ≤ Z^(uniformReflectionScale P) := by
  dsimp only
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hd := selectedGcd_spec F hF (2*B) hN D hD
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hd.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have heN := maskDivisor_norm_le D hd.1 e he
  have he0 : e ≠ 0 := by
    intro hh
    simp only [hh,map_zero,Nat.cast_zero] at heN
    linarith [heN.1]
  have hd0 := ConcretePrimeRowBridge.idealGenerator_ne_zero e he0
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
  have hb0 : 0 < B/(Ideal.absNorm D : ℝ) := div_pos hB0 hDN0
  have hbU : B/(Ideal.absNorm D : ℝ) ≤ Z^P :=
    (div_le_self hB0.le hDN).trans hBU
  have hR := reflectedSourceRatio_range F hF L B hL hN D hD e he k hk
  have hR0 : 0 < reflectedSourceRatio e k := by linarith [hR.1]
  have hRU : reflectedSourceRatio e k ≤ Z^(5*P+1) := by
    apply hR.2.trans
    calc
      _ ≤ Z*(Z^P)*(Z^P)^4 := by gcongr
      _ = Z^(1 : ℝ)*Z^P*Z^(P*4) := by
        rw [Real.rpow_one]
        congr 1
        simpa only [Nat.cast_ofNat] using (Real.rpow_mul_natCast hz.le P 4).symm
      _ = _ := by rw [← Real.rpow_add hz, ← Real.rpow_add hz]; congr 1; ring
  have heq : (L/inputSectorScale k)/‖eisEmbedding (idealGenerator e)‖^2 = L/reflectedSourceRatio e k := by
    rw [idealGenerator_norm_sq]
    unfold reflectedSourceRatio
    ring
  have hE0 : 0 < L/reflectedSourceRatio e k := div_pos hL0 hR0
  have hElo : Z^(-(5*P+1)) ≤ L/reflectedSourceRatio e k := by
    rw [Real.rpow_neg hz.le]
    calc
      _ = 1/Z^(5*P+1) := (one_div _).symm
      _ ≤ 1/reflectedSourceRatio e k := div_le_div_of_nonneg_left zero_le_one hR0 hRU
      _ ≤ _ := div_le_div_of_nonneg_right hL hR0.le
  have hEU : L/reflectedSourceRatio e k ≤ Z^P := (div_le_self hL0.le hR.1).trans hLU
  have hexp : P ≤ uniformReflectionScale P := by unfold uniformReflectionScale; linarith
  have h2b : 2*(B/(Ideal.absNorm D : ℝ)) ≤ Z^(uniformReflectionScale P) := by
    calc
      _ ≤ Z*(Z^P) := mul_le_mul (by linarith : (2 : ℝ) ≤ Z) hbU hb0.le hz.le
      _ = Z^(P+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by unfold uniformReflectionScale; linarith)
  refine ⟨hb0,div_pos hL0 (inputSectorScale_pos k),hd0,
    hbU.trans (Real.rpow_le_rpow_of_exponent_le hz1 hexp),h2b,?_,?_,?_⟩
  · rw [heq]
    exact (Real.rpow_le_rpow_of_exponent_le hz1 (by unfold uniformReflectionScale; linarith)).trans hElo
  · rw [heq]
    exact hEU.trans (Real.rpow_le_rpow_of_exponent_le hz1 hexp)
  · unfold modeFrequencyCutoff
    rw [heq]
    calc
      _ ≤ (4*(Z^P)^2/Z^(-(5*P+1)))*Z := by
        apply mul_le_mul _ (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz1 hs)
          (Real.rpow_nonneg hz.le _) (by positivity)
        exact div_le_div₀ (by positivity) (by gcongr) (Real.rpow_pos_of_pos hz _) hElo
      _ = 4*Z^(7*P+2) := by
        rw [← Real.rpow_mul_natCast hz.le, Real.rpow_neg hz.le, div_inv_eq_mul]
        calc
          _ = 4*(Z^(P*(2 : ℝ))*Z^(5*P+1)*Z^(1 : ℝ)) := by rw [Real.rpow_one]; norm_num; ring
          _ = _ := by rw [← Real.rpow_add hz, ← Real.rpow_add hz]; congr 1; congr 1; ring
      _ ≤ Z*Z^(7*P+2) := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz.le _)
      _ = Z^(7*P+3) := by
        rw [show 7*P+3 = (7*P+2)+1 by ring,Real.rpow_add hz (7*P+2) 1,Real.rpow_one]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by unfold uniformReflectionScale; linarith)


def simpleReflectionValues (F : Finset (Ideal O)) (L B H : ℝ) : Finset ℝ :=
  insert 0 ((BadFrequencySectors.boundedKeys L).biUnion fun k =>
    (gcdPool (fun I : F => I.val)).biUnion fun D =>
      (idealDivisors (commonMaskIdeal D)).image fun e =>
        simpleModeProfile (selectedQuotientRows F D) (L/inputSectorScale k)
          (B/(Ideal.absNorm D : ℝ)) H (idealGenerator e))

def simpleReflectionProfile (F : Finset (Ideal O)) (L B H : ℝ) : ℝ :=
  (simpleReflectionValues F L B H).sup' (Finset.insert_nonempty _ _) (fun x => x)

theorem simpleReflectionProfile_nonneg (F : Finset (Ideal O)) (L B H : ℝ) :
    0 ≤ simpleReflectionProfile F L B H := by
  unfold simpleReflectionProfile simpleReflectionValues
  exact Finset.le_sup' (fun x : ℝ => x) (Finset.mem_insert_self _ _)

theorem simpleModeProfile_le (F : Finset (Ideal O)) (L B H : ℝ)
    (k : Oˣ × ℕ × ℕ) (hk : k ∈ BadFrequencySectors.boundedKeys L)
    (D : Ideal O) (hD : D ∈ gcdPool (fun I : F => I.val))
    (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D)) :
    simpleModeProfile (selectedQuotientRows F D) (L/inputSectorScale k)
      (B/(Ideal.absNorm D : ℝ)) H (idealGenerator e) ≤ simpleReflectionProfile F L B H := by
  unfold simpleReflectionProfile
  apply Finset.le_sup' (fun x : ℝ => x)
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k,hk,
    Finset.mem_biUnion.mpr ⟨D,hD,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩⟩)

theorem reflectionBudget_le_of_modes (F : Finset (Ideal O)) (L B H Cnear Ctail ε K : ℝ)
    (hε : 0 < ε) (A : ℕ) (hK : 0 ≤ K)
    (hbound : ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      modeBudget (selectedQuotientRows F D) QuadraticInitialBound.sieveCutoff L
        (B/(Ideal.absNorm D : ℝ)) H Cnear Ctail (idealGenerator e) ε hε A ≤ K) :
    reflectionBudget F L B H Cnear Ctail ε hε A ≤ K := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hK
  · obtain ⟨D,hD,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    exact hbound D hD e he

theorem allSourceReflectionBudget_le_of_modes (F : Finset (Ideal O))
    (L B H Cnear Ctail ε K : ℝ) (hε : 0 < ε) (A : ℕ) (hK : 0 ≤ K)
    (hbound : ∀ k ∈ BadFrequencySectors.boundedKeys L,
      ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      modeBudget (selectedQuotientRows F D) QuadraticInitialBound.sieveCutoff
        (L/inputSectorScale k) (B/(Ideal.absNorm D : ℝ)) H Cnear Ctail (idealGenerator e) ε hε A ≤ K) :
    allSourceReflectionBudget F L B H Cnear Ctail ε hε A ≤ K := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hK
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact reflectionBudget_le_of_modes F _ B H Cnear Ctail ε K hε A hK (hbound k hk)

theorem sharedDivisorCost_uniform (P η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hbudget : 2*P*ε ≤ η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z B : ℝ, 1 ≤ Z → 0 ≤ B → B ≤ Z^P →
      sharedDivisorCost reflectionBadIdeal B ε hε ≤ C*Z^η := by
  let C₀ := (idealDivisorConstant ε hε)^2*(Ideal.absNorm reflectionBadIdeal : ℝ)^ε
  have hC₀ : 0 ≤ C₀ := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C₀+1,by positivity,?_⟩
  intro Z B hZ hB hBU
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  calc
    _ = C₀*(B^ε)^2 := by
      unfold sharedDivisorCost C₀
      rw [Real.mul_rpow hB (Nat.cast_nonneg _)]
      ring
    _ ≤ C₀*((Z^P)^ε)^2 := by
      apply mul_le_mul_of_nonneg_left _ hC₀
      exact pow_le_pow_left₀ (Real.rpow_nonneg hB _) (Real.rpow_le_rpow hB hBU hε.le) 2
    _ = C₀*Z^(2*P*ε) := by
      rw [← Real.rpow_mul hz.le, ← Real.rpow_mul_natCast hz.le]
      congr 1
      norm_num
      ring
    _ ≤ C₀*Z^η := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hbudget) hC₀
    _ ≤ _ := by gcongr; linarith


/-- Uniform polynomial-range squarefree reflection for the ACTUAL all-source
selected norm. The only hypotheses are original row/source ranges and the
actual squarefree/ray conditions. All finite costs and the full Schwartz tail
are absorbed. The displayed finite profile retains every `D,e,k` label. -/
theorem squarefree_uniform_reflection (P loss : ℝ) (hP : 0 ≤ P) (hloss : 0 < loss) :
    ∃ C Z₀ s : ℝ, 0 < C ∧ 0 < s ∧ s ≤ 1 ∧ s ≤ loss/3 ∧
      ∀ (Z L B : ℝ) (F S : Finset (Ideal O)),
      Z₀ ≤ Z → 1 ≤ L → L ≤ Z^P → 1 ≤ B → B ≤ Z^P →
      (∀ I ∈ F, Admissible I) →
      (∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
        (Ideal.span {(36 : O)} : Ideal O)) →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤
        C*Z^loss*simpleReflectionProfile F L B (Z^s) := by
  let Q := uniformReflectionScale P
  have hQ : 0 ≤ Q := by dsimp [Q,uniformReflectionScale]; positivity
  let η := loss/3
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := η/(2*(Q+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεid : ε*(2*(Q+1)) = η := by dsimp [ε]; field_simp
  have hεbudget : Q*ε ≤ η/2 := by nlinarith
  let s := min 1 η
  have hs : 0 < s := lt_min zero_lt_one hη
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsη : s ≤ η := min_le_right _ _
  obtain ⟨A,hAge⟩ := exists_nat_ge (8*Q/s)
  have hA : 8*Q ≤ s*(A : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hs).mp hAge
  obtain ⟨Cn,Ct,hCn,hCt,hreflection⟩ := squarefree_all_source_reflection A
  obtain ⟨Cm,hCm,hmode⟩ := modeBudget_uniform QuadraticInitialBound.sieveCutoff Q η ε Cn Ct
    hQ hη hε hεbudget hCn hCt
  obtain ⟨Co,hCo,houter⟩ := sharedDivisorCost_uniform Q η ε hη hε (by nlinarith)
  obtain ⟨Ci,hCi,hinput⟩ := badSector_small_power P η hP hη
  let C := (1/6 : ℝ)*Co*Ci*Cm
  let Z₀ := max 4 (32*(Ideal.absNorm reflectionBadIdeal : ℝ))
  refine ⟨C,Z₀,s,by dsimp [C]; positivity,hs,hs1,hsη,?_⟩
  intro Z L B F S hZ₀ hL hLU hB hBU hF hmod hN hS
  have hZ : 4 ≤ Z := (le_max_left _ _).trans hZ₀
  have hbad : 32*(Ideal.absNorm reflectionBadIdeal : ℝ) ≤ Z := (le_max_right _ _).trans hZ₀
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := by linarith
  have h2BU : 2*B ≤ Z^Q := by
    calc
      _ ≤ Z*(Z^P) := mul_le_mul (by linarith : (2 : ℝ) ≤ Z) hBU hB0.le hz.le
      _ = Z^(P+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by dsimp [Q,uniformReflectionScale]; linarith)
  have hout := houter Z (2*B) hz1 (by positivity) h2BU
  have hin := hinput Z L hz1 hL0 hLU
  have hprofile0 := simpleReflectionProfile_nonneg F L B (Z^s)
  have hbudget : allSourceReflectionBudget F L B (Z^s) Cn Ct ε hε A ≤
      Cm*Z^η*simpleReflectionProfile F L B (Z^s) := by
    apply allSourceReflectionBudget_le_of_modes F L B (Z^s) Cn Ct ε _ hε A (by positivity)
    intro k hk D hD e he
    obtain ⟨hb,hl,hd,hbU,h2bU,hEl,hEu,hTu⟩ := reflection_polynomial_ranges F hF Z P L B s
      hZ hP hbad hL hLU hB hBU hs1 (fun I hI => (hN I hI).2) D hD e he k hk
    have hDn := (selectedGcd_spec F hF (2*B) (fun I hI => (hN I hI).2) D hD).1.1
    have hm := hmode (selectedQuotientRows F D) Z (L/inputSectorScale k)
      (B/(Ideal.absNorm D : ℝ)) s (idealGenerator e) A (by linarith) hl hb hd
      hbU h2bU hEl hEu hTu (quotientRows_card_le F hF D hDn B hB0.le hN) hA
    exact hm.trans (mul_le_mul_of_nonneg_left (simpleModeProfile_le F L B (Z^s) k hk D hD e he)
      (by positivity))
  have hSD0 : 0 ≤ sharedDivisorCost reflectionBadIdeal (2*B) ε hε := by
    unfold sharedDivisorCost
    exact mul_nonneg
      (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε))
      (mul_nonneg (idealDivisorConstant_pos ε hε).le
        (Real.rpow_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) ε))
  have hb0 := allSourceReflectionBudget_nonneg F L B (Z^s) Cn Ct ε hε A
  calc
    _ ≤ (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε *
        ((BadFrequencySectors.boundedKeys L).card : ℝ)*
          allSourceReflectionBudget F L B (Z^s) Cn Ct ε hε A :=
      hreflection F hF hmod S L B (Z^s) ε hε hL0 hB0 (Real.rpow_nonneg hz.le _) hN hS
    _ ≤ (1/6 : ℝ)*(Co*Z^η)*(Ci*Z^η)*(Cm*Z^η*simpleReflectionProfile F L B (Z^s)) := by
      gcongr
    _ = C*(Z^η*Z^η*Z^η)*simpleReflectionProfile F L B (Z^s) := by dsimp [C]; ring
    _ = _ := by
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 2
      dsimp [η]
      ring


/-- The exact reflected cutoff; the input bad sector is part of `R`. -/
def reflectedFrequencyCutoff (L B H : ℝ) (D e : Ideal O) (k : Oˣ × ℕ × ℕ) : ℝ :=
  4*B^2*reflectedSourceRatio e k/(L*(Ideal.absNorm D : ℝ)^2)*H

theorem modeFrequencyCutoff_eq_reflected (L B H : ℝ) (D e : Ideal O) (k : Oˣ × ℕ × ℕ) :
    modeFrequencyCutoff (L/inputSectorScale k) (B/(Ideal.absNorm D : ℝ)) H (idealGenerator e) =
      reflectedFrequencyCutoff L B H D e k := by
  unfold modeFrequencyCutoff reflectedFrequencyCutoff reflectedSourceRatio
  rw [idealGenerator_norm_sq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow]
  ring

theorem simpleModeProfile_eq_reflected (rows : Finset O) (L B H : ℝ)
    (D e : Ideal O) (k : Oˣ × ℕ × ℕ) :
    simpleModeProfile rows (L/inputSectorScale k) (B/(Ideal.absNorm D : ℝ)) H (idealGenerator e) =
      L/reflectedSourceRatio e k +
        (L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k)) *
          selectedNorm rows (selectedFrequencyPool
            (reflectionFrequencies (reflectedFrequencyCutoff L B H D e k))
            (reflectedFrequencyCutoff L B H D e k)) := by
  unfold simpleModeProfile
  rw [modeFrequencyCutoff_eq_reflected,idealGenerator_norm_sq]
  unfold reflectedSourceRatio
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

/-- Every actual reflected ordinary source has the displayed length. -/
theorem reflectedFrequencyPool_spec (L B H : ℝ) (D e : Ideal O) (k : Oˣ × ℕ × ℕ)
    (hY : 0 ≤ reflectedFrequencyCutoff L B H D e k)
    (I : Ideal O) (hI : I ∈ selectedFrequencyPool
      (reflectionFrequencies (reflectedFrequencyCutoff L B H D e k))
      (reflectedFrequencyCutoff L B H D e k)) :
    Supported I ∧ (Ideal.absNorm I : ℝ) ≤ reflectedFrequencyCutoff L B H D e k :=
  selectedFrequencyPool_spec _ _ (reflectionFrequencies_bound _ hY) I hI

/-- The uniform reflection's finite maximum can be consumed one actual
`k,D,e` mode at a time. This is scalar finite-max elimination, not an assumed
reflection inequality. -/
theorem simpleReflectionProfile_le_of_modes (F : Finset (Ideal O)) (L B H K : ℝ)
    (hK : 0 ≤ K)
    (hbound : ∀ k ∈ BadFrequencySectors.boundedKeys L,
      ∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
      L/reflectedSourceRatio e k + (L*(Ideal.absNorm D : ℝ)/(B*reflectedSourceRatio e k)) *
        selectedNorm (selectedQuotientRows F D) (selectedFrequencyPool
          (reflectionFrequencies (reflectedFrequencyCutoff L B H D e k))
          (reflectedFrequencyCutoff L B H D e k)) ≤ K) :
    simpleReflectionProfile F L B H ≤ K := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hK
  · obtain ⟨k,hk,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨D,hD,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
    rw [simpleModeProfile_eq_reflected]
    exact hbound k hk D hD e he

/-- The factor four in the precise dual cutoff is absorbed in any larger
ambient exponent reserve, at a threshold fixed before row/source data. -/
theorem reflectedFrequencyCutoff_le_power (Z loss s L B : ℝ) (D e : Ideal O)
    (k : Oˣ × ℕ × ℕ) (hgap : 0 < loss-s)
    (hZ : (4 : ℝ)^(1/(loss-s)) ≤ Z) (hL : 0 ≤ L) :
    reflectedFrequencyCutoff L B (Z^s) D e k ≤
      Z^loss * (B^2*reflectedSourceRatio e k/(L*(Ideal.absNorm D : ℝ)^2)) := by
  have hz : 0 < Z := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<4) _).trans_le hZ
  have h4 : (4 : ℝ) ≤ Z^(loss-s) := by
    calc
      _ = ((4 : ℝ)^(1/(loss-s)))^(loss-s) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ)≤4)]
        rw [one_div_mul_cancel hgap.ne',Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hZ hgap.le
  have hfactor : 4*Z^s ≤ Z^loss := by
    apply (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hz.le s)).trans_eq
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hratio : 0 ≤ B^2*reflectedSourceRatio e k/(L*(Ideal.absNorm D : ℝ)^2) := by
    unfold reflectedSourceRatio
    exact div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (inputSectorScale_pos k).le))
      (mul_nonneg hL (sq_nonneg _))
  calc
    _ = (4*Z^s)*(B^2*reflectedSourceRatio e k/(L*(Ideal.absNorm D : ℝ)^2)) := by
      unfold reflectedFrequencyCutoff
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hratio

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.squarefree_uniform_reflection
#print axioms Qrh.JointDetector.simpleReflectionProfile_le_of_modes
#print axioms Qrh.JointDetector.reflectedFrequencyCutoff_le_power
