/- Copyright (c) 2026 Sil. Apache-2.0.
Attach the explicit dyadic growth majorant to the literal Poisson family.
-/
import Candidate.FourthPower.SieveGrowthAlgebra

set_option autoImplicit false
namespace Candidate.FourthPower.SievePoissonSeries
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open SexticSieve SievePairPoisson SieveBandBound SieveGrowthAlgebra
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

def fiberBand {n : Type*} [Fintype n] (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (a b : n → ℂ)
    (u v : SieveColumnPartition.Label N) (j : ℕ) : ℝ :=
  ∑ x : CubicSieve.frequencyDyad j, ‖∑ i : SieveColumnPartition.Fiber N cols hc u,
    ∑ k : SieveColumnPartition.Fiber N cols hc v,
      if IsCoprime (cols i.val) (cols k.val) then
        dualTerm (cols i.val) (cols k.val) (hc i.val) (hc k.val) (a i.val) (b k.val) W M x.val else 0‖

theorem prefactor_general (ε Cb D C A S N X t H E : ℝ) (hN : 0 < N) (hX : 0 < X) :
    (Cb*X^ε)*(D/(1+t*X)^3)*(C*A*S*(2*N^2*X)^(2*ε)*H)*E =
    (Cb*D*C*S*(2 : ℝ)^(2*ε))*A*N^(4*ε)*(X^(3*ε)*H/(1+t*X)^3)*E := by
  rw [Real.mul_rpow (by positivity : 0 ≤ 2*N^2) hX.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg N),
    ← Real.rpow_natCast_mul hN.le,Nat.cast_ofNat,
    show (2 : ℝ)*(2*ε)=4*ε by ring,
    show 3*ε=ε+2*ε by ring,Real.rpow_add hX]
  ring

theorem fixed_dyadic_bound (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α A : ℝ), 1 ≤ α → 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ {n : Type*} [Fintype n] (N : ℝ), 1 ≤ N → ∀ (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (M : ℝ), 0 < M → ∀ (u v : SieveColumnPartition.Label N),
        SieveColumnPartition.scale u ≤ N → SieveColumnPartition.scale v ≤ N →
        ∀ (a b : n → ℂ) (j : ℕ),
        fiberBand N cols hc W M a b u v j ≤ C₀*A*N^(4*ε)*
          dyadicGrowth ε α (M/(2*SieveColumnPartition.scale u*SieveColumnPartition.scale v))
            (mainCoefficient N M α) (secondaryCoefficient N M) j *
          Real.sqrt ((∑ i : SieveColumnPartition.Fiber N cols hc u, ‖a i.val‖^2)*
            (∑ k : SieveColumnPartition.Fiber N cols hc v, ‖b k.val‖^2)) := by
  obtain ⟨C,D,hC,hD,hb⟩ := fixed_column_band ε hε W 3
  obtain ⟨Cb,hCb,hcb⟩ := SieveFrequencyGeometry.labels_small_power ε hε
  let S := IdealCoprimeSieveOperator.supportConstant ε hε
  have hS : 0 < S := IdealCoprimeSieveOperator.supportConstant_pos ε hε
  let Z := Cb*D*C*S*(2 : ℝ)^(2*ε)
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  refine ⟨Z+1,by positivity,?_⟩
  intro α A hα hA hGrowth n _ N hN cols hc hf hi hn M hM u v hu hv a b j
  let P := SieveColumnPartition.scale u
  let Q := SieveColumnPartition.scale v
  let X : ℝ := (2 : ℝ)^j
  let t := M/(2*P*Q)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hP : 1 ≤ P := divisorDyadicScale_ge_one u.2.val
  have hQ : 1 ≤ Q := divisorDyadicScale_ge_one v.2.val
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hX : 0 < X := zero_lt_one.trans_le hX1
  have ht : 0 < t := by dsimp only [t]; positivity
  have hR : ∀ x ∈ CubicSieve.frequencyDyad j,
      x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X := by
    intro x hx
    have hh := CubicSieve.frequencyDyad_bounds j x hx
    exact ⟨hh.1,hh.2.2⟩
  have hRlo : ∀ x ∈ CubicSieve.frequencyDyad j,
      X/2 ≤ (Ideal.absNorm (Ideal.span {x}) : ℝ) :=
    fun x hx => (CubicSieve.frequencyDyad_bounds j x hx).2.1
  have hh := hb N (zero_le_one.trans hN) cols hc hf hi hn X hX
    (CubicSieve.frequencyDyad j) hR hRlo M hM u v a b
  have hg := sqrt_density_scaled ε hε C A N M X P Q α hC.le hA hN0 hM hX
    hP hu hQ hv hα
    (hGrowth _ _ (by positivity) (by linarith))
    (hGrowth _ _ (by positivity) (by linarith))
  have he : M*X/(2*P*Q)=t*X := by dsimp only [t]; ring
  rw [he] at hg
  change fiberBand N cols hc W M a b u v j ≤
    (Fintype.card (SieveFrequencyGeometry.BadLabel X) : ℝ)*(D/(1+M*X/(2*P*Q))^3)*
      Real.sqrt (density ε hε C P (N*X/Q)*density ε hε C Q (N*X/P))*_ at hh
  rw [he] at hh
  have hnum : 0 ≤ numerator N M α (t*X) := by
    unfold numerator mainCoefficient secondaryCoefficient
    positivity
  have hmul := mul_le_mul
    (mul_le_mul_of_nonneg_right (hcb X hX1) (by positivity : 0 ≤ D/(1+t*X)^3)) hg
    (Real.sqrt_nonneg _) (by positivity : 0 ≤ (Cb*X^ε)*(D/(1+t*X)^3))
  have hprod := mul_le_mul_of_nonneg_right hmul
    (Real.sqrt_nonneg ((∑ i : SieveColumnPartition.Fiber N cols hc u, ‖a i.val‖^2)*
      (∑ k : SieveColumnPartition.Fiber N cols hc v, ‖b k.val‖^2)))
  apply (hh.trans hprod).trans
  rw [prefactor_general _ _ _ _ _ _ _ _ _ _ _ hN0 hX]
  change Z*A*N^(4*ε)*dyadicGrowth ε α t (mainCoefficient N M α) (secondaryCoefficient N M) j*_ ≤ _
  have hg0 : 0 ≤ dyadicGrowth ε α t (mainCoefficient N M α) (secondaryCoefficient N M) j := by
    unfold dyadicGrowth mainCoefficient secondaryCoefficient
    positivity
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ hg0
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hA

theorem fixed_series_bound (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ {n : Type*} [Fintype n] (N : ℝ), 1 ≤ N → ∀ (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (M : ℝ), 0 < M → ∀ (u v : SieveColumnPartition.Label N),
        SieveColumnPartition.scale u ≤ N → SieveColumnPartition.scale v ≤ N →
        ∀ a b : n → ℂ,
        Summable (fiberBand N cols hc W M a b u v) ∧
        (∑' j, fiberBand N cols hc W M a b u v j) ≤ C*A*N^(4*ε)*
          (M/(2*SieveColumnPartition.scale u*SieveColumnPartition.scale v))^(-(3*ε))*
          (mainCoefficient N M α+secondaryCoefficient N M)*
          Real.sqrt ((∑ i : SieveColumnPartition.Fiber N cols hc u, ‖a i.val‖^2)*
            (∑ k : SieveColumnPartition.Fiber N cols hc v, ‖b k.val‖^2)) := by
  obtain ⟨C,hC,hb⟩ := fixed_dyadic_bound ε hε W
  obtain ⟨K,hK,hk⟩ := dyadic_growth_sum ε α hε hεs hα hα₂
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro A hA hGrowth n _ N hN cols hc hf hi hn M hM u v hu hv a b
  let t := M/(2*SieveColumnPartition.scale u*SieveColumnPartition.scale v)
  let U := mainCoefficient N M α
  let V := secondaryCoefficient N M
  let E := Real.sqrt ((∑ i : SieveColumnPartition.Fiber N cols hc u, ‖a i.val‖^2)*
    (∑ k : SieveColumnPartition.Fiber N cols hc v, ‖b k.val‖^2))
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hp := SieveColumnPartition.scale_pos u
  have hq := SieveColumnPartition.scale_pos v
  have ht : 0 < t := by dsimp only [t]; positivity
  have hU : 0 ≤ U := by dsimp only [U,mainCoefficient]; positivity
  have hV : 0 ≤ V := by dsimp only [V,secondaryCoefficient]; positivity
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  obtain ⟨hs,hb'⟩ := hk t U V ht hU hV
  have hg : Summable (fun j => C*A*N^(4*ε)*dyadicGrowth ε α t U V j*E) :=
    (hs.mul_left (C*A*N^(4*ε))).mul_right E
  have hpoint (j : ℕ) : fiberBand N cols hc W M a b u v j ≤
      C*A*N^(4*ε)*dyadicGrowth ε α t U V j*E :=
    hb α A hα hA hGrowth N hN cols hc hf hi hn M hM u v hu hv a b j
  have hfiber := hg.of_nonneg_of_le
    (fun j => Finset.sum_nonneg (fun x _ => norm_nonneg _)) hpoint
  refine ⟨hfiber,(hfiber.tsum_le_tsum hpoint hg).trans ?_⟩
  rw [tsum_mul_right,tsum_mul_left]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb' (show 0 ≤ C*A*N^(4*ε) by positivity)) hE
  exact hm.trans_eq (by dsimp only [t,U,V,E]; ring)

theorem scale_loss (ε N M P Q : ℝ) (hε : 0 < ε) (hN : 0 < N) (hM : 0 < M)
    (hP : 0 < P) (hPN : P ≤ N) (hQ : 0 < Q) (hQN : Q ≤ N) :
    N^(4*ε)*(M/(2*P*Q))^(-(3*ε)) ≤ (2 : ℝ)^(3*ε)*N^(10*ε)*M^(-(3*ε)) := by
  rw [Real.rpow_neg_eq_inv_rpow,inv_div]
  have hpq : 2*P*Q ≤ 2*N^2 := by
    have h := mul_le_mul hPN hQN hQ.le hN.le
    nlinarith
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 2*P*Q/M)
    (div_le_div_of_nonneg_right hpq hM.le) (by positivity : 0 ≤ 3*ε)
  calc
    _ ≤ N^(4*ε)*(2*N^2/M)^(3*ε) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by
      rw [Real.div_rpow (by positivity : 0 ≤ 2*N^2) hM.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg N),
        ← Real.rpow_natCast_mul hN.le,Nat.cast_ofNat,
        show (2 : ℝ)*(3*ε)=6*ε by ring,Real.rpow_neg hM.le]
      have he : N^(4*ε)*N^(6*ε)=N^(10*ε) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (2 : ℝ)^(3*ε)*(N^(4*ε)*N^(6*ε))*(M^(3*ε))⁻¹ := by ring
        _ = _ := by rw [he]

/-- Uniformly sum each pair of column blocks. Empty blocks contribute zero;
nonempty blocks have scales in [1,N]. All original coefficients are retained. -/
theorem uniform_fiber_series (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ {n : Type*} [Fintype n] (N : ℝ), 1 ≤ N → ∀ (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (M : ℝ), 0 < M → ∀ (u v : SieveColumnPartition.Label N) (a b : n → ℂ),
        Summable (fiberBand N cols hc W M a b u v) ∧
        (∑' j, fiberBand N cols hc W M a b u v j) ≤ C*A*N^(10*ε)*M^(-(3*ε))*
          (mainCoefficient N M α+secondaryCoefficient N M)*
          Real.sqrt ((∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2)) := by
  obtain ⟨C,hC,hb⟩ := fixed_series_bound ε α hε hεs hα hα₂ W
  refine ⟨C*(2 : ℝ)^(3*ε),by positivity,?_⟩
  intro A hA hGrowth n _ N hN cols hc hf hi hn M hM u v a b
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hm : 0 ≤ mainCoefficient N M α+secondaryCoefficient N M := by
    unfold mainCoefficient secondaryCoefficient
    positivity
  by_cases hu : Nonempty (SieveColumnPartition.Fiber N cols hc u)
  · by_cases hv : Nonempty (SieveColumnPartition.Fiber N cols hc v)
    · obtain ⟨i⟩ := hu
      obtain ⟨k⟩ := hv
      have hu' := fiber_scale_bounds N cols hc hn u i
      have hv' := fiber_scale_bounds N cols hc hn v k
      obtain ⟨hs,hb'⟩ := hb A hA hGrowth N hN cols hc hf hi hn M hM u v hu'.2 hv'.2 a b
      refine ⟨hs,hb'.trans ?_⟩
      have hscale := scale_loss ε N M _ _ hε hN0 hM
        (SieveColumnPartition.scale_pos u) hu'.2 (SieveColumnPartition.scale_pos v) hv'.2
      have he := Real.sqrt_le_sqrt
        (mul_le_mul (SieveColumnPartition.fiber_mass_le N cols hc a u)
          (SieveColumnPartition.fiber_mass_le N cols hc b v)
          (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
      have hh := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale
          (show 0 ≤ C*A by positivity)) hm) he (Real.sqrt_nonneg _)
        (show 0 ≤ C*A*((2 : ℝ)^(3*ε)*N^(10*ε)*M^(-(3*ε)))*
          (mainCoefficient N M α+secondaryCoefficient N M) by positivity)
      convert hh using 1 <;> ring
    · letI : IsEmpty (SieveColumnPartition.Fiber N cols hc v) := ⟨fun k => hv ⟨k⟩⟩
      have hz : fiberBand N cols hc W M a b u v = fun _ => 0 := by
        funext j
        simp [fiberBand]
      rw [hz]
      refine ⟨summable_zero,?_⟩
      rw [tsum_zero]
      positivity
  · letI : IsEmpty (SieveColumnPartition.Fiber N cols hc u) := ⟨fun i => hu ⟨i⟩⟩
    have hz : fiberBand N cols hc W M a b u v = fun _ => 0 := by
      funext j
      simp [fiberBand]
    rw [hz]
    refine ⟨summable_zero,?_⟩
    rw [tsum_zero]
    positivity

def wholeBand {n : Type*} [Fintype n] (cols : n → Id) (hc : ∀ i, Supported (cols i))
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (a b : n → ℂ) (j : ℕ) : ℝ :=
  ∑ x : CubicSieve.frequencyDyad j, ‖∑ i, ∑ k, if IsCoprime (cols i) (cols k) then
    dualTerm (cols i) (cols k) (hc i) (hc k) (a i) (b k) W M x.val else 0‖

theorem wholeBand_le {n : Type*} [Fintype n] (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (a b : n → ℂ) (j : ℕ) :
    wholeBand cols hc W M a b j ≤ ∑ u : SieveColumnPartition.Label N,
      ∑ v : SieveColumnPartition.Label N, fiberBand N cols hc W M a b u v j := by
  let F (x : CubicSieve.frequencyDyad j) (i k : n) : ℂ :=
    if IsCoprime (cols i) (cols k) then dualTerm (cols i) (cols k) (hc i) (hc k)
      (a i) (b k) W M x.val else 0
  let H (x : CubicSieve.frequencyDyad j) (u v : SieveColumnPartition.Label N) : ℝ :=
    ‖∑ i : SieveColumnPartition.Fiber N cols hc u,
      ∑ k : SieveColumnPartition.Fiber N cols hc v, F x i.val k.val‖
  change (∑ x, ‖∑ i, ∑ k, F x i k‖) ≤ ∑ u, ∑ v, ∑ x, H x u v
  calc
    _ ≤ ∑ x, ∑ u, ∑ v, H x u v := by
      apply Finset.sum_le_sum
      intro x _
      rw [pair_partition N cols hc (F x)]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => norm_sum_le _ _))
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun u _ => Finset.sum_comm)

/-- Full nonzero Poisson series with every frequency and column included.
The only analytic hypothesis is the explicit completed-norm growth bound
that will be supplied by the exponent induction. No constant depends on
the two lengths, the coefficient family, or its cardinality. -/
theorem all_series_bound (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ {n : Type*} [Fintype n] (N : ℝ), 1 ≤ N → ∀ (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (M : ℝ), 0 < M → ∀ a b : n → ℂ,
        Summable (wholeBand cols hc W M a b) ∧
        (∑' j, wholeBand cols hc W M a b j) ≤ C*A*N^(12*ε)*M^(-(3*ε))*
          (mainCoefficient N M α+secondaryCoefficient N M)*
          Real.sqrt ((∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2)) := by
  obtain ⟨C,hC,hb⟩ := uniform_fiber_series ε α hε hεs hα hα₂ W
  obtain ⟨L,hL,hl⟩ := SieveColumnPartition.labels_small_power ε hε
  refine ⟨C*L^2,by positivity,?_⟩
  intro A hA hGrowth n _ N hN cols hc hf hi hn M hM a b
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let f := fiberBand N cols hc W M a b
  let Z := mainCoefficient N M α+secondaryCoefficient N M
  let E := Real.sqrt ((∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2))
  let B := C*A*N^(10*ε)*M^(-(3*ε))*Z*E
  have hZ : 0 ≤ Z := by dsimp only [Z,mainCoefficient,secondaryCoefficient]; positivity
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have h (u v : SieveColumnPartition.Label N) : Summable (f u v) ∧ (∑' j, f u v j) ≤ B :=
    hb A hA hGrowth N hN cols hc hf hi hn M hM u v a b
  have hs : Summable (fun j => ∑ u, ∑ v, f u v j) :=
    summable_sum (fun u _ => summable_sum (fun v _ => (h u v).1))
  have ht := wholeBand_le N cols hc W M a b
  have hw := hs.of_nonneg_of_le (fun j => Finset.sum_nonneg (fun x _ => norm_nonneg _)) ht
  refine ⟨hw,(hw.tsum_le_tsum ht hs).trans ?_⟩
  have he : (∑' j, ∑ u, ∑ v, f u v j) = ∑ u, ∑ v, ∑' j, f u v j := by
    rw [Summable.tsum_finsetSum (fun u _ => summable_sum (fun v _ => (h u v).1))]
    exact Finset.sum_congr rfl (fun u _ => Summable.tsum_finsetSum (fun v _ => (h u v).1))
  rw [he]
  have hsum : (∑ u, ∑ v, ∑' j, f u v j) ≤ (Fintype.card (SieveColumnPartition.Label N) : ℝ)^2*B := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun v _ => (h u v).2))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
    exact hh.trans_eq (by ring)
  have hcard := pow_le_pow_left₀ (Nat.cast_nonneg (Fintype.card (SieveColumnPartition.Label N)) :
    (0 : ℝ) ≤ Fintype.card (SieveColumnPartition.Label N)) (hl N hN) 2
  have hp : (N^ε)^2*N^(10*ε)=N^(12*ε) := by
    rw [← Real.rpow_mul_natCast hN0.le,Nat.cast_ofNat,← Real.rpow_add hN0]
    congr 1
    ring
  apply hsum.trans ((mul_le_mul_of_nonneg_right hcard hB).trans_eq ?_)
  dsimp only [B,Z,E]
  rw [mul_pow]
  calc
    _ = C*L^2*A*((N^ε)^2*N^(10*ε))*M^(-(3*ε))*
        (mainCoefficient N M α+secondaryCoefficient N M)*
        Real.sqrt ((∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2)) := by ring
    _ = _ := by rw [hp]

end
end Candidate.FourthPower.SievePoissonSeries
