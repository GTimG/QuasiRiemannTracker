/- Copyright (c) 2026 Sil. Apache-2.0.
Bilinear operator interface for the actual smoothed Poisson family.
Two independent coefficient vectors are kept throughout, so a bound on
quadratic forms is never silently identified with an operator norm. -/
import Candidate.SilPrior.FourthPower.SieveGcdNorm
import Candidate.SilPrior.FourthPower.SieveWindow

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SievePoissonBound
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge FiniteSieveOperator
open SieveSmoothed SievePairPoisson SexticSieve SieveGcd ConcreteTraceCRT
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

def pairing {m n : Type*} [Fintype m] [Fintype n]
    (G : Matrix m n ℂ) (a : m → ℂ) (b : n → ℂ) : ℂ :=
  ∑ i, star (a i)*(∑ j, G i j*b j)

theorem pairing_image {m n : Type*} [Fintype m] [Fintype n]
    (G : Matrix m n ℂ) (b : n → ℂ) :
    pairing G (fun i => ∑ j, G i j*b j) b =
      ((∑ i, ‖∑ j, G i j*b j‖^2 : ℝ) : ℂ) := by
  unfold pairing
  simp only [← starRingEnd_apply,Complex.conj_mul',Complex.ofReal_sum,Complex.ofReal_pow]

/-- A sufficient bilinear estimate for the actual operator norm. There is
no positivity or Hermitian hypothesis on the matrix. -/
theorem operator_norm_le_of_pairing {m n : Type*} [Fintype m] [Fintype n]
    (G : Matrix m n ℂ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (a : m → ℂ) (b : n → ℂ), ‖pairing G a b‖^2 ≤
      K^2*(∑ i, ‖a i‖^2)*(∑ j, ‖b j‖^2)) : ‖operator G‖ ≤ K := by
  apply (sq_le_sq₀ (norm_nonneg _) hK).mp
  apply squared_norm_le_of_energy G (K^2) (sq_nonneg _)
  intro b
  have hb := h (fun i => ∑ j, G i j*b j) b
  rw [pairing_image,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hb
  have hs : 0 ≤ ∑ i, ‖∑ j, G i j*b j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht : 0 ≤ ∑ j, ‖b j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : (∑ i, ‖∑ j, G i j*b j‖^2) = 0
  · rw [hz]
    positivity
  · have hp : 0 < ∑ i, ‖∑ j, G i j*b j‖^2 := lt_of_le_of_ne hs (Ne.symm hz)
    nlinarith

theorem gram_pairing {n : Type*} [Fintype n] (cols : n → Id)
    (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    pairing (gramMatrix cols W M) a b =
      ∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
        star (a i)*b j*∑' z : O, (star (row (cols i) z)*row (cols j) z)*
          W (‖eisEmbedding z‖^2/M) else 0 := by
  unfold pairing
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : IsCoprime (cols i) (cols j) <;>
    simp only [gramMatrix,h,ite_true,ite_false]
  · ring
  · ring

theorem gram_pairing_poisson {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    pairing (gramMatrix cols W M) a b =
      (M : ℂ)*∑' k : O, ∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
        dualTerm (cols j) (cols i) (hc j) (hc i) (b j) (a i) W M k else 0 := by
  have hs (i j : n) : Summable (fun k : O => if IsCoprime (cols i) (cols j) then
      dualTerm (cols j) (cols i) (hc j) (hc i) (b j) (a i) W M k else 0) := by
    split_ifs
    · exact dualTerm_summable _ _ _ _ _ _ _ _ hM
    · exact summable_zero
  rw [gram_pairing,Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  simp_rw [Summable.tsum_finsetSum (fun j _ => hs _ j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : IsCoprime (cols i) (cols j)
  · simp only [ite_eq_left h]
    have he := pair_poisson (cols j) (cols i) (hc j) (hc i) (hf j) (hf i) h.symm W M hM
    have hr : (∑' z : O, (star (row (cols i) z)*row (cols j) z)*W (‖eisEmbedding z‖^2/M)) =
        ∑' z : O, (idealRowHom z (cols j)*star (idealRowHom z (cols i)))*W (‖eisEmbedding z‖^2/M) := by
      apply tsum_congr
      intro z
      simp only [row,mul_comm]
    rw [hr,he]
    simp only [dualTerm,tsum_mul_left]
    ring
  · simp only [ite_eq_right h,tsum_zero,mul_zero]

open EisensteinSchwartzPoisson FourierBridge SieveWindow SieveBilinear SieveUncoupling SieveOperator

def leftTwist {U R : Type*} (a : U × R → ℂ) (x : R → ℝ) (t : ℝ) : U × R → ℂ :=
  fun p => star (logPhase t (-x p.2))*a p

def rightTwist {V T : Type*} (b : V × T → ℂ) (y : T → ℝ) (t : ℝ) : V × T → ℂ :=
  fun p => logPhase t (-y p.2)*b p

theorem leftTwist_norm {U R : Type*} (a : U × R → ℂ) (x : R → ℝ) (t : ℝ) (p : U × R) :
    ‖leftTwist a x t p‖ = ‖a p‖ := by
  simp only [leftTwist,norm_mul,norm_star,logPhase_norm,one_mul]

theorem rightTwist_norm {V T : Type*} (b : V × T → ℂ) (y : T → ℝ) (t : ℝ) (p : V × T) :
    ‖rightTwist b y t p‖ = ‖b p‖ := by
  simp only [rightTwist,norm_mul,logPhase_norm,one_mul]

theorem phased_cross_norm {U V : Type*} (u : U) (v : V)
    (Ui Vi K : Id) (Rs Ts : Finset Id) (r₀ t₀ : EisensteinEPrimaryPhase.Coord)
    (hU : Supported Ui) (hV : Supported Vi)
    (hR : ∀ R ∈ Rs, Supported R ∧ ray R = r₀)
    (hT : ∀ T ∈ Ts, Supported T ∧ ray T = t₀)
    (a : U × ↥Rs → ℂ) (b : V × ↥Ts → ℂ) (x : Rs → ℝ) (y : Ts → ℝ) (z t : ℝ) :
    ‖∑ r : Rs, ∑ s : Ts, (if IsCoprime r.val s.val then
      star (a (u,r))*b (v,s)*crossKernel Ui Vi r.val s.val K else 0)*
        separatedPhase (x r) (y s) z t‖ ≤
      ‖∑ r : Rs, ∑ s : Ts, if IsCoprime r.val s.val then
        star (rowValue (Vi*K) r.val * leftTwist a x t (u,r))*
          (rowValue (Ui*K) s.val * rightTwist b y t (v,s)) else 0‖ := by
  have he : (∑ r : Rs, ∑ s : Ts, (if IsCoprime r.val s.val then
      star (a (u,r))*b (v,s)*crossKernel Ui Vi r.val s.val K else 0)*
        separatedPhase (x r) (y s) z t) =
      logPhase t z * (∑ r : Rs, ∑ s : Ts, if IsCoprime r.val s.val then
        star (leftTwist a x t (u,r))*rightTwist b y t (v,s)*
          crossKernel Ui Vi r.val s.val K else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    by_cases hc : IsCoprime r.val s.val
    · simp only [ite_eq_left hc,separatedPhase,leftTwist,rightTwist,star_mul,star_star]
      ring
    · simp only [ite_eq_right hc,zero_mul,mul_zero]
  rw [he,norm_mul,logPhase_norm,one_mul]
  exact cross_coprime_norm Ui Vi K Rs Ts r₀ t₀ hU hV hR hT
    (fun r => leftTwist a x t (u,r)) (fun s => rightTwist b y t (v,s))

/-- Quantitative bound for a whole logarithmic box of the actual cross
kernel. Both constants are chosen before any lengths, ranges or vectors.
The Fourier weight is retained and supplies arbitrary decay in its scale. -/
theorem coherent_weighted_bound (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (Us Vs Ks Rs Ts : Finset Id) (L₁ L₂ N₁ N₂ : ℝ),
      0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ N₁ → 0 ≤ N₂ →
      (∀ U ∈ Us, Supported U) → (∀ V ∈ Vs, Supported V) →
      (∀ V ∈ Vs, ∀ K ∈ Ks, Supported (V*K) ∧ (Ideal.absNorm (V*K) : ℝ) ≤ L₁) →
      (∀ U ∈ Us, ∀ K ∈ Ks, Supported (U*K) ∧ (Ideal.absNorm (U*K) : ℝ) ≤ L₂) →
      (∀ R ∈ Rs, Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ N₁) →
      (∀ T ∈ Ts, Supported T ∧ PowerFree 6 T ∧ (Ideal.absNorm T : ℝ) ≤ N₂) →
      ∀ r₀ t₀ : EisensteinEPrimaryPhase.Coord,
      (∀ R ∈ Rs, ray R = r₀) → (∀ T ∈ Ts, ray T = t₀) →
      ∀ (a : ↥Us × ↥Rs → ℂ) (b : ↥Vs × ↥Ts → ℂ)
        (x : Rs → ℝ) (y : Ts → ℝ) (z : Ks → ℝ),
      (∀ r, |x r| ≤ Real.log 2) → (∀ s, |y s| ≤ Real.log 2) →
      (∀ k, |z k| ≤ Real.log 2) → ∀ H : ℝ, 0 < H →
      (∑ u : Us, ∑ v : Vs, ∑ k : Ks, ‖∑ r : Rs, ∑ s : Ts,
        (if IsCoprime r.val s.val then
          star (a (u,r))*b (v,s)*crossKernel u.val v.val r.val s.val k.val else 0)*
          paperRadialFourier W (H*Real.exp (z k-x r-y s))‖)^2 ≤
        (D/(1+H)^m)^2 *
        ((C*L₁^ε*SieveRanges.lambda L₁ N₁ *
          (IdealCoprimeSieveOperator.supportConstant ε hε*N₁^ε) * ∑ p, ‖a p‖^2) *
        (C*L₂^ε*SieveRanges.lambda L₂ N₂ *
          (IdealCoprimeSieveOperator.supportConstant ε hε*N₂^ε) * ∑ p, ‖b p‖^2)) := by
  obtain ⟨C,hC,hf⟩ := coherent_frequency_bound ε hε
  obtain ⟨D,hD,hw⟩ := separated_groups_bound W m
  refine ⟨C,D,hC,hD,?_⟩
  intro Us Vs Ks Rs Ts L₁ L₂ N₁ N₂ hL₁ hL₂ hN₁ hN₂ hU hV hVK hUK hR hT
    r₀ t₀ hr ht a b x y z hx hy hz H hH
  let Q : ℝ :=
    (C*L₁^ε*SieveRanges.lambda L₁ N₁ *
      (IdealCoprimeSieveOperator.supportConstant ε hε*N₁^ε) * ∑ p, ‖a p‖^2) *
    (C*L₂^ε*SieveRanges.lambda L₂ N₂ *
      (IdealCoprimeSieveOperator.supportConstant ε hε*N₂^ε) * ∑ p, ‖b p‖^2)
  have hQ : 0 ≤ Q := by
    have hc := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    have hl := SieveRanges.lambda_nonneg L₁ N₁
    have hr' := SieveRanges.lambda_nonneg L₂ N₂
    dsimp only [Q]
    positivity
  let c (p : ↥Us × ↥Vs × ↥Ks) (q : ↥Rs × ↥Ts) : ℂ :=
    if IsCoprime q.1.val q.2.val then
      star (a (p.1,q.1))*b (p.2.1,q.2)*
        crossKernel p.1.val p.2.1.val q.1.val q.2.val p.2.2.val else 0
  have hphase (t : ℝ) :
      (∑ p : ↥Us × ↥Vs × ↥Ks, ‖∑ q : ↥Rs × ↥Ts,
        c p q*separatedPhase (x q.1) (y q.2) (z p.2.2) t‖) ≤ Real.sqrt Q := by
    have hb := hf Us Vs Ks Rs Ts L₁ L₂ N₁ N₂ hL₁ hL₂ hN₁ hN₂ hVK hUK hR hT
      (leftTwist a x t) (rightTwist b y t)
    simp only [leftTwist_norm,rightTwist_norm] at hb
    have he := (Real.le_sqrt (by positivity) hQ).mpr hb
    apply le_trans _ he
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro k _
    exact phased_cross_norm u v u.val v.val k.val Rs Ts r₀ t₀
      (hU _ u.property) (hV _ v.property)
      (fun R h => ⟨(hR R h).1,hr R h⟩) (fun T h => ⟨(hT T h).1,ht T h⟩) a b x y (z k) t
  have hw' := hw H hH c (fun _ q => x q.1) (fun _ q => y q.2) (fun p _ => z p.2.2)
    (fun _ q => hx q.1) (fun _ q => hy q.2) (fun p _ => hz p.2.2)
    (Real.sqrt Q) (Real.sqrt_nonneg _) hphase
  have hs := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hw' 2
  rw [mul_pow,Real.sq_sqrt hQ] at hs
  simpa only [c,Q,Fintype.sum_prod_type] using hs

end
end Candidate.SilPrior.FourthPower.SievePoissonBound
