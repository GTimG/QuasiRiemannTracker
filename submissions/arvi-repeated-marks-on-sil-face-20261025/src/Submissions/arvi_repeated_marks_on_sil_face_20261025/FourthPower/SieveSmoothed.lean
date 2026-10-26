/- Copyright (c) 2026 Sil. Apache-2.0.
Actual compact smoothing and quantitative GCD descent for sextic columns.
Generic compact majorants and lattice reindexing are reused from the baseline;
the character-dependent identities are proved for the present sextic rows. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveGcd
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveInitial
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveRanges
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.QuotientColumns

set_option autoImplicit false
namespace Candidate.FourthPower.SieveSmoothed
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CanonicalQuadraticSieve IdealMobiusDivisorSum
open SexticSieve SieveGcd
open CubicSieve (majorant_radial_summable dividedRows dividedMajorant_tsum finite_sum_restrict)
open SecondPassArithmetic (rowMajorant rowMajorantBall rowMajorant_tsum_eq_sum
  finite_row_energy_le_rowMajorant)
local notation "O" => ActualEisensteinCubic.O

def smoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*∑' z : O, (star (row (cols j) z)*row (cols k) z)*
      W (‖eisEmbedding z‖^2/M) else 0

theorem majorant_coprime_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖^2/M)*
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (row (cols j) z*a j)*(row (cols k) z*a k) else 0) =
      smoothedCoprime cols a rowMajorant M := by
  have hs (j k : n) := majorant_radial_summable
    (fun z => if IsCoprime (cols j) (cols k) then
      star (row (cols j) z*a j)*(row (cols k) z*a k) else 0) M hM
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => hs j k))]
  unfold smoothedCoprime
  apply Finset.sum_congr rfl
  intro j _
  rw [Summable.tsum_finsetSum (fun k _ => hs j k)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [star_mul]
    ring
  · simp only [ite_eq_right hcop,mul_zero,tsum_zero]

theorem compact_gcd_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : Supported D) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2/M)*
      ∑ j, ∑ k, gcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D, (UniqueFactorizationMonoid.moebius E : ℂ)*
        smoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M/(Ideal.absNorm E : ℝ)) := by
  rw [gcd_mobius_descent D hD cols a]
  apply Finset.sum_congr rfl
  intro E hE
  have hE0 : E ≠ 0 := by
    intro he
    have hh := (mem_idealDivisors hD.1).mp hE
    rw [he,zero_dvd_iff] at hh
    exact hD.1 hh
  have hgen := idealGenerator_ne_zero E hE0
  congr 1
  rw [dividedMajorant_tsum _ _ hgen M hM,span_idealGenerator]
  apply majorant_coprime_tsum
  exact div_pos hM (CenteredExceptionalCount.norm_pos hE0)

theorem gcdPool_supported {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Supported (cols j))
    (D : Ideal O) (hD : D ∈ gcdPool cols) : Supported D := by
  obtain ⟨⟨j,k⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact SixthDecomposition.supported_dvd (hc j) (gcd_dvd_left _ _)

theorem finite_energy_le_compact_descendants {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Supported (cols j)) (a : n → ℂ)
    (R : Finset O) (M : ℝ) (hM : 0 < M)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) :
    (∑ z ∈ R, ‖∑ j, row (cols j) z*a j‖^2) ≤
      ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖smoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M/(Ideal.absNorm E : ℝ))‖ := by
  have hs := finite_row_energy_le_rowMajorant (fun z => ∑ j, row (cols j) z*a j) R M hM hR
  apply hs.trans
  apply (Complex.re_le_norm _).trans
  rw [rowMajorant_tsum_eq_sum _ M hM,weighted_energy_eq_gcd_blocks (rowMajorantBall M) _ cols a]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [compact_gcd_descent D (gcdPool_supported cols hc D hD) cols a M hM]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (QuadraticInitialBound.norm_ideal_moebius_le_one E)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- The quantitative GCD reduction for the original finite energy.
The explicit residual bound is an intermediate input supplied by Poisson;
it is not asserted or registered as an unconditional analytic theorem. -/
theorem quantitative_gcd_descent (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type*} [Fintype n] (cols : n → Ideal O),
      (∀ j, Supported (cols j)) → ∀ (B : ℝ), 1 ≤ B →
      (∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ B) →
      ∀ (a : n → ℂ) (R : Finset O) (M : ℝ), 0 < M →
      (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
      ∀ H : ℝ, 0 ≤ H →
      (∀ D ∈ gcdPool cols, ∀ E ∈ idealDivisors D,
        ‖smoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M/(Ideal.absNorm E : ℝ))‖ ≤
            H*∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) →
      (∑ z ∈ R, ‖∑ j, row (cols j) z*a j‖^2) ≤ C*B^ε*H*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hm⟩ := descended_mass ε hε
  refine ⟨C,hC,?_⟩
  intro n _ cols hc B hB hN a R M hM hR H hH hbound
  calc
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖smoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant (M/(Ideal.absNorm E : ℝ))‖ :=
      finite_energy_le_compact_descendants cols hc a R M hM hR
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        H*∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 :=
      Finset.sum_le_sum (fun D hD => Finset.sum_le_sum (fun E hE => hbound D hD E hE))
    _ = H*(∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by simp only [Finset.mul_sum]
    _ ≤ H*(C*B^ε*∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left (hm _ cols (fun j => (hc j).1) B hB hN a) hH
    _ = _ := by ring

theorem smoothed_poisson {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    smoothedCoprime cols a W M =
      (M : ℂ)*∑' k : O, ∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
        SievePairPoisson.dualTerm (cols i) (cols j) (hc i) (hc j) (a i) (a j) W M k else 0 := by
  rw [← SievePairPoisson.family_poisson cols hc hf a W M hM]
  unfold smoothedCoprime
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : IsCoprime (cols i) (cols j)
  · simp only [ite_eq_left h,ite_eq_left h.symm,row,mul_comm]
  · have hs : ¬ IsCoprime (cols j) (cols i) := fun hc => h hc.symm
    simp only [ite_eq_right h,ite_eq_right hs]

def gramMatrix {n : Type*} [Fintype n] (cols : n → Ideal O)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) : Matrix n n ℂ := fun j k =>
  if IsCoprime (cols j) (cols k) then
    ∑' z : O, (star (row (cols j) z)*row (cols k) z)*W (‖eisEmbedding z‖^2/M) else 0

theorem smoothed_gram {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    smoothedCoprime cols a W M = ∑ j, star (a j)*(∑ k, gramMatrix cols W M j k*a k) := by
  unfold smoothedCoprime
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : IsCoprime (cols j) (cols k) <;> simp only [gramMatrix, h, ite_true,ite_false]
  · ring
  · ring

theorem smoothed_norm_bound {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    ‖smoothedCoprime cols a W M‖ ≤
      ‖FiniteSieveOperator.operator (gramMatrix cols W M)‖*(∑ j, ‖a j‖^2) := by
  let G := gramMatrix cols W M
  have hn : ‖smoothedCoprime cols a W M‖ ≤ ∑ j, ‖a j‖*‖∑ k, G j k*a k‖ := by
    rw [smoothed_gram]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [norm_mul,norm_star,G,le_refl]
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖∑ k, G j k*a k‖))
  have he : (∑ j, ‖∑ k, G j k*a k‖^2) ≤
      ‖FiniteSieveOperator.operator G‖^2*(∑ j, ‖a j‖^2) := by
    simpa only [CubicSieve.squaredNorm,CubicSieve.operator,FiniteSieveOperator.operator] using
      CubicSieve.energy_le_squaredNorm G a
  have hh := hs.trans (mul_le_mul_of_nonneg_left he (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have ha : 0 ≤ ∑ j, ‖a j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp := mul_nonneg (norm_nonneg (FiniteSieveOperator.operator G)) ha
  dsimp only [G] at hh hp
  nlinarith [norm_nonneg (smoothedCoprime cols a W M)]

/-- A concrete norm of the coprime smoothed Gram matrix. No estimate for
this norm is assumed in its definition. -/
def coprimeNorm (M N : ℝ) : ℝ :=
  ‖FiniteSieveOperator.operator
    (gramMatrix (fun I : SieveRanges.freeRange N => I.val) rowMajorant M)‖

theorem coprimeNorm_nonneg (M N : ℝ) : 0 ≤ coprimeNorm M N := norm_nonneg _

theorem smoothed_le_coprimeNorm {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hinj : Function.Injective cols) (hs : ∀ j, Supported (cols j))
    (hf : ∀ j, PowerFree 6 (cols j)) (M N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    ‖smoothedCoprime cols a rowMajorant M‖ ≤ coprimeNorm M N*(∑ j, ‖a j‖^2) := by
  let f : n → SieveRanges.freeRange N := fun j =>
    ⟨cols j,SieveRanges.mem_freeRange.mpr ⟨hs j,hf j,hN j⟩⟩
  have hfi : Function.Injective f := fun i j h =>
    hinj (congrArg (fun I : SieveRanges.freeRange N => I.val) h)
  have hnorm := FiniteSieveRestriction.submatrix_norm_le f hfi f hfi
    (gramMatrix (fun I : SieveRanges.freeRange N => I.val) rowMajorant M)
  exact (smoothed_norm_bound cols a rowMajorant M).trans
    (mul_le_mul_of_nonneg_right hnorm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem quotient_geometry (D I : Ideal O) (hI : Supported I) (hf : PowerFree 6 I)
    (hDI : D ∣ I) (N : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ N) :
    Supported (idealQuotient D I) ∧ PowerFree 6 (idealQuotient D I) ∧
      (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N/(Ideal.absNorm D : ℝ) := by
  have hD := SixthDecomposition.supported_dvd hI hDI
  have hQ : idealQuotient D I ∣ I := ⟨D,by rw [mul_comm,idealQuotient_mul hDI]⟩
  refine ⟨SixthDecomposition.supported_dvd hI hQ,SieveInitial.powerFree_dvd hf hQ,?_⟩
  apply (le_div_iff₀ (CenteredExceptionalCount.norm_pos hD.1)).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ)) (idealQuotient_mul hDI)
  simp only [map_mul,Nat.cast_mul] at he
  simpa only [mul_comm] using he.trans_le hN

theorem smoothed_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    smoothedCoprime cols a W M =
      smoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold smoothedCoprime
  rw [finite_sum_restrict p _ (by intro j hj; simp [ha j hj])]
  apply Finset.sum_congr rfl
  intro j _
  exact finite_sum_restrict p _ (by intro k hk; simp [ha k hk])

theorem descendant_norm {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (hinj : Function.Injective cols) (hs : ∀ j, Supported (cols j))
    (hf : ∀ j, PowerFree 6 (cols j)) (M N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) (d : O) :
    ‖smoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) rowMajorant M‖ ≤
        coprimeNorm M (N/(Ideal.absNorm D : ℝ)) * ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  let q (j : {j // D ∣ cols j}) := totalQuotient D (cols j.val)
  let b (j : {j // D ∣ cols j}) := descendedCoefficient D cols a d j.val
  have hz (j : n) (hj : ¬D ∣ cols j) : descendedCoefficient D cols a d j = 0 := by
    simp only [descendedCoefficient,ite_eq_right hj,mul_zero]
  have hi : Function.Injective q := by
    intro j k he
    apply Subtype.ext
    apply hinj
    exact idealQuotient_injective_on D j.property k.property
      (by simpa only [q,totalQuotient,ite_eq_left j.property,ite_eq_left k.property] using he)
  have hq (j : {j // D ∣ cols j}) : Supported (q j) ∧ PowerFree 6 (q j) ∧
      (Ideal.absNorm (q j) : ℝ) ≤ N/(Ideal.absNorm D : ℝ) := by
    simpa only [q,totalQuotient,ite_eq_left j.property] using
      quotient_geometry D (cols j.val) (hs j.val) (hf j.val) j.property N (hN j.val)
  rw [smoothed_restrict _ _ (fun j => D ∣ cols j) hz]
  have hm : (∑ j : {j // D ∣ cols j}, ‖b j‖^2) = ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
    symm
    exact finite_sum_restrict (fun j => D ∣ cols j) _ (fun j hj => by rw [hz j hj]; simp)
  have he := smoothed_le_coprimeNorm q hi (fun j => (hq j).1) (fun j => (hq j).2.1)
    M (N/(Ideal.absNorm D : ℝ)) (fun j => (hq j).2.2) b
  rwa [hm] at he

end
end Candidate.FourthPower.SieveSmoothed
