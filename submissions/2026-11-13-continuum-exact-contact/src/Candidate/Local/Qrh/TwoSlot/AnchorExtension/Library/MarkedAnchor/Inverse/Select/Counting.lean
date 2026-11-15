/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.Separate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.InverseContour
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Mask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

/-!
# Inverse.Select.Counting — the counting inputs of the selection (diagonal lemmas)

For a family of pairwise distinct prime elements `p i` (maximal `span {p i}`):
* `span_prod_injective`: `U ↦ span (∏_U p)` is injective (unique factorization);
* `powerset_norm_count`: `#{U ⊆ pool : N U ≤ Y} ≤ 128 Y` (ideal count);
* `card_le_idealDivisors`: `#U ≤ #divisors (∏_U p)`;
* `primeMarkInj_norm_le`: `|markInj U| ≤ #U ^ #slots` for bounded coefficients;
* `tupleImage_norm`: one prime per selected slot (injective tuple), `N(img d) = ∏ N(d_i)`;
* `tuple_fiber_card_le`: the multiplicity of `(d, k) ↦ k P_d⁴` is at most `#R^#R #divisors (k')`;
* `eis_norm_sq_mul`, `eis_norm_sq_pow` (so `‖k P⁴‖² = ‖k‖² N(P)⁴`); ball facts; monotonicity of
  the energy in the rows.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

theorem eis_norm_sq_mul (x y : O) :
    ‖ConcreteTraceCRT.eisEmbedding (x * y)‖^2 =
      ‖ConcreteTraceCRT.eisEmbedding x‖^2 * ‖ConcreteTraceCRT.eisEmbedding y‖^2 := by
  rw [map_mul, norm_mul, mul_pow]

theorem eis_norm_sq_pow (x : O) (n : ℕ) :
    ‖ConcreteTraceCRT.eisEmbedding (x ^ n)‖^2 = (‖ConcreteTraceCRT.eisEmbedding x‖^2)^n := by
  rw [map_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm]

/-- A nonzero element has `‖eis k‖² ≥ 1`. -/
theorem one_le_eis_norm_sq (k : O) (hk : k ≠ 0) : 1 ≤ ‖ConcreteTraceCRT.eisEmbedding k‖^2 := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have h : Ideal.absNorm (Ideal.span {k}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hk
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem ball_empty_of_neg (Z M : ℝ) (hZ : 1 < Z) (hM : M < 0) :
    nonzeroChildFrequencyBall 1 (Z^M) = ∅ := by
  ext k
  simp only [Finset.notMem_empty, iff_false]
  intro hk
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero, one_mul] at hk
  have hk0 : k ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hk; norm_num at hk
  have h1 := one_le_eis_norm_sq k hk0
  have h2 : Z^M < 1 := Real.rpow_lt_one_of_one_lt_of_neg hZ hM
  linarith [hk.2]

theorem ball_mono (R R' : ℝ) (h : R ≤ R') :
    nonzeroChildFrequencyBall 1 R ⊆ nonzeroChildFrequencyBall 1 R' := by
  intro k hk
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero] at hk ⊢
  exact ⟨hk.1, hk.2.trans h⟩

section Energy
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- The energy is monotone in the row set. -/
theorem energy_rows_mono (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal O)) (ks ks' : Finset O)
    (hks : ks ⊆ ks') (Dw : Ideal O → ℝ) (hDw : ∀ f ∈ labels, 0 ≤ Dw f) (Wf : ℝ → ℂ)
    (X Z F : ℝ) :
    columnEnergyInj p hp hcop hg pool Ψ m slots lists a
        labels ks Dw Wf X Z F ≤
      columnEnergyInj p hp hcop hg pool Ψ m slots lists a
        labels ks' Dw Wf X Z F := by
  unfold columnEnergyInj
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul_of_nonneg_left _ (hDw f hf)
  exact Finset.sum_le_sum_of_subset_of_nonneg hks (fun _ _ _ => by positivity)

/-- The energy vanishes when every row vanishes. -/
theorem energy_eq_zero (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal O)) (ks : Finset O)
    (Dw : Ideal O → ℝ) (Wf : ℝ → ℂ) (X Z F : ℝ)
    (h : ∀ f k, canonRowInj p hp hcop hg pool Ψ m f k slots lists a Wf X = 0) :
    columnEnergyInj p hp hcop hg pool Ψ m slots lists a
        labels ks Dw Wf X Z F = 0 := by
  unfold columnEnergyInj
  simp [h]

/-- The energy at normalization `F` against the energy at normalization `F'`. -/
theorem energy_renormalize (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal O)) (ks : Finset O)
    (Dw : Ideal O → ℝ) (Wf : ℝ → ℂ) (X Z F F' : ℝ) (hZ : 0 < Z) :
    columnEnergyInj p hp hcop hg pool Ψ m slots lists a
        labels ks Dw Wf X Z F =
      Z^(F'-F) * columnEnergyInj p hp hcop hg pool Ψ m slots
        lists a labels ks Dw Wf X Z F' := by
  have hsq : ∀ (G : ℝ) (x : ℂ), ‖((Z^(-G/2) : ℝ) : ℂ) * x‖^2 = Z^(-G) * ‖x‖^2 := by
    intro G x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hZ _), mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul hZ.le]
    congr 2
    push_cast
    ring
  have hsplit : Z^(-F) = Z^(F'-F) * Z^(-F') := by
    rw [← Real.rpow_add hZ]; ring_nf
  unfold columnEnergyInj
  simp only [hsq, hsplit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Energy

section Primes
variable {ι : Type} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hp in
theorem prime_of_maximal (j : ι) : Prime (p j) :=
  (Ideal.span_singleton_prime (hp j)).mp (Ideal.IsMaximal.isPrime inferInstance)

include hp hinj in
theorem span_prod_subset (U U' : Finset ι)
    (h : Ideal.span {∏ i ∈ U, p i} = Ideal.span {∏ i ∈ U', p i}) : U ⊆ U' := by
  intro j hj
  have hdvd : p j ∣ ∏ i ∈ U', p i := by
    have hmem : ∏ i ∈ U', p i ∈ Ideal.span {∏ i ∈ U, p i} := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hmem
    exact (Finset.dvd_prod_of_mem p hj).trans hmem
  obtain ⟨i, hi, hji⟩ := ((prime_of_maximal p hp j).dvd_finset_prod_iff p).mp hdvd
  have hle : Ideal.span {p i} ≤ Ideal.span {p j} := Ideal.span_singleton_le_span_singleton.mpr hji
  have heq : Ideal.span {p i} = Ideal.span {p j} :=
    Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsMaximal.ne_top inferInstance) hle
  have : i = j := hinj heq
  rw [← this]; exact hi

include hp hinj in
theorem span_prod_injective : Function.Injective (fun U : Finset ι => Ideal.span {∏ i ∈ U, p i}) := by
  intro U U' h
  exact Finset.Subset.antisymm (span_prod_subset p hp hinj U U' h)
    (span_prod_subset p hp hinj U' U h.symm)

theorem primeProductNorm_eq_absNorm (U : Finset ι) :
    FirstPassCubeLabels.primeProductNorm p U =
      (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) :=
  ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _

include hp in
theorem span_prod_ne_bot (U : Finset ι) : Ideal.span {∏ i ∈ U, p i} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)

include hp hinj in
/-- `#{U ⊆ pool : N U ≤ Y} ≤ 128 Y`. -/
theorem powerset_norm_count (pool : Finset ι) (Y : ℝ) (hY : 1 ≤ Y) :
    ((pool.powerset.filter (fun U => FirstPassCubeLabels.primeProductNorm p U ≤ Y)).card : ℝ)
      ≤ 128 * Y := by
  set S := pool.powerset.filter (fun U => FirstPassCubeLabels.primeProductNorm p U ≤ Y)
  have hcard : (S.image (fun U => Ideal.span {∏ i ∈ U, p i})).card = S.card :=
    Finset.card_image_of_injective S (span_prod_injective p hp hinj)
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real _ _ hY
  · intro I hI
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hI
    exact span_prod_ne_bot p hp U
  · intro I hI
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hI
    rw [← primeProductNorm_eq_absNorm]
    exact (Finset.mem_filter.mp hU).2

include hp hinj in
/-- `#U ≤ #divisors(∏_U p)`. -/
theorem card_le_idealDivisors (U : Finset ι) :
    (U.card : ℝ) ≤ (IdealMobiusDivisorSum.idealDivisors (Ideal.span {∏ i ∈ U, p i})).card := by
  have h1 : U.card < 2^U.card := Nat.lt_two_pow_self
  have h2 : (U.powerset.image (fun V => Ideal.span {∏ i ∈ V, p i})).card = 2^U.card := by
    rw [Finset.card_image_of_injective _ (span_prod_injective p hp hinj), Finset.card_powerset]
  have h3 : U.powerset.image (fun V => Ideal.span {∏ i ∈ V, p i}) ⊆
      IdealMobiusDivisorSum.idealDivisors (Ideal.span {∏ i ∈ U, p i}) := by
    intro I hI
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hI
    rw [IdealMobiusDivisorSum.mem_idealDivisors (span_prod_ne_bot p hp U),
      Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact Finset.prod_dvd_prod_of_subset _ _ p (Finset.mem_powerset.mp hV)
  have h4 := Finset.card_le_card h3
  rw [h2] at h4
  exact_mod_cast h1.le.trans h4

end Primes

/-- `|markInj U| ≤ #U ^ #slots` for coefficients bounded by `1` on the lists. -/
theorem primeMarkInj_norm_le {ι σ : Type} [DecidableEq ι] (S : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (ha : ∀ i ∈ S, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) (U : Finset ι) :
    ‖primeMarkInj S lists a U‖ ≤ (U.card : ℝ)^S.card :=
  markInj_norm_le lists a S ha U

section Tuples
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

/-- `N(img d) = ∏_i N(d_i)` for an injective tuple. -/
theorem tupleImage_norm (p : ι → O) (R : Finset σ) (lists : σ → Finset ι)
    (d : ∀ i ∈ R, ι) (hd : d ∈ injPi R lists) :
    FirstPassCubeLabels.primeProductNorm p (tupleImage R d) =
      ∏ i ∈ R.attach, FirstPassCubeLabels.primeProductNorm p {d i.1 i.2} := by
  have hprod : ∀ S : Finset ι, FirstPassCubeLabels.primeProductNorm p S =
      ∏ j ∈ S, ‖ConcreteTraceCRT.eisEmbedding (p j)‖^2 := by
    intro S
    unfold FirstPassCubeLabels.primeProductNorm
    rw [map_prod, norm_prod, Finset.prod_pow]
  rw [hprod, tupleImage, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _
    rw [hprod, Finset.prod_singleton]
  · intro i _ j _ hij
    exact Subtype.ext ((mem_injPi.mp hd).2 i.1 i.2 j.1 j.2 hij)

/-- `n ≤ K → n^n ≤ K^K`. -/
theorem pow_self_le_pow_self {n K : ℕ} (h : n ≤ K) : n^n ≤ K^K := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · have : n = 0 := by omega
    rw [this, hK]
  · exact (Nat.pow_le_pow_left h n).trans (Nat.pow_le_pow_right hK h)

/-- The multiplicity of `(d, k) ↦ k (∏_{img d} p)⁴` on injective tuples is at most
`#R^#R · #divisors (k')` (a set of `#R` primes is the image of at most `#R^#R` tuples). -/
theorem tuple_fiber_card_le (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (R : Finset σ) (lists : σ → Finset ι) (ks : Finset O) (k' : O) (hk' : k' ≠ 0) :
    ((injPi R lists ×ˢ ks).filter
      (fun x => x.2 * (∏ i ∈ tupleImage R x.1, p i)^4 = k')).card ≤
      R.card^R.card * (IdealMobiusDivisorSum.idealDivisors (Ideal.span {k'})).card := by
  set F := (injPi R lists ×ˢ ks).filter
    (fun x => x.2 * (∏ i ∈ tupleImage R x.1, p i)^4 = k') with hFdef
  have hk'span : Ideal.span {k'} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hk'
  have hmaps : ∀ x ∈ F, Ideal.span {∏ i ∈ tupleImage R x.1, p i} ∈
      IdealMobiusDivisorSum.idealDivisors (Ideal.span {k'}) := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    rw [IdealMobiusDivisorSum.mem_idealDivisors hk'span,
      Ideal.span_singleton_dvd_span_singleton_iff_dvd, ← hx']
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by norm_num)) _
  refine Finset.card_le_mul_card_image_of_maps_to hmaps _ ?_
  intro I _
  by_cases hne : (F.filter (fun x => Ideal.span {∏ i ∈ tupleImage R x.1, p i} = I)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨x0, hx0⟩ := hne
  have hx0F := (Finset.mem_filter.mp hx0).1
  have hx0d : x0.1 ∈ injPi R lists :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hx0F).1).1
  set S := tupleImage R x0.1 with hS
  -- every element of the fiber has image `S`
  have himgS : ∀ x ∈ F.filter (fun x => Ideal.span {∏ i ∈ tupleImage R x.1, p i} = I),
      tupleImage R x.1 = S := by
    intro x hx
    have h1 := (Finset.mem_filter.mp hx).2
    have h0 := (Finset.mem_filter.mp hx0).2
    exact span_prod_injective p hp hinj (h1.trans h0.symm)
  calc (F.filter (fun x => Ideal.span {∏ i ∈ tupleImage R x.1, p i} = I)).card
      ≤ (R.pi (fun _ => S)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro x hx
          have hxS := himgS x hx
          simp only [Finset.mem_coe] at hx ⊢
          rw [Finset.mem_pi]
          intro i hi
          rw [← hxS]
          exact mem_tupleImage.mpr ⟨i, hi, rfl⟩
        · intro x hx y hy hxy
          have hxF := (Finset.mem_filter.mp hx).1
          have hyF := (Finset.mem_filter.mp hy).1
          have hx' := (Finset.mem_filter.mp hxF).2
          have hy' := (Finset.mem_filter.mp hyF).2
          have hd : x.1 = y.1 := hxy
          have hP : (∏ i ∈ tupleImage R x.1, p i)^4 ≠ 0 :=
            pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
          have hk : x.2 = y.2 := by
            have h2 := hx'.trans hy'.symm
            rw [hd] at h2
            exact mul_right_cancel₀ (by rw [← hd]; exact hP) h2
          exact Prod.ext hd hk
    _ = S.card^R.card := by rw [Finset.card_pi, Finset.prod_const]
    _ = R.card^R.card := by rw [hS, tupleImage_card hx0d]

end Tuples

end
end Qrh.MarkedAnchor.Inverse
