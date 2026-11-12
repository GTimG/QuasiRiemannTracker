/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.RowTuple
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.Cauchy
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.ProfileWide
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.CommonMeasure
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

/-!
# Inverse.Select.Separate — one inner row for all tuples, central Cauchy

After the tuple selection (`canonical_row_select_tuple`) the canonical row at `(f, k)` is
`∑_d c_d · sel_d · row(pool \ img d, f, k P_d⁴, slots \ R, W(N_d ·), X)`.

* `row_full_pool`: the inner pool `pool \ img d` may be replaced by `pool` (a column `U'` meeting
  `img d` has `χ_{U'}(k P_d⁴) = 0`).
* `row_eq_integral`: with the wide profile separation (`profile_separation_wide`,
  `r_d = N_d/T ∈ [2^(-Kb), 1]`) the profile `W(N_d ·)` becomes the fixed bump `Φ` at the common
  column scale `X/T` and height `t + s`:
  `row(f,k) = ∫ b(t) · ∑_d c_d sel_d logPhase(t+s)(log r_d) · Y_{t+s}(f, k P_d⁴) dt`,
  `Y_h(f, k') = row(pool, f, k', slots \ R, childLogTest Φ h, X/T)` (independent of `d`).
* `selected_energy_bound`: weighted integral Cauchy (`common_measure_energy`), central Cauchy over
  `d` with mass `∑_d |c_d|²`, and the multiplicity of `(d, k) ↦ k P_d⁴` give
  `E(slots, ks, W, s) ≤ (∫|b|(1+|t|)^deg)² · mass · mult · A · (1+|s|)^(2 deg)` whenever the inner
  energy on the enlarged row set `ks'` is `≤ A (1+|h|)^(2 deg)` at every height `h`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

/-- Finite sums commute with the integral against `b` (termwise integrable). -/
theorem integral_mul_sum {α : Type*} (s : Finset α) (b : ℝ → ℂ) (c : α → ℂ) (g : α → ℝ → ℂ)
    (hint : ∀ i ∈ s, Integrable (fun t => b t * g i t)) :
    Integrable (fun t => b t * ∑ i ∈ s, c i * g i t) ∧
      ∫ t, b t * ∑ i ∈ s, c i * g i t = ∑ i ∈ s, c i * ∫ t, b t * g i t := by
  have hfun : (fun t => b t * ∑ i ∈ s, c i * g i t) = fun t => ∑ i ∈ s, c i * (b t * g i t) := by
    funext t; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfun]
  refine ⟨integrable_finset_sum s (fun i hi => (hint i hi).const_mul (c i)), ?_⟩
  rw [integral_finset_sum s (fun i hi => (hint i hi).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul (c i) _

/-- Fibre count: summing a nonnegative function along `(D, k) ↦ e D k`. -/
theorem sum_fiber_le {α β : Type*} [DecidableEq β] (Ds : Finset α) (ks ks' : Finset β)
    (e : α → β → β) (g : β → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hmap : ∀ D ∈ Ds, ∀ k ∈ ks, e D k ∈ ks') (mult : ℕ)
    (hmult : ∀ k' ∈ ks', ((Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k')).card ≤ mult) :
    ∑ k ∈ ks, ∑ D ∈ Ds, g (e D k) ≤ mult * ∑ k' ∈ ks', g k' := by
  have step2 : ∑ k ∈ ks, ∑ D ∈ Ds, g (e D k) = ∑ x ∈ Ds ×ˢ ks, g (e x.1 x.2) := by
    rw [Finset.sum_product_right]
  have step3 : ∑ x ∈ Ds ×ˢ ks, g (e x.1 x.2) =
      ∑ k' ∈ ks', ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), g (e x.1 x.2) := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro x hx
    exact hmap x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
  have step4 : ∑ k' ∈ ks', ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), g (e x.1 x.2) ≤
      ∑ k' ∈ ks', (mult : ℝ) * g k' := by
    apply Finset.sum_le_sum
    intro k' hk'
    have hconst : ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), g (e x.1 x.2) =
        ∑ x ∈ (Ds ×ˢ ks).filter (fun x => e x.1 x.2 = k'), g k' := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hg k')
    exact_mod_cast hmult k' hk'
  rw [step2, step3, Finset.mul_sum]
  exact step4

section
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
/-- The canonical row as a column sum with the profile pulled out. -/
theorem row_eq_column_sum (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Wf : ℝ → ℂ) (X : ℝ) :
    canonRowInj p hp hcop hg pool Ψ m f k slots lists a Wf X =
      ∑ U ∈ pool.powerset, Wf (FirstPassCubeLabels.primeProductNorm p U / X) *
        SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k
          (primeMarkInj slots lists a) U := by
  unfold canonRowInj SecondPassArithmetic.fixedChildRow
  apply Finset.sum_congr rfl
  intro U _
  have hfun : (fun U => primeMarkInj slots lists a U *
      Wf (FirstPassCubeLabels.primeProductNorm p U / X)) =
      (fun U => Wf (FirstPassCubeLabels.primeProductNorm p U / X) * primeMarkInj slots lists a U) :=
    funext fun U => mul_comm _ _
  rw [hfun]
  exact secondChildColumn_mul p hp hcop hg Ψ m f k _ _ U

omit [DecidableEq σ] in
/-- Full-pool extension: columns meeting `T` vanish at the row `k (∏_T p)⁴`. -/
theorem row_full_pool (pool T : Finset ι) (hT : T ⊆ pool) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (Wf : ℝ → ℂ) (X : ℝ) :
    canonRowInj p hp hcop hg (pool \ T) Ψ m f (k * (∏ i ∈ T, p i)^4) slots lists a
        Wf X =
      canonRowInj p hp hcop hg pool Ψ m f (k * (∏ i ∈ T, p i)^4) slots lists a
        Wf X := by
  unfold canonRowInj SecondPassArithmetic.fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro U hU hU'
  have hex : ∃ i ∈ U, i ∈ T := by
    by_contra hno
    push_neg at hno
    apply hU'
    rw [Finset.mem_powerset] at hU ⊢
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hU hx, hno x hx⟩
  obtain ⟨i, hiU, hiT⟩ := hex
  have hrow : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (k * (∏ i ∈ T, p i)^4) = 0 := by
    have hmem : k * (∏ i ∈ T, p i)^4 ∈ Ideal.span {p i} := by
      rw [Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_left (dvd_pow (Finset.dvd_prod_of_mem p hiT) (by norm_num)) k
    apply FirstPassCubeLabels.row_zero_of_mask_zero
    unfold rowCoprimeMask
    rw [if_pos ⟨i, hiU, hmem⟩]
  unfold SecondPassArithmetic.secondChildColumn
  rw [hrow]
  ring

/-- Separation of one column profile value. -/
theorem column_profile_sep (W Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ)) (Kb : ℕ)
    (hsep : ∀ r x h : ℝ, 1 ≤ 2^Kb * r → r ≤ 1 → 0 < x →
      W (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t)
    (Nd T X NU s : ℝ) (hT : 0 < T) (hX : 0 < X) (hNU : 0 < NU)
    (hr1 : 1 ≤ 2^Kb * (Nd / T)) (hr2 : Nd / T ≤ 1) :
    childLogTest W s (Nd * (NU / X)) =
      ∫ t : ℝ, b t * (FourierBridge.logPhase (t + s) (Real.log (Nd / T)) *
        childLogTest Φ (t + s) (NU / (X / T))) := by
  have key := hsep (Nd / T) (NU / (X / T)) s hr1 hr2 (by positivity)
  have hx : Nd / T * (NU / (X / T)) = Nd * (NU / X) := by field_simp
  rw [hx] at key
  rw [childLogTest, key]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem phase_profile_integrable (Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ)) (α s x : ℝ) :
    Integrable (fun t : ℝ => b t * (FourierBridge.logPhase (t + s) α *
      childLogTest Φ (t + s) x)) volume := by
  apply schwartz_mul_bounded_integrable b _ _ ‖Φ x‖
  · intro t
    rw [norm_mul, childLogTest, norm_mul, FourierBridge.logPhase_norm,
      FourierBridge.logPhase_norm]
    simp
  · unfold childLogTest
    have h1 : Continuous (fun t : ℝ => FourierBridge.logPhase (t + s) α) :=
      (FourierBridge.logPhase_continuous_left α).comp (continuous_id.add continuous_const)
    have h2 : Continuous (fun t : ℝ => FourierBridge.logPhase (t + s) (Real.log x)) :=
      (FourierBridge.logPhase_continuous_left (Real.log x)).comp
        (continuous_id.add continuous_const)
    exact h1.mul (continuous_const.mul h2)

/-- The common inner row and the separated integrand of one canonical row. -/
def sepIntegrand (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (ss R : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (s T X t : ℝ) : ℂ :=
  ∑ d ∈ injPi R lists, (∏ i ∈ R.attach, a i.1 (d i.1 i.2)) *
    (selectedCoefficient p hp hcop hg Ψ m f k (∅ : Finset σ) lists a (tupleImage R d) *
      (FourierBridge.logPhase (t + s)
          (Real.log (FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T)) *
        canonRowInj p hp hcop hg pool Ψ m f (k * (∏ i ∈ tupleImage R d, p i)^4)
          (ss \ R) lists a (childLogTest Φ (t + s)) (X / T)))

/-- One tuple term: integrability and the separated identity. -/
theorem tuple_term_sep (pool : Finset ι) (Ψ : O →* ℂ) (m f k' : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ)) (Kb : ℕ)
    (hsep : ∀ r x h : ℝ, 1 ≤ 2^Kb * r → r ≤ 1 → 0 < x →
      W (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t)
    (Nd T X s : ℝ) (hT : 0 < T) (hX : 0 < X) (hr1 : 1 ≤ 2^Kb * (Nd / T)) (hr2 : Nd / T ≤ 1) :
    Integrable (fun t => b t * (FourierBridge.logPhase (t + s) (Real.log (Nd / T)) *
        canonRowInj p hp hcop hg pool Ψ m f k' slots lists a
          (childLogTest Φ (t + s)) (X / T))) ∧
    canonRowInj p hp hcop hg pool Ψ m f k' slots lists a
        (fun x => childLogTest W s (Nd * x)) X =
      ∫ t, b t * (FourierBridge.logPhase (t + s) (Real.log (Nd / T)) *
        canonRowInj p hp hcop hg pool Ψ m f k' slots lists a
          (childLogTest Φ (t + s)) (X / T)) := by
  set Col : Finset ι → ℂ := fun U => SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k'
    (primeMarkInj slots lists a) U with hCol
  have hexp : ∀ t, FourierBridge.logPhase (t + s) (Real.log (Nd / T)) *
      canonRowInj p hp hcop hg pool Ψ m f k' slots lists a
        (childLogTest Φ (t + s)) (X / T) =
      ∑ U ∈ pool.powerset, Col U * (FourierBridge.logPhase (t + s) (Real.log (Nd / T)) *
        childLogTest Φ (t + s) (FirstPassCubeLabels.primeProductNorm p U / (X / T))) := by
    intro t
    rw [row_eq_column_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    ring
  have hint : ∀ U ∈ pool.powerset, Integrable (fun t => b t *
      (FourierBridge.logPhase (t + s) (Real.log (Nd / T)) *
        childLogTest Φ (t + s) (FirstPassCubeLabels.primeProductNorm p U / (X / T)))) :=
    fun U _ => phase_profile_integrable Φ b _ s _
  obtain ⟨hI, hE⟩ := integral_mul_sum pool.powerset b Col _ hint
  simp only [hexp]
  refine ⟨hI, ?_⟩
  rw [hE, row_eq_column_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [mul_comm]
  congr 1
  exact column_profile_sep W Φ b Kb hsep Nd T X _ s hT hX
    (FirstPassCubeLabels.primeProductNorm_pos p hp U) hr1 hr2

/-- The canonical row as ONE integral over the separation height, with a common inner row. -/
theorem row_eq_integral (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (ss R : Finset σ) (hR : R ⊆ ss)
    (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (hpool : ∀ i ∈ R, lists i ⊆ pool)
    (W Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ)) (Kb : ℕ)
    (hsep : ∀ r x h : ℝ, 1 ≤ 2^Kb * r → r ≤ 1 → 0 < x →
      W (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t)
    (T X s : ℝ) (hT : 0 < T) (hX : 0 < X)
    (hNd : ∀ d ∈ injPi R lists,
      1 ≤ 2^Kb * (FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T) ∧
      FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T ≤ 1) :
    Integrable (fun t => b t * sepIntegrand p hp hcop hg pool Ψ m f k ss R lists a Φ s T X t) ∧
    canonRowInj p hp hcop hg pool Ψ m f k ss lists a (childLogTest W s) X =
      ∫ t, b t * sepIntegrand p hp hcop hg pool Ψ m f k ss R lists a Φ s T X t := by
  have himg : ∀ d ∈ injPi R lists, tupleImage R d ⊆ pool := by
    intro d hd x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hpool i.1 i.2 (Finset.mem_pi.mp (injPi_subset _ _ hd) i.1 i.2)
  have hterm := fun d (hd : d ∈ injPi R lists) => tuple_term_sep p hp hcop hg pool Ψ m f
    (k * (∏ i ∈ tupleImage R d, p i)^4) (ss \ R) lists a W Φ b Kb hsep
    (FirstPassCubeLabels.primeProductNorm p (tupleImage R d)) T X s hT hX (hNd d hd).1 (hNd d hd).2
  have hshape : ∀ t, sepIntegrand p hp hcop hg pool Ψ m f k ss R lists a Φ s T X t =
      ∑ d ∈ injPi R lists, ((∏ i ∈ R.attach, a i.1 (d i.1 i.2)) *
        selectedCoefficient p hp hcop hg Ψ m f k (∅ : Finset σ) lists a (tupleImage R d)) *
        (FourierBridge.logPhase (t + s)
          (Real.log (FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T)) *
        canonRowInj p hp hcop hg pool Ψ m f (k * (∏ i ∈ tupleImage R d, p i)^4)
          (ss \ R) lists a (childLogTest Φ (t + s)) (X / T)) := by
    intro t
    unfold sepIntegrand
    apply Finset.sum_congr rfl
    intro d _
    ring
  obtain ⟨hI, hE⟩ := integral_mul_sum (injPi R lists) b _ _ (fun d hd => (hterm d hd).1)
  simp only [hshape]
  refine ⟨hI, ?_⟩
  rw [hE, canonical_row_select_tuple p hp hcop hg hpr pool Ψ m f k ss R hR lists a hpool]
  apply Finset.sum_congr rfl
  intro d hd
  rw [row_full_pool p hp hcop hg pool _ (himg d hd), (hterm d hd).2]
  ring

/-- The pointwise central Cauchy bound for the separated integrand. -/
theorem sepIntegrand_sq_le (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f k : O) (ss R : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (s T X t : ℝ) :
    ‖sepIntegrand p hp hcop hg pool Ψ m f k ss R lists a Φ s T X t‖^2 ≤
      (∑ d ∈ injPi R lists, ‖∏ i ∈ R.attach, a i.1 (d i.1 i.2)‖^2) *
        ∑ d ∈ injPi R lists, ‖canonRowInj p hp hcop hg pool Ψ m f
          (k * (∏ i ∈ tupleImage R d, p i)^4) (ss \ R) lists a (childLogTest Φ (t + s))
          (X / T)‖^2 := by
  unfold sepIntegrand
  refine (norm_sum_mul_sq_le _ _ _).trans ?_
  gcongr with d hd
  have hsel : ‖selectedCoefficient p hp hcop hg Ψ m f k (∅ : Finset σ) lists a
      (tupleImage R d)‖ ≤ 1 := by
    unfold selectedCoefficient
    refine (SecondPassArithmetic.secondChildColumn_norm_le_test p hp hcop hg hc Ψ hΨ m f k
      _ _).trans ?_
    simp
  rw [norm_mul, norm_mul, FourierBridge.logPhase_norm, one_mul]
  have h0 := norm_nonneg (canonRowInj p hp hcop hg pool Ψ m f
    (k * (∏ i ∈ tupleImage R d, p i)^4) (ss \ R) lists a (childLogTest Φ (t + s)) (X / T))
  have h1 := norm_nonneg (selectedCoefficient p hp hcop hg Ψ m f k (∅ : Finset σ) lists a
      (tupleImage R d))
  exact mul_le_of_le_one_left h0 hsel

/-- **The selected energy bound** (separation and central Cauchy). -/
theorem selected_energy_bound (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (ss R : Finset σ)
    (hR : R ⊆ ss) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (hpool : ∀ i ∈ R, lists i ⊆ pool)
    (W Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ)) (Kb : ℕ)
    (hsep : ∀ r x h : ℝ, 1 ≤ 2^Kb * r → r ≤ 1 → 0 < x →
      W (r * x) * FourierBridge.logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b t)
    (T X : ℝ) (hT : 0 < T) (hX : 0 < X)
    (hNd : ∀ d ∈ injPi R lists,
      1 ≤ 2^Kb * (FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T) ∧
      FirstPassCubeLabels.primeProductNorm p (tupleImage R d) / T ≤ 1)
    (labels : Finset (Ideal O)) (Dw : Ideal O → ℝ) (hDw : ∀ f ∈ labels, 0 ≤ Dw f)
    (ks ks' : Finset O)
    (hmap : ∀ d ∈ injPi R lists, ∀ k ∈ ks, k * (∏ i ∈ tupleImage R d, p i)^4 ∈ ks')
    (mult : ℕ)
    (hmult : ∀ k' ∈ ks', ((injPi R lists ×ˢ ks).filter
      (fun x => x.2 * (∏ i ∈ tupleImage R x.1, p i)^4 = k')).card ≤ mult)
    (Z F A : ℝ) (deg : ℕ) (hA0 : 0 ≤ A)
    (hA : ∀ h : ℝ, columnEnergyInj p hp hcop hg pool Ψ m
      (ss \ R) lists a labels ks' Dw (childLogTest Φ h) (X / T) Z F ≤ A * (1 + ‖h‖)^(2*deg))
    (s : ℝ) :
    columnEnergyInj p hp hcop hg pool Ψ m ss lists a labels
        ks Dw (childLogTest W s) X Z F ≤
      (∫ t, ‖b t‖ * (1 + ‖t‖)^deg)^2 *
        ((∑ d ∈ injPi R lists, ‖∏ i ∈ R.attach, a i.1 (d i.1 i.2)‖^2) * mult * A *
          (1 + ‖s‖)^(2*deg)) := by
  set mass : ℝ := ∑ d ∈ injPi R lists, ‖∏ i ∈ R.attach, a i.1 (d i.1 i.2)‖^2 with hmass
  have hmass0 : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => by positivity)
  set cZ : ℂ := ((Z^(-F/2) : ℝ) : ℂ) with hcZ
  set sep : Ideal O → O → ℝ → ℂ := fun f k t =>
    sepIntegrand p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f) k ss R lists a Φ s T X t with hsepdef
  set hw : ℝ → ℝ := fun t => (1 + ‖t‖)^deg with hhw
  have hw0 : ∀ t, 0 < hw t := fun t => by simp only [hhw]; positivity
  let κ := ↥(labels ×ˢ ks)
  let b' : ℝ → ℂ := fun t => b t * ((hw t : ℝ) : ℂ)
  let φ0 : Ideal O × O → ℝ → ℂ := fun x t =>
    ((Real.sqrt (Dw x.1) : ℝ) : ℂ) * cZ * sep x.1 x.2 t / ((hw t : ℝ) : ℂ)
  let φ : κ → ℝ → ℂ := fun x t => φ0 x.1 t
  have hrow := fun (f : Ideal O) (k : O) => row_eq_integral p hp hcop hg hpr pool Ψ m
    (CompletedGauss.primaryGenerator f) k ss R hR lists a hpool W Φ b Kb hsep T X s hT hX hNd
  have hbφ0 : ∀ x : Ideal O × O, ∀ t, b' t * φ0 x t =
      (((Real.sqrt (Dw x.1) : ℝ) : ℂ) * cZ) * (b t * sep x.1 x.2 t) := by
    intro x t
    have hn : ((hw t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hw0 t).ne'
    simp only [b', φ0]
    field_simp
  have hbφ : ∀ x : κ, ∀ t, b' t * φ x t =
      (((Real.sqrt (Dw x.1.1) : ℝ) : ℂ) * cZ) * (b t * sep x.1.1 x.1.2 t) :=
    fun x t => hbφ0 x.1 t
  have hint : ∀ x : κ, Integrable (fun t => b' t * φ x t) := by
    intro x
    simp only [hbφ]
    exact (hrow x.1.1 x.1.2).1.const_mul _
  have hb' : Integrable (fun t => ‖b' t‖) := by
    have h := schwartz_weight_integrable b deg
    refine h.congr ?_
    filter_upwards with t
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, hhw]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |t|)^deg)]
  set E : ℝ := mass * mult * A * (1 + ‖s‖)^(2*deg) with hE
  have hE0 : 0 ≤ E := by positivity
  have hbound : ∀ t, (∑ x : κ, ‖φ x t‖^2) ≤ E := by
    intro t
    have hφn : ∀ x : κ, ‖φ x t‖^2 =
        Dw x.1.1 * ‖cZ‖^2 * ‖sep x.1.1 x.1.2 t‖^2 / (hw t)^2 := by
      intro x
      have hD := hDw x.1.1 (Finset.mem_product.mp x.2).1
      simp only [φ, φ0, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hw0 t), abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hD]
    simp only [hφn]
    rw [Finset.sum_coe_sort (labels ×ˢ ks)
      (fun x => Dw x.1 * ‖cZ‖^2 * ‖sep x.1 x.2 t‖^2 / (hw t)^2), ← Finset.sum_div,
      div_le_iff₀ (by have := hw0 t; positivity), Finset.sum_product]
    -- inner energy at height `t + s`
    set Y : Ideal O → O → ℂ := fun f k' => canonRowInj p hp hcop hg pool Ψ m
      (CompletedGauss.primaryGenerator f) k' (ss \ R) lists a (childLogTest Φ (t + s)) (X / T) with hY
    have hstep : ∀ f ∈ labels, ∑ k ∈ ks, Dw f * ‖cZ‖^2 * ‖sep f k t‖^2 ≤
        mass * mult * (Dw f * ∑ k' ∈ ks', ‖cZ * Y f k'‖^2) := by
      intro f hf
      have hD := hDw f hf
      have hc2 : 0 ≤ Dw f * ‖cZ‖^2 := by positivity
      calc ∑ k ∈ ks, Dw f * ‖cZ‖^2 * ‖sep f k t‖^2
          ≤ ∑ k ∈ ks, Dw f * ‖cZ‖^2 * (mass * ∑ d ∈ injPi R lists,
              ‖Y f (k * (∏ i ∈ tupleImage R d, p i)^4)‖^2) := by
            gcongr with k hk
            exact sepIntegrand_sq_le p hp hcop hg hc pool Ψ hΨ m (CompletedGauss.primaryGenerator f) k ss R
              lists a Φ s T X t
        _ = Dw f * ‖cZ‖^2 * mass * ∑ k ∈ ks, ∑ d ∈ injPi R lists,
              ‖Y f (k * (∏ i ∈ tupleImage R d, p i)^4)‖^2 := by
            rw [Finset.mul_sum ks]
            apply Finset.sum_congr rfl; intro k _; ring
        _ ≤ Dw f * ‖cZ‖^2 * mass * (mult * ∑ k' ∈ ks', ‖Y f k'‖^2) := by
            gcongr
            exact sum_fiber_le (injPi R lists) ks ks'
              (fun d k => k * (∏ i ∈ tupleImage R d, p i)^4) (fun k' => ‖Y f k'‖^2)
              (fun _ => by positivity) hmap mult hmult
        _ = mass * mult * (Dw f * ∑ k' ∈ ks', ‖cZ * Y f k'‖^2) := by
            have hcz : ∀ w : ℂ, ‖cZ * w‖^2 = ‖cZ‖^2 * ‖w‖^2 := fun w => by
              rw [norm_mul, mul_pow]
            simp only [hcz]
            rw [← Finset.mul_sum ks' (fun k' => ‖Y f k'‖^2) (‖cZ‖^2)]
            ring
    have hinner := hA (t + s)
    unfold columnEnergyInj at hinner
    have hts : (1 + ‖t + s‖)^(2*deg) ≤ hw t ^ 2 * (1 + ‖s‖)^(2*deg) := by
      have h1 : 1 + ‖t + s‖ ≤ (1 + ‖t‖) * (1 + ‖s‖) := by
        have := norm_add_le t s
        nlinarith [norm_nonneg t, norm_nonneg s]
      calc (1 + ‖t + s‖)^(2*deg) ≤ ((1 + ‖t‖) * (1 + ‖s‖))^(2*deg) := by
            gcongr
        _ = hw t ^ 2 * (1 + ‖s‖)^(2*deg) := by
            simp only [hhw]; rw [mul_pow, ← pow_mul, mul_comm deg 2]
    calc ∑ f ∈ labels, ∑ k ∈ ks, Dw f * ‖cZ‖^2 * ‖sep f k t‖^2
        ≤ ∑ f ∈ labels, mass * mult * (Dw f * ∑ k' ∈ ks', ‖cZ * Y f k'‖^2) :=
          Finset.sum_le_sum hstep
      _ = mass * mult * ∑ f ∈ labels, Dw f * ∑ k' ∈ ks', ‖cZ * Y f k'‖^2 := by
          rw [Finset.mul_sum]
      _ ≤ mass * mult * (A * (1 + ‖t + s‖)^(2*deg)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ mass * mult * (A * (hw t ^ 2 * (1 + ‖s‖)^(2*deg))) := by
          gcongr
      _ = E * hw t ^ 2 := by simp only [hE]; ring
  have hmain := common_measure_energy volume b' φ E hE0 hb' hint hbound
  have hlhs : columnEnergyInj p hp hcop hg pool Ψ m ss lists
      a labels ks Dw (childLogTest W s) X Z F = ∑ x : κ, ‖∫ t, b' t * φ x t‖^2 := by
    unfold columnEnergyInj
    rw [Finset.sum_coe_sort (labels ×ˢ ks) (fun x => ‖∫ t, b' t * φ0 x t‖^2),
      Finset.sum_product]
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hD := hDw f hf
    simp only [hbφ0]
    rw [integral_const_mul, ← (hrow f k).2]
    have hs : ‖((Real.sqrt (Dw f) : ℝ) : ℂ)‖^2 = Dw f := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hD]
    simp only [norm_mul, mul_pow, hs]
    ring
  rw [hlhs]
  refine hmain.trans (le_of_eq ?_)
  have hb'n : (∫ t, ‖b' t‖) = ∫ t, ‖b t‖ * (1 + ‖t‖)^deg := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [b', norm_mul, Complex.norm_real, Real.norm_eq_abs, hhw]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |t|)^deg)]
  rw [hb'n]
  ring

end

end
end Qrh.MarkedAnchor.Inverse
