/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Uniform
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Loss
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Arith
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.Assembly

/-!
# Inverse.Restore.Main — the slot restoration

**`restoreChildBoundUniform_canonical`**: `RestoreChildBoundUniform canonicalFamily canonicalFamily`.

Given the child source `UniformInverseRectSourceExcess canonicalFamily ρc x` at `ε/4` (mesh
`meshS`), the restoration mesh is `min (meshS·Hlo) 1`. For a parent class
`canonicalSlotsRay W (33/50) rayM G hH`, profiles `Φs`, `bo`, `K`, `q`:
* separation: one bump `Φsep = 1` on `[a', 2^{2K+1} b']` (`Poisson.exists_profile_bump`) and Schwartz
  weights for `Φs j` and `star ∘ Φs j` (`profile_separation_wide` at `2K+1`);
* child profiles `Φ₂ = Φsep·x^{-1/2}` and the unit bump `Φ₀`; uniform child source constants over
  the finite child keys (`Uniform.uniform_child_sources`), `dchild = 2 dU`;
* per datum and orientation: `Oriented.oriented_bound` (negative orientation through
  `Glue.mobiusChildSumInj_negative`), the frozen scale through `Arith.g1_scale`, the restoration
  loss through
  `Loss.restore_loss` with `η = ε/8`, the constant through `Arith.mainConst_le`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.SevenEighths.HeckeInverseAmplification (RowData NonzeroElement)
open OAI.SevenEighths.HeckeDyadic (polynomial)
open OAI.ConcretePrimeRowBridge (primePool)
open OAI.CanonicalQuadraticSieve (poolPrimary)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor IsBaseRayTwist)
open DetectorDictionaryInverseRawInitialGates (deletedBase basePeriod)
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

theorem rpow_ge_of_root (c e Z : ℝ) (hc : 0 ≤ c) (he : 0 < e) (hZ : c^(1/e) ≤ Z) :
    c ≤ Z^e := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hc _) hZ he.le
  rwa [← Real.rpow_mul hc, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one] at h

theorem bounded_of_support (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ)
    (hs : Function.support f ⊆ Set.Icc a b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc a b
  · exact (hM x hx).trans (le_max_left _ _)
  · have : f x = 0 := by
      by_contra h; exact hx (hs h)
    rw [this, norm_zero]; exact le_max_right _ _

theorem childLogTest_norm_le (Φ : ℝ → ℂ) (θ x M : ℝ) (h : ‖Φ x‖ ≤ M) :
    ‖childLogTest Φ θ x‖ ≤ M := by
  unfold childLogTest
  rw [norm_mul, FourierBridge.logPhase_norm, mul_one]; exact h

set_option maxHeartbeats 4000000 in
/-- **The slot restoration.** -/
theorem restoreChildBoundUniform_canonical :
    RestoreChildBoundUniform canonicalFamily canonicalFamily := by
  intro ρc x Hlo hx hHlo hsrc ε hε
  obtain ⟨meshS, hmeshS, hS⟩ := hsrc (ε/4) (by positivity)
  refine ⟨min (meshS * Hlo) 1, lt_min (by positivity) one_pos, ?_⟩
  intro cls hcls J Φs a' b' ha' hab hΦs bo hbo K q hq
  obtain ⟨W, hW, hWs, rayM, hne, G, hH, rfl⟩ := hcls
  -- the separation bump and the Schwartz weights
  have h2K : (1:ℝ) ≤ 2^(2*K+1) := one_le_pow₀ (by norm_num)
  obtain ⟨Φsep, hΦsm, hΦsupp, hΦ1, -, -⟩ :=
    Poisson.exists_profile_bump a' (2^(2*K+1) * b') ha' (by nlinarith)
  have hΦsJ : ∀ j, ContDiff ℝ ∞ (fun x => star (Φs j x)) ∧
      Function.support (fun x => star (Φs j x)) ⊆ Set.Icc a' b' := by
    intro j
    refine ⟨?_, ?_⟩
    · have : (fun x => star (Φs j x)) = fun x => (starRingEnd ℂ) (Φs j x) := rfl
      rw [this]
      exact Complex.conjCLE.contDiff.comp (hΦs j).1
    · intro x hx
      apply (hΦs j).2
      intro h0; apply hx; simp [h0]
  have hsepP : ∀ j, ∃ b : 𝓢(ℝ, ℂ), ∀ r x' h : ℝ, 1 ≤ 2^(2*K+1) * r → r ≤ 1 → 0 < x' →
      Φs j (r * x') * FourierBridge.logPhase h (Real.log (r * x')) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φsep (t + h) x' * b t :=
    fun j => profile_separation_wide (Φs j) (hΦs j).1 a' b' ha' (hΦs j).2 (2*K+1) Φsep hΦ1 hΦsupp
  have hsepN : ∀ j, ∃ b : 𝓢(ℝ, ℂ), ∀ r x' h : ℝ, 1 ≤ 2^(2*K+1) * r → r ≤ 1 → 0 < x' →
      star (Φs j (r * x')) * FourierBridge.logPhase h (Real.log (r * x')) =
        ∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log r) * childLogTest Φsep (t + h) x' * b t :=
    fun j => profile_separation_wide (fun x => star (Φs j x)) (hΦsJ j).1 a' b' ha' (hΦsJ j).2
      (2*K+1) Φsep hΦ1 hΦsupp
  choose bP hbP using hsepP
  choose bN hbN using hsepN
  -- the child profiles
  set bsup : ℝ := 2 * (2^(2*K+1) * b') with hbsup
  have hbsup0 : 0 < bsup := by have := ha'.trans_le hab; positivity
  have hΦsepv : ∀ y, bsup < y → Φsep y = 0 := by
    intro y hy; by_contra h; have := (hΦsupp h).2; linarith
  set Φ₂ : ℝ → ℂ := fun y => Φsep y * ((y : ℂ) ^ (-(1/2 : ℂ))) with hΦ₂
  have hΦ₂sm : ContDiff ℝ ∞ Φ₂ := contDiff_mul_cpow Φsep hΦsm (a'/2) bsup (by positivity) hΦsupp _
  have hΦ₂s : Function.support Φ₂ ⊆ Set.Icc (a'/2) bsup := by
    intro y hy; apply hΦsupp; intro h0; apply hy; simp [hΦ₂, h0]
  obtain ⟨Φ₀, hΦ₀sm, hΦ₀s, hΦ₀1⟩ := exists_unit_bump
  have hΦ₀2 : ∀ y, 2 ≤ y → Φ₀ y = 0 := by
    intro y hy; by_contra h; have := (hΦ₀s h).2; linarith
  obtain ⟨Mw, hMw0, hMw⟩ := bounded_of_support Φ₂ hΦ₂sm.continuous (a'/2) bsup hΦ₂s
  obtain ⟨Cb, hCb0, hCbW⟩ := polynomial_small_bound bsup Mw hbsup0 hMw0
  have hCb : ∀ (θ : ℝ) (χ : Character) (Y : ℝ), 0 < Y → Y ≤ 1 →
      ‖polynomial χ true (childLogTest Φ₂ θ) Y 0 0‖ ≤ Cb := by
    intro θ χ Y hY hY1
    refine hCbW _ (fun y => childLogTest_norm_le Φ₂ θ y Mw (hMw y)) ?_ χ Y hY hY1
    intro y hy; unfold childLogTest; rw [hΦ₂]; simp only [hΦsepv y hy, zero_mul]
  -- uniform child sources
  have hao : 0 < min (a'/2) (1/2) := lt_min (by positivity) (by norm_num)
  obtain ⟨dU, CU, Z₀U, c₀, hCU, hZ₀U, hc₀, hU⟩ := uniform_child_sources hS W hW hWs rayM G hH
    K q hq Φ₂ Φ₀ (min (a'/2) (1/2)) (max bsup 2) hao
    ((min_le_right _ _).trans (by norm_num : (1/2:ℝ) ≤ 2) |>.trans (le_max_right _ _))
    (hΦ₂s.trans (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _))) hΦ₂sm
    (hΦ₀s.trans (Set.Icc_subset_Icc (min_le_right _ _) (by
      have : (3/2:ℝ) ≤ 2 := by norm_num
      exact this.trans (le_max_right _ _)))) hΦ₀sm
  -- the restoration loss
  obtain ⟨CL, hCL, hloss⟩ := restore_loss K (ε/8) (by positivity)
  -- constants
  set dchild : ℕ := dU + dU with hdchild
  set Ib : ℝ := ∑ j, ((∫ τ, ‖bP j τ‖ * (1 + ‖τ‖)^dchild) + ∫ τ, ‖bN j τ‖ * (1 + ‖τ‖)^dchild)
    with hIb
  have hIbP : ∀ j, (∫ τ, ‖bP j τ‖ * (1 + ‖τ‖)^dchild) ≤ Ib := by
    intro j
    have h0 : ∀ j, 0 ≤ (∫ τ, ‖bP j τ‖ * (1 + ‖τ‖)^dchild) + ∫ τ, ‖bN j τ‖ * (1 + ‖τ‖)^dchild :=
      fun j => add_nonneg (integral_nonneg (fun τ => by positivity))
        (integral_nonneg (fun τ => by positivity))
    have := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j)
    have hN0 : 0 ≤ ∫ τ, ‖bN j τ‖ * (1 + ‖τ‖)^dchild := integral_nonneg (fun τ => by positivity)
    linarith
  have hIbN : ∀ j, (∫ τ, ‖bN j τ‖ * (1 + ‖τ‖)^dchild) ≤ Ib := by
    intro j
    have h0 : ∀ j, 0 ≤ (∫ τ, ‖bP j τ‖ * (1 + ‖τ‖)^dchild) + ∫ τ, ‖bN j τ‖ * (1 + ‖τ‖)^dchild :=
      fun j => add_nonneg (integral_nonneg (fun τ => by positivity))
        (integral_nonneg (fun τ => by positivity))
    have := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j)
    have hP0 : 0 ≤ ∫ τ, ‖bP j τ‖ * (1 + ‖τ‖)^dchild := integral_nonneg (fun τ => by positivity)
    linarith
  have hcost : 0 ≤ QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K := by
    unfold QRH.Record1252270103Source.Collision.collisionProjectionCost; positivity
  set Kc : ℝ := (Ib^2 + 1) * (QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
    ((smallConst c₀ K * max 1 Cb)^2 * ((CU + CU) * 64^(2*dchild)))) with hKc
  have hKc0 : 0 < Kc := by
    have h1 := one_le_smallConst c₀ K
    have h2 : (1:ℝ) ≤ max 1 Cb := le_max_left _ _
    have hcost' : 0 < QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K := by
      unfold QRH.Record1252270103Source.Collision.collisionProjectionCost; positivity
    positivity
  set C : ℝ := CL * (2 * bo)^(ε/8) * Kc with hCdef
  have hC0 : 0 < C := by positivity
  set Zp : ℝ := (2 * bsup)^(1/(Hlo * (-ρc.Pmax))) with hZp
  set Z₀ : ℝ := max (max 2 bsup) (max (Z₀U^(1/Hlo)) Zp) with hZ₀def
  refine ⟨dchild, C, Z₀, hC0, lt_of_lt_of_le one_lt_two ((le_max_left _ _).trans
    (le_max_left _ _)), ?_⟩
  intro Z hZ
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans ((le_max_left _ _).trans hZ)
  have hZb : bsup ≤ Z := (le_max_right _ _).trans ((le_max_left _ _).trans hZ)
  have hZU : Z₀U^(1/Hlo) ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZP : Zp ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 < Z := lt_of_lt_of_le one_lt_two hZ2
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  unfold RestoreChildAt
  intro D hD σ _ slots lists H a hK hH1 hHn ha hv hv0 hadm base hbase hbf Ψ hΨ m hm hmZ R hR
    Xmax Hc' hXmax0 hXZ hHlo' hHc2 hPm hSm
  dsimp only
  haveI hmaxI : ∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal :=
    fun i => by
      rw [CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) i]; infer_instance
  intro t ht hGt Js hJs ψ hψ j s Xc hXc hXcm hG1 neg
  -- the datum
  obtain ⟨cls', hcls', data, L, ell, β, J0, tpar, hc, hell0, hellm, hprime, hratio, hβ1, hgateP,
    hq', hslots, hlists, hHdef, haform, htv⟩ := hadm
  subst hcls'
  obtain ⟨θp, v, hvb, hLβ⟩ := hc
  have hL : ∀ i, L i = canonicalPool rayM G.pool (Z^(ell i)) := fun i => (hLβ i).1
  have hβ : ∀ i, β i = rayCoeff rayM G hH W (33/50) data θp (Z^(ell i)) (v i) :=
    fun i => (hLβ i).2
  have hHc'0 : 0 < Hc' := lt_of_lt_of_le hHlo hHlo'
  -- the child twist
  have hψf : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ :=
    childRay_factors hbf hΨ hψ
  have hψn : ∀ y, ‖ψ y‖ ≤ 1 := by
    obtain ⟨χ, rfl⟩ := hψ
    intro y
    rw [MonoidHom.mul_apply, norm_mul]
    have h1 := SecondPassArithmetic.rayMonoid_norm_le_one χ y
    have h2 := IsBaseRayTwist.norm_le hΨ hbase y
    calc ‖SecondPassArithmetic.rayMonoid χ y‖ * ‖Ψ y‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  -- slot sets
  set S := slots \ R with hSdef
  set I := S \ Js with hIdef
  have hJsS : Js ⊆ S := Finset.mem_powerset.mp hJs
  have hIS : I ⊆ S := Finset.sdiff_subset
  have hSs : S ⊆ slots := Finset.sdiff_subset
  have hSK : S.card ≤ K := (Finset.card_le_card hSs).trans hK
  have hIK : I.card ≤ K := (Finset.card_le_card hIS).trans hSK
  have hmesh1 : ∀ i, ell i ≤ 1 := fun i => (hellm i).trans (min_le_right _ _)
  have hZell : ∀ i, Z^(ell i) ≤ Z := fun i => by
    have := Real.rpow_le_rpow_of_exponent_le hZ1.le (hmesh1 i); rwa [Real.rpow_one] at this
  have hZ3 : Z^3 ≤ (D : ℝ) := hD
  have hZD : ∀ i ∈ I, 2 * Z^(ell i) ≤ D := by
    intro i _
    have h1 := hZell i
    have : 2 * Z ≤ Z^3 := by nlinarith
    linarith
  have hmeshS' : ∀ i ∈ I, ell i / Hc' ≤ meshS := by
    intro i _
    rw [div_le_iff₀ hHc'0]
    calc ell i ≤ meshS * Hlo := (hellm i).trans (min_le_left _ _)
      _ ≤ meshS * Hc' := mul_le_mul_of_nonneg_left hHlo' hmeshS.le
  have hHpos : ∀ i ∈ S, 0 < H i := fun i hi => by
    rw [hHdef i]; positivity
  have hHge : ∀ i ∈ S, Z^(ell i) ≤ H i := fun i _ => by
    rw [hHdef i]; have := Real.rpow_pos_of_pos hZ0 (ell i); linarith
  have hprodS : 0 < ∏ i ∈ S, H i := Finset.prod_pos hHpos
  -- slot width
  have hSw : ∑ i ∈ I, ell i / Hc' ≤ ρc.Smax := by
    rw [← Finset.sum_div, div_le_iff₀ hHc'0]
    calc ∑ i ∈ I, ell i ≤ ∑ i ∈ S, ell i :=
          Finset.sum_le_sum_of_subset_of_nonneg hIS (fun i _ _ => hell0 i)
      _ ≤ ρc.Smax * Hc' := slot_width_le S ell H Z _ hZ1 hHge hSm
  -- the child scale
  have hZ'U : Z₀U ≤ Z^Hc' := by
    have h1 : Z₀U ≤ Z^Hlo := rpow_ge_of_root Z₀U Hlo Z (by linarith) hHlo hZU
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le hHlo')
  have hZ'1 : 1 < Z^Hc' := Real.one_lt_rpow hZ1 hHc'0
  have hZ'P : (Z^Hc')^ρc.Pmax = Z^(ρc.Pmax * Hc') := by
    rw [← Real.rpow_mul hZ0.le, mul_comm]
  have hPmax' : 0 ≤ ρc.Pmax ∨ bsup * (Z^Hc')^ρc.Pmax < 1 := by
    by_cases hP : 0 ≤ ρc.Pmax
    · exact Or.inl hP
    · right
      push_neg at hP
      have he : 0 < Hlo * (-ρc.Pmax) := mul_pos hHlo (by linarith)
      have h1 : 2 * bsup ≤ Z^(Hlo * (-ρc.Pmax)) := rpow_ge_of_root _ _ Z (by positivity) he hZP
      have h2 : (Z^Hc')^ρc.Pmax ≤ Z^(Hlo * ρc.Pmax) := by
        rw [hZ'P]
        apply Real.rpow_le_rpow_of_exponent_le hZ1.le
        nlinarith
      have h3 : Z^(Hlo * ρc.Pmax) * Z^(Hlo * (-ρc.Pmax)) = 1 := by
        rw [← Real.rpow_add hZ0]; simp
      have h4 : 0 < Z^(Hlo * ρc.Pmax) := Real.rpow_pos_of_pos hZ0 _
      nlinarith
  -- the frozen scale
  have hXmaxP : Xmax ≤ (∏ i ∈ S, H i) * (Z^Hc')^ρc.Pmax := by
    rw [hZ'P]; exact xmax_le Z Xmax _ _ hZ1 hXmax0 hprodS hPm
  have hfro : Xc * ∏ i ∈ Js, (H i / 2) ≤ 2 * Xmax := by
    obtain ⟨d, hd, hdX⟩ := hG1
    refine le_trans ?_ hdX
    apply mul_le_mul_of_nonneg_left _ hXc.le
    rw [← Finset.prod_attach Js (fun i => H i / 2)]
    apply Finset.prod_le_prod₀ (fun i hi => by have := hHpos i.1 (hJsS i.2); positivity)
    intro i _
    have hdi : d i.1 i.2 ∈ lists i.1 := by
      letI : DecidableEq σ := fun a b => Classical.propDecidable (a = b)
      exact Finset.mem_pi.mp (mem_injPi.mp hd).1 i.1 i.2
    have hr := hratio i.1 (d i.1 i.2).val ((hlists i.1 _).mp hdi)
    rw [Set.mem_Icc, le_div_iff₀ (Real.rpow_pos_of_pos hZ0 _), one_mul] at hr
    have hn : ‖eisEmbedding (poolPrimary (childF q D) (d i.1 i.2))‖ ^ 2 =
        ((d i.1 i.2).val.absNorm : ℝ) := primeN_pool q D (d i.1 i.2)
    rw [hn, hHdef i.1]
    linarith [hr.1]
  have hXcmax : Xc * 2^I.card ≤ 2^(K+1) * (∏ i ∈ I, H i) * (Z^Hc')^ρc.Pmax :=
    g1_scale S Js hJsS H hHpos K hSK Xc Xmax _ hXc (Real.rpow_nonneg (by positivity) _) hfro
      hXmaxP
  have hXcZ : Xc ≤ Z^2 := hXcm.trans hXZ
  have hDX : bsup * Xc ≤ D := by
    calc bsup * Xc ≤ Z * Z^2 := mul_le_mul hZb hXcZ hXc.le hZ0.le
      _ = Z^3 := by ring
      _ ≤ D := hZ3
  have ha1 : ∀ i ∈ I, ∀ P ∈ lists i, ‖a i P‖ ≤ 1 := fun i hi => ha i (hSs (hIS hi))
  have hΦv : ∀ y, b' < y → Φs j y = 0 := by
    intro y hy; by_contra h; have := ((hΦs j).2 h).2; linarith
  have hΦvN : ∀ y, b' < y → star (Φs j y) = 0 := by
    intro y hy; rw [hΦv y hy, star_zero]
  have hb'0 : 0 ≤ b' := (ha'.le.trans hab)
  -- the restoration loss at this datum
  have hp0 : ∀ i, poolPrimary (childF q D) i ≠ 0 :=
    CanonicalQuadraticSieve.poolPrimary_ne_zero _ (childF_admissible q D)
  have hinj : Function.Injective (fun i => Ideal.span {poolPrimary (childF q D) i}) := by
    intro i k h
    have hi := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) i
    have hk := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) k
    exact Subtype.ext (hi.symm.trans (h.trans hk))
  have hL1 := hloss (poolPrimary (childF q D)) hp0 hinj t m hm I.card hIK (2 * bo * Xmax)
    (Z^2) hGt hmZ
  have hL2 : CL * (2 * bo * Xmax * Z^2)^(ε/8) ≤ CL * (2 * bo)^(ε/8) * Z^(ε/2) := by
    have hX4 : 2 * bo * Xmax * Z^2 ≤ (2 * bo) * Z^(4:ℝ) := by
      have h4 : Z^(4:ℝ) = Z^2 * Z^2 := by
        rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [h4]
      have h5 : Xmax * Z^2 ≤ Z^2 * Z^2 := mul_le_mul_of_nonneg_right hXZ (sq_nonneg Z)
      have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 2 * bo)
      calc 2 * bo * Xmax * Z^2 = 2 * bo * (Xmax * Z^2) := by ring
        _ ≤ 2 * bo * (Z^2 * Z^2) := h6
    have h0 : 0 ≤ 2 * bo * Xmax * Z^2 := by positivity
    calc CL * (2 * bo * Xmax * Z^2)^(ε/8) ≤ CL * ((2 * bo) * Z^(4:ℝ))^(ε/8) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hX4 (by positivity)) hCL.le
      _ = CL * (2 * bo)^(ε/8) * Z^(ε/2) := by
          rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
          ring_nf
  -- conclude for one orientation from the oriented bound
  have hfinal : ∀ (Lm Mc : ℝ), 0 ≤ Lm → Lm ≤ CL * (2 * bo * Xmax * Z^2)^(ε/8) →
      Mc ≤ Kc * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε/2) * (1 + ‖s‖)^(2*dchild) →
      Lm * Mc ≤ C * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε) * (1 + ‖s‖)^(2*dchild) := by
    intro Lm Mc hLm0 hLm hMc
    have hR0 : 0 ≤ Kc * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε/2) * (1 + ‖s‖)^(2*dchild) := by
      have := Real.rpow_pos_of_pos hZ0 (Hc' * (1 + x) + ε/2)
      positivity
    calc Lm * Mc ≤ Lm * (Kc * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε/2) *
          (1 + ‖s‖)^(2*dchild)) := mul_le_mul_of_nonneg_left hMc hLm0
      _ ≤ (CL * (2 * bo)^(ε/8) * Z^(ε/2)) *
          (Kc * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε/2) * (1 + ‖s‖)^(2*dchild)) :=
          mul_le_mul_of_nonneg_right (hLm.trans hL2) hR0
      _ = C * (1 + hv)^(2*dchild) * (Z^(ε/2) * Z^(Hc' * (1 + x) + ε/2)) *
          (1 + ‖s‖)^(2*dchild) := by rw [hCdef]; ring
      _ = C * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε) * (1 + ‖s‖)^(2*dchild) := by
          rw [← Real.rpow_add hZ0, show ε/2 + (Hc' * (1 + x) + ε/2) = Hc' * (1 + x) + ε by ring]
  have hLm0 : 0 ≤ lamA 256 I.card * (12^((t ∪ Finset.univ.filter
      (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card) *
        lamA ((t ∪ Finset.univ.filter
          (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card : ℕ) I.card) := by
    have h1 := one_le_lamA 256 (by norm_num) I.card
    have h2 := one_le_lamA ((t ∪ Finset.univ.filter
      (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card : ℕ)
      (Nat.cast_nonneg _) I.card
    positivity
  cases neg
  · -- positive orientation
    obtain ⟨hgate, hsrcZ⟩ := hU false data hq' ψ hψf
    obtain ⟨hs₂, hs₀⟩ := hsrcZ (Z^Hc') hZ'U
    have hob := oriented_bound false q D hq ψ hψf hψn (CanonicalQuadraticSieve.poolPrimary_good (childF q D) (childF_admissible q D)) rayM G hH W I lists a ha1 H Z hZ1.le data
      L ell β tpar θp v hv hvb htv hL hβ hell0 hβ1 hgateP hlists hHdef haform hZD Hc' hHc'0 meshS
      hmeshS' K hIK (Φs j) Φsep b' hb'0 hΦv (bP j) (hbP j) bsup hbsup0 hΦsepv hs₂ hs₀ hZ'1
      hCU.le hCU.le hΦ₀1 hΦ₀2 Cb hCb0 hCb c₀ hc₀ hgate hSw hPmax' s Xc hXc hXcmax hDX t m
    have ha_eq : (fun i P => if false = true then star (a i P) else a i P) = a := by
      funext i P; simp
    rw [ha_eq] at hob
    have hfin := hob.trans (show _ ≤ C * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε) *
        (1 + ‖s‖)^(2*dchild) from by
      rw [← mul_assoc, ← mul_assoc]
      rw [mul_assoc (lamA 256 I.card)]
      exact hfinal _ _ hLm0 hL1
        (mainConst_le (bP j) dchild K c₀ Cb (CU + CU) Z Hc' x ε hv s Ib (by linarith) hZ1.le
          hHc'0.le hHc2 hε.le hv0 (hIbP j)))
    convert hfin using 2
    ext y
    simp only [hIdef, Finset.mem_sdiff]
  · -- negative orientation
    rw [mobiusChildSumInj_negative, star_childLogTest]
    obtain ⟨hgate, hsrcZ⟩ := hU true data hq' (conjHom ψ) (conjHom_factors hψf)
    obtain ⟨hs₂, hs₀⟩ := hsrcZ (Z^Hc') hZ'U
    have hob := oriented_bound true q D hq (conjHom ψ) (conjHom_factors hψf)
      (fun y => by rw [norm_conjHom]; exact hψn y) (CanonicalQuadraticSieve.poolPrimary_good (childF q D) (childF_admissible q D)) rayM G hH W I lists a ha1 H Z hZ1.le data
      L ell β tpar θp v hv hvb htv hL hβ hell0 hβ1 hgateP hlists hHdef haform hZD Hc' hHc'0 meshS
      hmeshS' K hIK (fun y => star (Φs j y)) Φsep b' hb'0 hΦvN (bN j) (hbN j) bsup hbsup0
      hΦsepv hs₂ hs₀ hZ'1 hCU.le hCU.le hΦ₀1 hΦ₀2 Cb hCb0 hCb c₀ hc₀ hgate hSw hPmax' (-s) Xc
      hXc hXcmax hDX t m
    have ha_eq : (fun i P => if true = true then star (a i P) else a i P) =
        (fun i P => star (a i P)) := by
      funext i P; simp
    rw [ha_eq] at hob
    have hM := mainConst_le (bN j) dchild K c₀ Cb (CU + CU) Z Hc' x ε hv (-s) Ib (by linarith)
      hZ1.le hHc'0.le hHc2 hε.le hv0 (hIbN j)
    rw [norm_neg] at hM
    have hfin := hob.trans (show _ ≤ C * (1 + hv)^(2*dchild) * Z^(Hc' * (1 + x) + ε) *
        (1 + ‖s‖)^(2*dchild) from by
      rw [← mul_assoc, ← mul_assoc]
      rw [mul_assoc (lamA 256 I.card)]
      exact hfinal _ _ hLm0 hL1 hM)
    convert hfin using 2
    ext y
    simp only [hIdef, Finset.mem_sdiff]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.restoreChildBoundUniform_canonical
