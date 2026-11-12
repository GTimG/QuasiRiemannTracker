/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Big
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.TauMoment
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Child
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.SlotTerm

/-!
# Inverse.Restore.Core — the main column moment from the child source

**`main_column_bound`**: on the canonical pool `primePool (childF q D)`, the row moment of the
main column `mCol (childWeight ψ 1 y) (primeN p) (childLogTest Φ s) univ univ I lists a X` over
the child ball is bounded by the child source:

1. profile separation (`Sep.mCol_sep`, ratio window `2^{-(2K+1)}`, separation scale
   `Hp = 2^{K+1} ∏_I H`; the ratio from `mark_ratio`);
2. the moment in the separation frequency (`TauMoment.tau_moment_le`);
3. per frequency `θ = τ + s`: the separated row is the canonical injective slot product times the
   child inverse polynomial (`RowId.twSlots_norm_eq` with the per-prime identity `hw`,
   `ChildCol.col_eq_childPolynomial`), bounded by `Big.slots_source_bound`;
4. the height factor `(1+|θ|+hv'(θ))^d ≤ (8(1+hvc)(1+|s|))^d (1+|τ|)^d`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.SevenEighths.HeckeInverseAmplification (RowData NonzeroElement)
open OAI.SevenEighths.HeckeDyadic (polynomial)
open OAI.ConcretePrimeRowBridge (primePool)
open OAI.CanonicalQuadraticSieve (poolPrimary)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor)
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

theorem prod_tupleImage_real {σ ι : Type*} [DecidableEq ι] {I : Finset σ} {L : σ → Finset ι}
    {d : ∀ i ∈ I, ι} (hd : d ∈ injPi I L) (g : ι → ℝ) :
    ∏ P ∈ tupleImage I d, g P = ∏ i ∈ I.attach, g (d i.1 i.2) := by
  unfold tupleImage
  rw [Finset.prod_image]
  intro i _ j _ hij
  exact Subtype.ext ((mem_injPi.mp hd).2 i.1 i.2 j.1 j.2 hij)

/-- The norm of a marked image lies in `[∏H / 2^|I|, ∏H]`. -/
theorem mark_ratio {σ ι : Type*} [DecidableEq ι] (n : ι → ℝ) (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (H : σ → ℝ) (hH : ∀ i ∈ I, 0 < H i)
    (hn : ∀ i ∈ I, ∀ P ∈ L i, H i / 2 ≤ n P ∧ n P ≤ H i)
    (T : Finset ι) (hT : T.card = I.card) (hm : primeMarkInj I L a T ≠ 0) :
    (∏ i ∈ I, H i) / 2^I.card ≤ ∏ P ∈ T, n P ∧ ∏ P ∈ T, n P ≤ ∏ i ∈ I, H i := by
  obtain ⟨d, hd, hdT⟩ := exists_injPi_of_markInj_ne_zero I L a T hm
  have hsub : tupleImage I d ⊆ T := by
    intro z hz
    unfold tupleImage at hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hdT k hk
  have heq : tupleImage I d = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hT, tupleImage_card hd])
  rw [← heq, prod_tupleImage_real hd]
  have hmem : ∀ k ∈ I.attach, d k.1 k.2 ∈ L k.1 :=
    fun k _ => Finset.mem_pi.mp (mem_injPi.mp hd).1 k.1 k.2
  constructor
  · calc (∏ i ∈ I, H i) / 2^I.card = ∏ i ∈ I, (H i / 2) := by
          rw [Finset.prod_div_distrib, Finset.prod_const]
      _ = ∏ k ∈ I.attach, (H k.1 / 2) := (Finset.prod_attach I (fun i => H i / 2)).symm
      _ ≤ ∏ k ∈ I.attach, n (d k.1 k.2) :=
          Finset.prod_le_prod₀ (fun k _ => by have := hH k.1 k.2; positivity)
            (fun k hk => (hn k.1 k.2 _ (hmem k hk)).1)
  · calc ∏ k ∈ I.attach, n (d k.1 k.2) ≤ ∏ k ∈ I.attach, H k.1 :=
          Finset.prod_le_prod₀
            (fun k hk => le_trans (by have := hH k.1 k.2; positivity) (hn k.1 k.2 _ (hmem k hk)).1)
            (fun k hk => (hn k.1 k.2 _ (hmem k hk)).2)
      _ = ∏ i ∈ I, H i := Finset.prod_attach I H

/-- The height bound used for the separation frequency. -/
theorem height_split (θ τ s hv hvc : ℝ) (hθ : θ = τ + s) (hvc0 : 0 ≤ hvc)
    (hhv : hv ≤ hvc + 2 * Real.pi * ‖θ‖) :
    1 + ‖θ‖ + hv ≤ 8 * (1 + hvc) * (1 + ‖s‖) * (1 + ‖τ‖) := by
  have hpi := Real.pi_lt_d2
  have hθn : ‖θ‖ ≤ ‖τ‖ + ‖s‖ := by rw [hθ]; exact norm_add_le τ s
  have h1 := norm_nonneg τ
  have h2 := norm_nonneg s
  have h3 := norm_nonneg θ
  have h4 : 2 * Real.pi * ‖θ‖ ≤ 7 * ‖θ‖ := by nlinarith
  nlinarith [mul_nonneg hvc0 h1, mul_nonneg hvc0 h2, mul_nonneg h1 h2,
    mul_nonneg (mul_nonneg hvc0 h1) h2]

set_option maxHeartbeats 1000000 in
/-- **The main column moment from the child source.** -/
theorem main_column_bound (q D : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
    (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
    [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
    {σ : Type} [DecidableEq σ] (I : Finset σ) (lists : σ → Finset (primePool (childF q D)))
    (a : σ → primePool (childF q D) → ℂ) (H : σ → ℝ) (hH : ∀ i ∈ I, 0 < H i)
    (hnH : ∀ i ∈ I, ∀ P ∈ lists i,
      H i / 2 ≤ (P.val.absNorm : ℝ) ∧ (P.val.absNorm : ℝ) ≤ H i)
    (K : ℕ) (hIK : I.card ≤ K)
    (Φ Φsep : ℝ → ℂ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ r x hh : ℝ, 1 ≤ 2^(2*K+1) * r → r ≤ 1 → 0 < x →
      Φ (r * x) * FourierBridge.logPhase hh (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + hh) (Real.log r) * childLogTest Φsep (t + hh) x * b t)
    (bsup : ℝ) (hbsup : 0 < bsup) (hΦsep : ∀ x, bsup < x → Φsep x = 0)
    {cls : SlotClass} {ρ : AnchorRect} {Φ₀ : ℝ → ℂ} {mesh ε Z' : ℝ} {d₂ d₀ : ℕ} {C₂ C₀ : ℝ}
    (hs₂ : InverseRectAt cls ρ (fun x => Φsep x * ((x : ℂ) ^ (-(1/2 : ℂ)))) K mesh 1 1 ε Z'
      (childData q hq ψ hψ) d₂ C₂)
    (hs₀ : InverseRectAt cls ρ Φ₀ K mesh 1 1 ε Z' (childData q hq ψ hψ) d₀ C₀)
    (hZ' : 1 < Z') (hC₂ : 0 ≤ C₂) (hC₀ : 0 ≤ C₀)
    (hΦ₀1 : Φ₀ 1 = 1) (hΦ₀2 : ∀ x, 2 ≤ x → Φ₀ x = 0)
    (Cb : ℝ) (hCb0 : 0 ≤ Cb)
    (hCb : ∀ (θ : ℝ) (χ : Character) (Y : ℝ), 0 < Y → Y ≤ 1 →
      ‖polynomial χ true (childLogTest (fun x => Φsep x * ((x : ℂ) ^ (-(1/2 : ℂ)))) θ) Y 0 0‖
        ≤ Cb)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hgate : (((DetectorDictionaryInverseRawInitialGates.deletedBase
      (childData q hq ψ hψ)).modulus.absNorm : ℕ) : ℝ) < c₀)
    (ell : σ → ℝ) (β' : ℝ → σ → Ideal O → ℂ) (κ : ℝ → σ → ℂ) (hκ : ∀ θ i, ‖κ θ i‖ = 1)
    (hw : ∀ (θ : ℝ) (y : O), ∀ i ∈ I, ∀ P ∈ lists i,
      CanonicalRowCompletion.idealRowHom y P.val *
        Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
          ((lists i).map (Function.Embedding.subtype _)) (β' θ i) (Z'^(ell i)) P.val =
        κ θ i * (a i P * (childWeight (poolPrimary (childF q D)) hg ψ 1 y P *
          FourierBridge.logPhase θ (Real.log (primeN (poolPrimary (childF q D)) P)))))
    (hv' : ℝ → ℝ) (hv'0 : ∀ θ, 0 ≤ hv' θ) (hvc : ℝ) (hvc0 : 0 ≤ hvc)
    (hv'le : ∀ θ, hv' θ ≤ hvc + 2 * Real.pi * ‖θ‖)
    (hcls : ∀ (θ : ℝ) (J : Type) [Fintype J] (f : J → σ), (∀ j, f j ∈ I) →
      cls J (childData q hq ψ hψ) (fun j => (lists (f j)).map (Function.Embedding.subtype _))
        (fun j => ell (f j)) (fun j => β' θ (f j)) Z' (hv' θ))
    (h1 : ∀ i ∈ I, 0 ≤ ell i) (h2 : ∀ i ∈ I, ell i ≤ mesh)
    (h3 : ∀ i ∈ I, ∀ P ∈ lists i, Prime P.val)
    (h5 : ∀ i ∈ I, ∀ P ∈ lists i, ((P.val.absNorm : ℝ)/Z'^(ell i)) ∈ Set.Icc (1 : ℝ) 2)
    (h6 : ∀ θ, ∀ i ∈ I, ∀ P ∈ lists i, ‖β' θ i P.val‖ ≤ 1)
    (hS : ∑ i ∈ I, ell i ≤ ρ.Smax)
    (hPmax : 0 ≤ ρ.Pmax ∨ bsup * Z'^ρ.Pmax < 1)
    (R : ℝ) (hR : R ≤ Z'^(1:ℝ))
    (s X : ℝ) (hX : 0 < X) (hXmax : X / (2^(K+1) * ∏ i ∈ I, H i) ≤ Z'^ρ.Pmax)
    (hD : bsup * (X / (2^(K+1) * ∏ i ∈ I, H i)) ≤ D) :
    ∑ y ∈ nonzeroChildFrequencyBall 1 R,
        ‖mCol (childWeight (poolPrimary (childF q D)) hg ψ 1 y) (primeN (poolPrimary (childF q D)))
          (childLogTest Φ s) Finset.univ Finset.univ I lists a X‖^2 ≤
      (∫ τ, ‖b τ‖ * (1 + ‖τ‖)^(d₂+d₀))^2 *
        (QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
          ((smallConst c₀ K * max 1 Cb)^2 * ((C₂ + C₀) * Z'^((1:ℝ)+ε) *
            ((8 * (1 + hvc) * (1 + ‖s‖))^(d₂+d₀))^2))) := by
  set p := poolPrimary (childF q D) with hpdef
  have hp0 : ∀ i, p i ≠ 0 := CanonicalQuadraticSieve.poolPrimary_ne_zero _ (childF_admissible q D)
  have hpn : ∀ i, 0 < primeN p i := fun i => lt_of_lt_of_le two_pos (primeN_two_le p hp0 i)
  have hprodH : 0 < ∏ i ∈ I, H i := Finset.prod_pos hH
  set Hp : ℝ := 2^(K+1) * ∏ i ∈ I, H i with hHpdef
  have hHp : 0 < Hp := by positivity
  set Φ₂ : ℝ → ℂ := fun x => Φsep x * ((x : ℂ) ^ (-(1/2 : ℂ))) with hΦ₂
  set dd := d₂ + d₀ with hdd
  have hcost : 0 ≤ QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K := by
    unfold QRH.Record1252270103Source.Collision.collisionProjectionCost; positivity
  -- the ratio window
  have hratio : ∀ T ⊆ (Finset.univ : Finset (primePool (childF q D))), T.card = I.card →
      primeMarkInj I lists a T ≠ 0 →
      1 ≤ 2^(2*K+1) * ((∏ i ∈ T, primeN p i) / Hp) ∧ (∏ i ∈ T, primeN p i) / Hp ≤ 1 := by
    intro T _ hT hm
    have hn : ∀ i ∈ I, ∀ P ∈ lists i, H i / 2 ≤ primeN p P ∧ primeN p P ≤ H i := by
      intro i hi P hP
      rw [hpdef, primeN_pool q D P]
      exact hnH i hi P hP
    obtain ⟨hlo, hhi⟩ := mark_ratio (primeN p) I lists a H hH hn T hT hm
    have h2K : (1:ℝ) ≤ 2^(K+1) := one_le_pow₀ (by norm_num)
    constructor
    · rw [mul_div_assoc', le_div_iff₀ hHp, one_mul]
      have hc : (2:ℝ)^I.card ≤ 2^K := pow_le_pow_right₀ (by norm_num) hIK
      have h2c : (0:ℝ) < 2^I.card := by positivity
      rw [div_le_iff₀ h2c] at hlo
      have hT0 : 0 ≤ ∏ i ∈ T, primeN p i := Finset.prod_nonneg (fun i _ => (hpn i).le)
      calc Hp = 2^(K+1) * ∏ i ∈ I, H i := rfl
        _ ≤ 2^(K+1) * ((∏ i ∈ T, primeN p i) * 2^I.card) :=
            mul_le_mul_of_nonneg_left hlo (by positivity)
        _ ≤ 2^(K+1) * ((∏ i ∈ T, primeN p i) * 2^K) := by gcongr
        _ = 2^(2*K+1) * ∏ i ∈ T, primeN p i := by ring
    · rw [div_le_one hHp]
      calc ∏ i ∈ T, primeN p i ≤ ∏ i ∈ I, H i := hhi
        _ ≤ Hp := le_mul_of_one_le_left hprodH.le h2K
  have hrow := fun y : O => mCol_sep (childWeight p hg ψ 1 y) (primeN p) hpn Φ Φsep b (2*K+1)
    hsep s Finset.univ Finset.univ I lists a Hp X hHp hX hratio
  set F : O → ℝ → ℂ := fun y τ => twSlots (childWeight p hg ψ 1 y) (primeN p) Finset.univ I
    lists a Hp (τ + s) * col (childWeight p hg ψ 1 y) (primeN p) (childLogTest Φsep (τ + s))
    Finset.univ (X / Hp) with hF
  set A : ℝ := QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
    ((smallConst c₀ K * max 1 Cb)^2 * ((C₂ + C₀) * Z'^((1:ℝ)+ε) *
      ((8 * (1 + hvc) * (1 + ‖s‖))^dd)^2)) with hA
  have hZ'0 : 0 < Z' := zero_lt_one.trans hZ'
  have hA0 : 0 ≤ A := by
    have := (Real.rpow_pos_of_pos hZ'0 ((1:ℝ)+ε)).le
    positivity
  -- the rows as nonzero elements
  set rows : Finset NonzeroElement :=
    (nonzeroChildFrequencyBall 1 R).subtype (fun y => y ≠ 0) with hrowsdef
  have hsumconv : ∀ f : O → ℝ, ∑ y ∈ nonzeroChildFrequencyBall 1 R, f y = ∑ u ∈ rows, f u.val := by
    intro f
    rw [hrowsdef, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem]
    intro y hy
    unfold nonzeroChildFrequencyBall at hy
    exact Finset.ne_of_mem_erase hy
  have hrows : ∀ u ∈ rows, ‖eisEmbedding u.val‖^2 ≤ Z'^(1:ℝ) := by
    intro u hu
    rw [hrowsdef, Finset.mem_subtype] at hu
    have h := (mem_nonzeroChildFrequencyBall 1 one_ne_zero R u.val).mp hu
    rw [one_mul] at h
    exact h.2.trans hR
  -- the per-frequency bound
  have hbound : ∀ τ : ℝ, ∑ y ∈ nonzeroChildFrequencyBall 1 R, ‖F y τ‖^2 ≤ A * ((1 + ‖τ‖)^dd)^2 := by
    intro τ
    set θ := τ + s with hθ
    have hY0 : 0 < X / Hp := div_pos hX hHp
    have hvan : ∀ x, bsup < x → childLogTest Φsep θ x = 0 := by
      intro x hx; unfold childLogTest; rw [hΦsep x hx, zero_mul]
    have hrowid : ∀ u : NonzeroElement, ‖F u.val τ‖ =
        ‖polynomial ((childData q hq ψ hψ).character u) true (childLogTest Φ₂ θ) (X / Hp) 0 0 *
          injSlots u.val (fun j : {i // i ∈ I} => (lists j.1).map (Function.Embedding.subtype _))
            (fun j => β' θ j.1) (fun j => Z'^(ell j.1))‖ := by
      intro u
      have ht := twSlots_norm_eq (Function.Embedding.subtype _) (childWeight p hg ψ 1 u.val)
        (primeN p) hpn I lists a Hp θ hHp u.val (fun j => β' θ j.1) (fun j => Z'^(ell j.1))
        (fun j => κ θ j.1) (fun j => hκ θ j.1) (fun j P hP => hw θ u.val j.1 j.2 P hP)
      have hc := col_eq_childPolynomial q D hq ψ hψ hg u (childLogTest Φsep θ) bsup (X / Hp)
        hY0 hvan hD
      rw [childLogTest_cpow] at hc
      simp only [hF]
      rw [norm_mul, ht, hc, norm_mul, mul_comm]
    have hPmax' : 0 ≤ ρ.Pmax ∨ ∀ χ : Character,
        polynomial χ true (childLogTest Φ₂ θ) (X / Hp) 0 0 = 0 := by
      rcases hPmax with h | h
      · exact Or.inl h
      · right
        intro χ
        apply polynomial_eq_zero_of_small χ _ bsup _ hY0
        · intro x hx; unfold childLogTest; rw [hΦ₂]; simp only [hΦsep x hx, zero_mul]
        · calc bsup * (X / Hp) ≤ bsup * Z'^ρ.Pmax := mul_le_mul_of_nonneg_left hXmax hbsup.le
            _ < 1 := h
    have hsb := slots_source_bound hs₂ hs₀ hZ' hC₂ hC₀ hΦ₀1 hΦ₀2 θ Cb hCb0 (hCb θ) c₀ hc₀ hgate
      (κ := {i // i ∈ I}) (by rw [Fintype.card_coe]; exact hIK)
      (fun j => (lists j.1).map (Function.Embedding.subtype _)) (fun j => ell j.1)
      (fun j => β' θ j.1) (hv' θ) (hv'0 θ)
      (fun J _ f => hcls θ J (fun j => (f j).1) (fun j => (f j).2))
      (fun j => h1 j.1 j.2) (fun j => h2 j.1 j.2)
      (fun j P hP => by
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.mp hP
        exact h3 j.1 j.2 Q hQ)
      (fun j P hP => by
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.mp hP
        exact h5 j.1 j.2 Q hQ)
      (fun j P hP => by
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.mp hP
        exact h6 θ j.1 j.2 Q hQ)
      (by rw [Finset.sum_coe_sort I ell]; exact hS)
      (X / Hp) hY0 hXmax hPmax' rows hrows
    rw [hsumconv (fun y => ‖F y τ‖^2)]
    simp only [hrowid]
    refine hsb.trans ?_
    rw [hA]
    have hfac : ((1 + ‖θ‖ + hv' θ)^dd)^2 ≤ ((8 * (1 + hvc) * (1 + ‖s‖))^dd)^2 * ((1 + ‖τ‖)^dd)^2 := by
      rw [← mul_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by have := hv'0 θ; positivity)
      apply pow_le_pow_left₀ (by have := hv'0 θ; positivity)
      exact height_split θ τ s (hv' θ) hvc hθ hvc0 (hv'le θ)
    have hZe : 0 ≤ Z'^((1:ℝ)+ε) := (Real.rpow_pos_of_pos hZ'0 _).le
    have hCC : 0 ≤ C₂ + C₀ := by linarith
    calc QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
          ((smallConst c₀ K * max 1 Cb)^2 * ((C₂ + C₀) * Z'^((1:ℝ)+ε) *
            ((1 + ‖θ‖ + hv' θ)^dd)^2))
        ≤ QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
          ((smallConst c₀ K * max 1 Cb)^2 * ((C₂ + C₀) * Z'^((1:ℝ)+ε) *
            (((8 * (1 + hvc) * (1 + ‖s‖))^dd)^2 * ((1 + ‖τ‖)^dd)^2))) := by
          gcongr
      _ = _ := by ring
  have key := tau_moment_le (nonzeroChildFrequencyBall 1 R) b F dd A hA0
    (fun y _ => (hrow y).1) hbound
  calc ∑ y ∈ nonzeroChildFrequencyBall 1 R,
        ‖mCol (childWeight p hg ψ 1 y) (primeN p) (childLogTest Φ s) Finset.univ Finset.univ I
          lists a X‖^2
      = ∑ y ∈ nonzeroChildFrequencyBall 1 R, ‖∫ τ, b τ * F y τ‖^2 := by
        apply Finset.sum_congr rfl
        intro y _
        rw [(hrow y).2]
    _ ≤ (∫ τ, ‖b τ‖ * (1 + ‖τ‖)^dd)^2 * A := key

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.main_column_bound
