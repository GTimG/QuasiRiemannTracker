/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Core

/-!
# Inverse.Restore.Datum — the physical child moment of one datum

**`child_sum_bound`**: the positive physical injective child moment on `univ \ t` with mask `m` is
`≤ lamA 256 |I| · 12^(v+|I|) · lamA (v+|I|) |I| · Mb` (`Child.mobiusChildSumInj_le_main` with slot
floors `h = H/2` and frozen mass `A = 256`, `frozen_mass_le`), where `Mb` is the bound of
`Core.main_column_bound`, applied to every sub-collection `I' ⊆ I` at every reduced scale
(`scale_bounds`: `X' ∏_{I\I'} H/2 ≤ Xc` gives `X'/(2^{K+1}∏_{I'} H) ≤ Z'^{Pmax}` from
`Xc 2^{|I|} ≤ 2^{K+1} ∏_I H · Z'^{Pmax}`).
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

theorem scale_bounds {σ : Type*} [DecidableEq σ] (I I' : Finset σ) (hII : I' ⊆ I) (H : σ → ℝ)
    (hH : ∀ i ∈ I, 2 ≤ H i) (K : ℕ) (Xc X' Q : ℝ) (hX' : 0 < X')
    (hXc : Xc * 2^I.card ≤ 2^(K+1) * (∏ i ∈ I, H i) * Q)
    (hX'c : X' * ∏ i ∈ I \ I', H i / 2 ≤ Xc) :
    X' / (2^(K+1) * ∏ i ∈ I', H i) ≤ Q ∧ X' ≤ Xc := by
  have hHp : ∀ i ∈ I, 0 < H i := fun i hi => lt_of_lt_of_le two_pos (hH i hi)
  set A' := ∏ i ∈ I', H i with hA'
  set B := ∏ i ∈ I \ I', H i with hB
  have hA'0 : 0 < A' := Finset.prod_pos (fun i hi => hHp i (hII hi))
  have hB0 : 0 < B := Finset.prod_pos (fun i hi => hHp i (Finset.mem_sdiff.mp hi).1)
  have hprod : B * A' = ∏ i ∈ I, H i := Finset.prod_sdiff hII
  have hB2 : ∏ i ∈ I \ I', H i / 2 = B / 2^(I \ I').card := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
  have hge1 : (1:ℝ) ≤ ∏ i ∈ I \ I', H i / 2 := by
    have h := Finset.prod_le_prod₀ (s := I \ I') (f := fun _ => (1:ℝ)) (g := fun i => H i / 2)
      (fun _ _ => zero_le_one)
      (fun i hi => by have := hH i (Finset.mem_sdiff.mp hi).1; linarith)
    simpa using h
  have hX'Xc : X' ≤ Xc := le_trans (le_mul_of_one_le_right hX'.le hge1) hX'c
  refine ⟨?_, hX'Xc⟩
  rw [hB2] at hX'c
  have hc2 : (0:ℝ) < 2^(I \ I').card := by positivity
  have hcard : (2:ℝ)^(I \ I').card ≤ 2^I.card :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.sdiff_subset)
  have h1 : X' * B ≤ Xc * 2^(I \ I').card := by
    rw [mul_div_assoc', div_le_iff₀ hc2] at hX'c; exact hX'c
  have hXc0 : 0 ≤ Xc := le_trans hX'.le hX'Xc
  have h2 : X' * B ≤ 2^(K+1) * (B * A') * Q := by
    rw [hprod]
    calc X' * B ≤ Xc * 2^(I \ I').card := h1
      _ ≤ Xc * 2^I.card := mul_le_mul_of_nonneg_left hcard hXc0
      _ ≤ _ := hXc
  rw [div_le_iff₀ (by positivity)]
  have h3 : X' * B ≤ (Q * (2^(K+1) * A')) * B := by nlinarith
  exact le_of_mul_le_mul_right h3 hB0

theorem pool_frozen_mass_le (q D : ℕ)
    [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
    (L : Finset (primePool (childF q D)))
    (a : primePool (childF q D) → ℂ) (Hi : ℝ) (hHi : 0 < Hi)
    (hn : ∀ P ∈ L, Hi / 2 ≤ (P.val.absNorm : ℝ) ∧ (P.val.absNorm : ℝ) ≤ Hi)
    (ha : ∀ P ∈ L, ‖a P‖ ≤ 1) :
    ∑ P ∈ L, ‖a P‖ * (primeN (poolPrimary (childF q D)) P)⁻¹ ≤ 256 := by
  have hcard : (L.card : ℝ) ≤ 128 * Hi := by
    have h := card_le_of_norm_le (L.map (Function.Embedding.subtype _)) Hi hHi.le (by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.mp hP
      refine ⟨?_, (hn Q hQ).2⟩
      have := (pool_facts q D Q).2.1
      rw [Ideal.zero_eq_bot]; exact this)
    rwa [Finset.card_map] at h
  have hterm : ∀ P ∈ L, ‖a P‖ * (primeN (poolPrimary (childF q D)) P)⁻¹ ≤ 2 / Hi := by
    intro P hP
    rw [primeN_pool q D P]
    have hN : Hi / 2 ≤ (P.val.absNorm : ℝ) := (hn P hP).1
    have hN0 : 0 < (P.val.absNorm : ℝ) := lt_of_lt_of_le (by positivity) hN
    calc ‖a P‖ * (P.val.absNorm : ℝ)⁻¹ ≤ 1 * (Hi / 2)⁻¹ := by
          apply mul_le_mul (ha P hP) _ (inv_nonneg.mpr hN0.le) zero_le_one
          exact inv_anti₀ (by positivity) hN
      _ = 2 / Hi := by field_simp
  calc ∑ P ∈ L, ‖a P‖ * (primeN (poolPrimary (childF q D)) P)⁻¹ ≤ ∑ _P ∈ L, 2 / Hi :=
        Finset.sum_le_sum hterm
    _ = L.card * (2 / Hi) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 128 * Hi * (2 / Hi) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 256 := by field_simp; ring

/-- The main-column constant of `Core.main_column_bound`. -/
def mainConst (b : 𝓢(ℝ, ℂ)) (d K : ℕ) (c₀ Cb C Z' ε hvc s : ℝ) : ℝ :=
  (∫ τ, ‖b τ‖ * (1 + ‖τ‖)^d)^2 *
    (QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
      ((smallConst c₀ K * max 1 Cb)^2 * (C * Z'^((1:ℝ)+ε) *
        ((8 * (1 + hvc) * (1 + ‖s‖))^d)^2)))

set_option maxHeartbeats 1000000 in
/-- **The physical child moment of one datum (positive orientation).** -/
theorem child_sum_bound (q D : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ) (hψn : ∀ x, ‖ψ x‖ ≤ 1)
    (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
    [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
    {σ : Type} (I : Finset σ) (lists : σ → Finset (primePool (childF q D)))
    (a : σ → primePool (childF q D) → ℂ) (ha : ∀ i ∈ I, ∀ P ∈ lists i, ‖a i P‖ ≤ 1)
    (H : σ → ℝ) (hH2 : ∀ i ∈ I, 2 ≤ H i)
    (hnH : ∀ i ∈ I, ∀ P ∈ lists i,
      H i / 2 ≤ (P.val.absNorm : ℝ) ∧ (P.val.absNorm : ℝ) ≤ H i)
    (K : ℕ) (hIK : I.card ≤ K)
    (Φ Φsep : ℝ → ℂ) (bΦ : ℝ) (hbΦ : 0 ≤ bΦ) (hΦv : ∀ x, bΦ < x → Φ x = 0) (b : 𝓢(ℝ, ℂ))
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
    (Z Hc : ℝ) (hR : Z^Hc ≤ Z'^(1:ℝ))
    (s Xc : ℝ) (hXc : 0 < Xc) (hXcmax : Xc * 2^I.card ≤ 2^(K+1) * (∏ i ∈ I, H i) * Z'^ρ.Pmax)
    (hD : bsup * Xc ≤ D) (t : Finset (primePool (childF q D))) (m : O) :
    mobiusChildSumInj (poolPrimary (childF q D)) hg (Finset.univ \ t) ψ m I lists a
        (childLogTest Φ s) Xc false Z Hc ≤
      lamA 256 I.card * (12^((t ∪ Finset.univ.filter
          (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card) *
        (lamA ((t ∪ Finset.univ.filter
          (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card : ℕ) I.card *
          mainConst b (d₂+d₀) K c₀ Cb (C₂ + C₀) Z' ε hvc s)) := by
  have hp0 : ∀ i, poolPrimary (childF q D) i ≠ 0 :=
    CanonicalQuadraticSieve.poolPrimary_ne_zero _ (childF_admissible q D)
  have hinj : Function.Injective (fun i => Ideal.span {poolPrimary (childF q D) i}) := by
    intro i j h
    have hi := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) i
    have hj := CanonicalQuadraticSieve.poolPrimary_span _ (childF_admissible q D) j
    exact Subtype.ext (hi.symm.trans (h.trans hj))
  have hHpos : ∀ i ∈ I, 0 < H i := fun i hi => lt_of_lt_of_le two_pos (hH2 i hi)
  have hΦ' : ∀ x, bΦ < x → childLogTest Φ s x = 0 := by
    intro x hx; unfold childLogTest; rw [hΦv x hx, zero_mul]
  refine mobiusChildSumInj_le_main (poolPrimary (childF q D)) hp0 hinj hg t ψ hψn m I lists a
    (childLogTest Φ s) bΦ hbΦ hΦ' Xc hXc Z Hc 256 (by norm_num)
    (fun i hi => pool_frozen_mass_le q D (lists i) (a i) (H i) (hHpos i hi) (hnH i hi) (ha i hi))
    ha (fun i => H i / 2) (fun i hi => by have := hHpos i hi; positivity)
    (fun i hi P hP => by rw [primeN_pool q D P]; exact (hnH i hi P hP).1) _ ?_
  intro I' hI' X' hX' hX'c
  obtain ⟨hY, hX'Xc⟩ := scale_bounds I I' hI' H hH2 K Xc X' (Z'^ρ.Pmax) hX' hXcmax hX'c
  have hY1 : X' / (2^(K+1) * ∏ i ∈ I', H i) ≤ X' := by
    apply div_le_self hX'.le
    have h1' : (1:ℝ) ≤ ∏ i ∈ I', H i := by
      have h := Finset.prod_le_prod₀ (s := I') (f := fun _ => (1:ℝ)) (g := H)
        (fun _ _ => zero_le_one) (fun i hi => by have := hH2 i (hI' hi); linarith)
      simpa using h
    have h2' : (1:ℝ) ≤ 2^(K+1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hsub : ∀ i ∈ I', i ∈ I := fun i hi => hI' hi
  exact main_column_bound q D hq ψ hψ hg I' lists a H (fun i hi => hHpos i (hsub i hi))
    (fun i hi => hnH i (hsub i hi)) K ((Finset.card_le_card hI').trans hIK) Φ Φsep b hsep bsup
    hbsup hΦsep hs₂ hs₀ hZ' hC₂ hC₀ hΦ₀1 hΦ₀2 Cb hCb0 hCb c₀ hc₀ hgate ell β' κ hκ
    (fun θ y i hi => hw θ y i (hsub i hi)) hv' hv'0 hvc hvc0 hv'le
    (fun θ J _ f hf => hcls θ J f (fun j => hsub _ (hf j)))
    (fun i hi => h1 i (hsub i hi)) (fun i hi => h2 i (hsub i hi))
    (fun i hi => h3 i (hsub i hi)) (fun i hi => h5 i (hsub i hi))
    (fun θ i hi => h6 θ i (hsub i hi))
    ((Finset.sum_le_sum_of_subset_of_nonneg hI' (fun i hi _ => h1 i hi)).trans hS)
    hPmax (Z^Hc) hR s X' hX' hY
    (le_trans (mul_le_mul_of_nonneg_left (hY1.trans hX'Xc) hbsup.le) hD)

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.child_sum_bound
