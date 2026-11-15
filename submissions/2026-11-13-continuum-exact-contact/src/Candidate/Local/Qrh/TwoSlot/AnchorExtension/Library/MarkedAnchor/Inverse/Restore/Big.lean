/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.SourceCall
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.SmallSlots
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.RowId

/-!
# Inverse.Restore.Big — one separated child row moment from the child source

**`slots_source_bound`**: the row moment of `polynomial(data.character u)(childLogTest Φ₂ θ)(Y) ·
injSlots u L β (Z^ell)` at a column scale `Y ≤ Z^{Pmax}` is bounded by the child source:

* small/big split at a free dyadic gap above `c₀ > N(mod δ')` (`SmallSlots.exists_gap`): the
  small factor is bounded pointwise (`≤ (128·2^{K+1} c₀)^K`), the big slots pass the deletion
  gate and their pools are disjoint from the small ones (`injSlots_split`);
* `Y ≥ 1`: the source at `r = log_Z Y` with the profile `Φ₂`;
* `Y < 1`: the column is bounded (`Cb`) and the source is used with the unit bump `Φ₀` at `r = 0`
  (`polynomial_unit_profile`), or the column vanishes (`Pmax < 0`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open OAI.SevenEighths.InverseMoment (childLogTest)
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- The small-slot constant. -/
def smallConst (c₀ : ℝ) (K : ℕ) : ℝ := (max 1 (128 * (2^(K+1) * c₀)))^K

theorem one_le_smallConst (c₀ : ℝ) (K : ℕ) : 1 ≤ smallConst c₀ K :=
  one_le_pow₀ (le_max_left _ _)

set_option maxHeartbeats 1000000 in
theorem slots_source_bound {cls : SlotClass} {ρ : AnchorRect} {Φ₂ Φ₀ : ℝ → ℂ} {K : ℕ}
    {mesh ε Z : ℝ} {data : RowData} {d₂ d₀ : ℕ} {C₂ C₀ : ℝ}
    (hs₂ : InverseRectAt cls ρ Φ₂ K mesh 1 1 ε Z data d₂ C₂)
    (hs₀ : InverseRectAt cls ρ Φ₀ K mesh 1 1 ε Z data d₀ C₀)
    (hZ : 1 < Z) (hC₂ : 0 ≤ C₂) (hC₀ : 0 ≤ C₀)
    (hΦ₀1 : Φ₀ 1 = 1) (hΦ₀2 : ∀ x, 2 ≤ x → Φ₀ x = 0) (θ : ℝ)
    (Cb : ℝ) (hCb0 : 0 ≤ Cb)
    (hCb : ∀ (χ : Character) (Y : ℝ), 0 < Y → Y ≤ 1 →
      ‖polynomial χ true (childLogTest Φ₂ θ) Y 0 0‖ ≤ Cb)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hgate : (((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℕ) : ℝ)
      < c₀)
    {κ : Type} [Fintype κ] [DecidableEq κ] (hK : Fintype.card κ ≤ K)
    (L : κ → Finset (Ideal O)) (ell : κ → ℝ) (β : κ → Ideal O → ℂ) (hv : ℝ) (hv0 : 0 ≤ hv)
    (hcls : ∀ (J : Type) [Fintype J] (f : J ↪ κ),
      cls J data (fun j => L (f j)) (fun j => ell (f j)) (fun j => β (f j)) Z hv)
    (h1 : ∀ i, 0 ≤ ell i) (h2 : ∀ i, ell i ≤ mesh) (h3 : ∀ i, ∀ P ∈ L i, Prime P)
    (h5 : ∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Set.Icc (1 : ℝ) 2)
    (h6 : ∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1)
    (hS : ∑ i, ell i ≤ ρ.Smax)
    (Y : ℝ) (hY0 : 0 < Y) (hYmax : Y ≤ Z^ρ.Pmax)
    (hPmax : 0 ≤ ρ.Pmax ∨ ∀ χ : Character, polynomial χ true (childLogTest Φ₂ θ) Y 0 0 = 0)
    (rows : Finset NonzeroElement)
    (hrows : ∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z^(1:ℝ)) :
    ∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 *
        injSlots u.val L β (fun i => Z^(ell i))‖^2 ≤
      QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K *
        ((smallConst c₀ K * max 1 Cb)^2 * ((C₂ + C₀) * Z^((1:ℝ)+ε) *
          ((1+‖θ‖+hv)^(d₂+d₀))^2)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hZ1 : 1 ≤ Z := hZ.le
  have hcost : 0 ≤ QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K := by
    unfold QRH.Record1252270103Source.Collision.collisionProjectionCost; positivity
  -- the gap
  obtain ⟨jg, hjg, hgap⟩ := exists_gap (Finset.univ : Finset κ) (fun i => Z^(ell i)) c₀ hc₀
  rw [Finset.card_univ] at hjg
  obtain ⟨s, hs_def⟩ : ∃ s : κ → Prop, ∀ i, s i ↔ Z^(ell i) ≤ 2^jg * c₀ := ⟨_, fun i => Iff.rfl⟩
  have hbig : ∀ i, ¬ s i → 2^(jg+1) * c₀ < Z^(ell i) := by
    intro i hi
    by_contra hle
    push_neg at hle
    exact hgap i (Finset.mem_univ i) ⟨lt_of_not_ge (fun h => hi ((hs_def i).mpr h)), hle⟩
  have hNle : ∀ i, ∀ P ∈ L i, (P.absNorm : ℝ) ≤ 2 * Z^(ell i) := by
    intro i P hP
    have := (h5 i P hP).2
    rwa [div_le_iff₀ (Real.rpow_pos_of_pos hZ0 _)] at this
  have hNge : ∀ i, ∀ P ∈ L i, Z^(ell i) ≤ (P.absNorm : ℝ) := by
    intro i P hP
    have := (h5 i P hP).1
    rwa [le_div_iff₀ (Real.rpow_pos_of_pos hZ0 _), one_mul] at this
  have hdis : ∀ i j, s i → ¬ s j → Disjoint (L i) (L j) := by
    intro i j hi hj
    rw [Finset.disjoint_left]
    intro P hPi hPj
    have h1' := hNle i P hPi
    have h2' := hNge j P hPj
    have h3' := hbig j hj
    have : (2:ℝ)^(jg+1) * c₀ = 2 * (2^jg * c₀) := by ring
    have hs : Z^(ell i) ≤ 2^jg * c₀ := (hs_def i).mp hi
    linarith
  -- small factor
  have hsmall : ∀ u : NonzeroElement, ‖injSlots u.val (fun i : {i // s i} => L i.1)
      (fun i => β i.1) (fun i => Z^(ell i.1))‖ ≤ smallConst c₀ K := by
    intro u
    refine (norm_injSlots_le u.val (fun i : {i // s i} => L i.1) (fun i => β i.1)
      (fun i => Z^(ell i.1)) (fun i => Real.one_le_rpow hZ1 (h1 i.1))
      (fun i => h6 i.1)).trans ?_
    have hcard : ∀ i : {i // s i}, ((L i.1).card : ℝ) ≤ max 1 (128 * (2^(K+1) * c₀)) := by
      intro i
      refine (card_le_of_norm_le (L i.1) (2^(K+1) * c₀) (by positivity) ?_).trans
        (le_max_right _ _)
      intro P hP
      refine ⟨(h3 i.1 P hP).ne_zero, ?_⟩
      have := hNle i.1 P hP
      have hs : Z^(ell i.1) ≤ 2^jg * c₀ := (hs_def i.1).mp i.2
      have hpow : (2:ℝ)^jg ≤ 2^K := pow_le_pow_right₀ (by norm_num) (hjg.trans hK)
      have : (2:ℝ)^(K+1) * c₀ = 2 * (2^K * c₀) := by ring
      nlinarith
    calc ∏ i : {i // s i}, ((L i.1).card : ℝ)
        ≤ ∏ _i : {i // s i}, max 1 (128 * (2^(K+1) * c₀)) :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcard i)
      _ = (max 1 (128 * (2^(K+1) * c₀)))^(Fintype.card {i // s i}) := by
          rw [Finset.prod_const, Finset.card_univ]
      _ ≤ smallConst c₀ K := by
          unfold smallConst
          exact pow_le_pow_right₀ (le_max_left _ _)
            ((Fintype.card_subtype_le _).trans hK)
  -- the big slots
  have hKι : Fintype.card {i // ¬ s i} ≤ K := (Fintype.card_subtype_le _).trans hK
  have hclsι : ∀ (J : Type) [Fintype J] (f : J ↪ {i // ¬ s i}),
      cls J data (fun j => L (f j).1) (fun j => ell (f j).1) (fun j => β (f j).1) Z hv :=
    fun J _ f => hcls J (f.trans (Function.Embedding.subtype _))
  have h7ι : ∀ i : {i // ¬ s i}, (((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm
      : ℕ) : ℝ) < Z^(ell i.1) := by
    intro i
    have h := hbig i.1 i.2
    have : c₀ ≤ 2^(jg+1) * c₀ := le_mul_of_one_le_left hc₀.le (one_le_pow₀ (by norm_num))
    linarith
  have hSι : ∑ i : {i // ¬ s i}, ell i.1 ≤ ρ.Smax := by
    have hsum := Fintype.sum_subtype_add_sum_subtype s ell
    have : 0 ≤ ∑ i : {i // s i}, ell i.1 := Finset.sum_nonneg (fun i _ => h1 i.1)
    linarith
  have hSι0 : 0 ≤ ∑ i : {i // ¬ s i}, ell i.1 := Finset.sum_nonneg (fun i _ => h1 i.1)
  have hsplit : ∀ u : NonzeroElement, injSlots u.val L β (fun i => Z^(ell i)) =
      injSlots u.val (fun i : {i // s i} => L i.1) (fun i => β i.1) (fun i => Z^(ell i.1)) *
        injSlots u.val (fun i  : {i // ¬ s i} => L i.1) (fun i => β i.1) (fun i => Z^(ell i.1)) :=
    fun u => injSlots_split u.val s L β (fun i => Z^(ell i)) hdis
  set Sm : NonzeroElement → ℂ := fun u =>
    injSlots u.val (fun i : {i // s i} => L i.1) (fun i => β i.1) (fun i => Z^(ell i.1)) with hSm
  have hCs0 : 0 ≤ smallConst c₀ K := zero_le_one.trans (one_le_smallConst c₀ K)
  have hθ1 : 1 ≤ 1 + ‖θ‖ + hv := by have := norm_nonneg θ; linarith
  have hfac₂ : ((1+‖θ‖+hv)^d₂)^2 ≤ ((1+‖θ‖+hv)^(d₂+d₀))^2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hθ1 (by omega)) 2
  have hfac₀ : ((1+‖(0:ℝ)‖+hv)^d₀)^2 ≤ ((1+‖θ‖+hv)^(d₂+d₀))^2 := by
    apply pow_le_pow_left₀ (by positivity)
    calc (1+‖(0:ℝ)‖+hv)^d₀ ≤ (1+‖θ‖+hv)^d₀ :=
          pow_le_pow_left₀ (by positivity) (by simp only [norm_zero]; linarith [norm_nonneg θ]) _
      _ ≤ (1+‖θ‖+hv)^(d₂+d₀) := pow_le_pow_right₀ hθ1 (by omega)
  have hZe : 0 ≤ Z^((1:ℝ)+ε) := (Real.rpow_pos_of_pos hZ0 _).le
  have hfin : 0 ≤ ((1+‖θ‖+hv)^(d₂+d₀))^2 := by positivity
  have hmb : 1 ≤ max 1 Cb := le_max_left _ _
  by_cases hY1 : 1 ≤ Y
  · -- Case A: the source at `r = log_Z Y`
    set r := Real.logb Z Y with hr
    have hZr : Z^r = Y := Real.rpow_logb hZ0 hZ.ne' hY0
    have hr0 : 0 ≤ r := Real.logb_nonneg hZ hY1
    have hrP : r ≤ ρ.Pmax := by
      rw [hr, Real.logb_le_iff_le_rpow hZ hY0]; exact hYmax
    have hadm : ρ.Admissible r (∑ i : {i // ¬ s i}, ell i.1) 1 :=
      ⟨hr0, by rw [mul_one]; exact hrP, hSι0, by rw [mul_one]; exact hSι⟩
    have h := source_inj_bound hs₂ hZ1 hC₂ hKι (fun i  : {i // ¬ s i} => L i.1) (fun i => ell i.1)
      (fun i => β i.1) hv hv0 hclsι (fun i => h1 i.1) (fun i => h2 i.1) (fun i => h3 i.1)
      (fun i => h5 i.1) (fun i => h6 i.1) h7ι r hadm rows hrows θ Sm (smallConst c₀ K) hCs0
      (fun u _ => hsmall u)
    rw [hZr] at h
    calc ∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 *
          injSlots u.val L β (fun i => Z^(ell i))‖^2
        = ∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 * Sm u *
          injSlots u.val (fun i  : {i // ¬ s i} => L i.1) (fun i => β i.1) (fun i => Z^(ell i.1))‖^2 := by
          apply Finset.sum_congr rfl; intro u _; rw [hsplit u, ← mul_assoc]
      _ ≤ _ := h
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hcost
          have hm : (smallConst c₀ K)^2 ≤ (smallConst c₀ K * max 1 Cb)^2 :=
            pow_le_pow_left₀ hCs0 (le_mul_of_one_le_right hCs0 hmb) 2
          have hc : C₂ * Z^((1:ℝ)+ε) * ((1+‖θ‖+hv)^d₂)^2 ≤
              (C₂ + C₀) * Z^((1:ℝ)+ε) * ((1+‖θ‖+hv)^(d₂+d₀))^2 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hZe) hfac₂
              (by positivity) (by positivity)
          exact mul_le_mul hm hc (by positivity) (by positivity)
  · -- Case B: the column scale is `< 1`
    push_neg at hY1
    rcases hPmax with hP0 | hzero
    · have hadm : ρ.Admissible 0 (∑ i : {i // ¬ s i}, ell i.1) 1 :=
        ⟨le_rfl, by rw [mul_one]; exact hP0, hSι0, by rw [mul_one]; exact hSι⟩
      have hw : ∀ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 * Sm u‖ ≤
          max 1 Cb * smallConst c₀ K := by
        intro u _
        rw [norm_mul]
        exact mul_le_mul ((hCb _ Y hY0 hY1.le).trans (le_max_right _ _)) (hsmall u)
          (norm_nonneg _) (zero_le_one.trans hmb)
      have h := source_inj_bound hs₀ hZ1 hC₀ hKι (fun i  : {i // ¬ s i} => L i.1) (fun i => ell i.1)
        (fun i => β i.1) hv hv0 hclsι (fun i => h1 i.1) (fun i => h2 i.1) (fun i => h3 i.1)
        (fun i => h5 i.1) (fun i => h6 i.1) h7ι 0 hadm rows hrows 0
        (fun u => polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 * Sm u)
        (max 1 Cb * smallConst c₀ K) (by positivity) hw
      have hone : ∀ u : NonzeroElement,
          polynomial (data.character u) true (childLogTest Φ₀ 0) (Z^(0:ℝ)) 0 0 = 1 := by
        intro u
        rw [Real.rpow_zero, childLogTest_zero]
        exact polynomial_unit_profile _ Φ₀ hΦ₀1 hΦ₀2
      simp only [hone, one_mul] at h
      calc ∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 *
            injSlots u.val L β (fun i => Z^(ell i))‖^2
          = ∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 * Sm u *
            injSlots u.val (fun i  : {i // ¬ s i} => L i.1) (fun i => β i.1) (fun i => Z^(ell i.1))‖^2 := by
            apply Finset.sum_congr rfl; intro u _; rw [hsplit u, ← mul_assoc]
        _ ≤ _ := h
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hcost
            have hm : (max 1 Cb * smallConst c₀ K)^2 = (smallConst c₀ K * max 1 Cb)^2 := by ring
            rw [hm]
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hZe) hfac₀
              (by positivity) (by positivity)
    · have hz : ∀ u ∈ rows, ‖polynomial (data.character u) true (childLogTest Φ₂ θ) Y 0 0 *
          injSlots u.val L β (fun i => Z^(ell i))‖^2 = 0 := by
        intro u _; rw [hzero, zero_mul, norm_zero]; ring
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      positivity

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.slots_source_bound
