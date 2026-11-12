/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 10: the provable label hypotheses of `RootLabelData`.

* `column_lower` (field `hcol`): a column with nonzero literal coefficient has
  `N(I)·N(d₁)N(d₂) ≥ a²·X₁X₂·∏ Pᵢ` (slot profiles supported in `[1,2]`, ordinary profiles in
  `[a,b]`, `X₁X₂ = Y₁Y₂`); hence `hcol` holds with `clow = a²` on canonical
  sources (`hcol_of_canonical`). The factor `N(d₁)N(d₂)` is cancelled by the frame energy.
* `lA_eq_primary`, `spanInj_holds` (field `hspanInj`): the second twist is the primary generator
  of `∏_P P^{min} · ∏_{nonunit} P`, hence determined by its ideal.
* `mult_le` (fields `hmultC`, `hmultD`): the labels with a given column `G` number at most
  `τ(G²)·2^{ω(G)} ≤ τ(G²)²` (cube-free columns divide `rad(G)²`).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly9

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedHeightEnergy
open MixedCommonCoefficient MixedLiteralAllocation MixedTupleRows

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentRectangle CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### (8) The column-norm lower bound -/

theorem norm_le_of_profile {W : ℝ → ℂ} {a b x : ℝ} (hs : Function.support W ⊆ Set.Icc a b)
    (h : W x ≠ 0) : a ≤ x := (hs h).1

/-- **One tuple.** -/
theorem tuple_lower {ι : Type*} [Fintype ι] (R : Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ)
    (P : ι → ℝ) (hP : ∀ i, 0 < P i) (hW : ∀ i, Function.support (Wslot i) ⊆ Set.Icc (1:ℝ) 2)
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hXY : X₁ * X₂ = Y₁ * Y₂) (B₁ B₂ seed : Id) (v : Tuple ι)
    (h : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v ≠ 0) :
    a^2 * (X₁ * X₂) * ∏ i, P i ≤
      (B₁.absNorm : ℝ) * (B₂.absNorm : ℝ) * (Ideal.absNorm (finiteTupleProduct v) : ℝ) := by
  unfold profileCoefficient at h
  have hprod := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hrect := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  -- slots
  have hslot : ∀ i, P i ≤ (Ideal.absNorm (v (Sum.inl i)) : ℝ) := by
    intro i
    have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ _)
    have hw := right_ne_zero_of_mul hi
    have h1 := (hW i hw).1
    rwa [le_div_iff₀ (hP i), one_mul] at h1
  -- ordinary parts
  have hord : a^2 * (X₁ * X₂) ≤ ((B₁ * v (Sum.inr 0)).absNorm : ℝ) *
      ((B₂ * v (Sum.inr 1)).absNorm : ℝ) := by
    unfold idealRectangle at hrect
    by_cases h1 : W₁ (((B₁ * v (Sum.inr 0)).absNorm : ℝ) / X₁) *
        W₂ (((B₂ * v (Sum.inr 1)).absNorm : ℝ) / X₂) = 0
    · rw [h1, zero_sub] at hrect
      have h2 := neg_ne_zero.mp hrect
      have ha1 := norm_le_of_profile hs₁ (left_ne_zero_of_mul h2)
      have ha2 := norm_le_of_profile hs₂ (right_ne_zero_of_mul h2)
      rw [le_div_iff₀ hY₁] at ha1
      rw [le_div_iff₀ hY₂] at ha2
      rw [hXY]
      nlinarith [mul_le_mul ha1 ha2 (by positivity) (by positivity)]
    · have ha1 := norm_le_of_profile hs₁ (left_ne_zero_of_mul h1)
      have ha2 := norm_le_of_profile hs₂ (right_ne_zero_of_mul h1)
      rw [le_div_iff₀ hX₁] at ha1
      rw [le_div_iff₀ hX₂] at ha2
      nlinarith [mul_le_mul ha1 ha2 (by positivity) (by positivity)]
  have hsplit : (Ideal.absNorm (finiteTupleProduct v) : ℝ) =
      (∏ i, (Ideal.absNorm (v (Sum.inl i)) : ℝ)) * (Ideal.absNorm (v (Sum.inr 0)) : ℝ) *
        (Ideal.absNorm (v (Sum.inr 1)) : ℝ) := by
    unfold finiteTupleProduct
    rw [map_prod, Nat.cast_prod, Fintype.prod_sum_type, Fin.prod_univ_two]
    ring
  rw [map_mul, map_mul, Nat.cast_mul, Nat.cast_mul] at hord
  have hP0 : 0 ≤ ∏ i, P i := Finset.prod_nonneg fun i _ => (hP i).le
  have hslots : ∏ i, P i ≤ ∏ i, (Ideal.absNorm (v (Sum.inl i)) : ℝ) :=
    Finset.prod_le_prod₀ (fun i _ => (hP i).le) (fun i _ => hslot i)
  rw [hsplit]
  have h3 : 0 ≤ a^2 * (X₁ * X₂) := by positivity
  calc a^2 * (X₁ * X₂) * ∏ i, P i ≤ ((B₁.absNorm : ℝ) * (v (Sum.inr 0)).absNorm *
        ((B₂.absNorm : ℝ) * (v (Sum.inr 1)).absNorm)) * ∏ i, (Ideal.absNorm (v (Sum.inl i)) : ℝ) :=
        mul_le_mul hord hslots hP0 (by positivity)
    _ = _ := by ring

/-- **The column-norm lower bound of an FP source.** -/
theorem column_lower {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0 < a)
    (I : Id) (h : sourceCoefficient s ha 1 I ≠ 0) :
    a^2 * (s.X₁ * s.X₂) * ∏ i, s.P i ≤
      (s.d.1.absNorm : ℝ) * (s.d.2.absNorm : ℝ) * (Ideal.absNorm I : ℝ) := by
  unfold sourceCoefficient originalColumn finiteColumnCoefficient at h
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hvI := (Finset.mem_filter.mp hv).2
  rw [← hvI]
  have hpc := right_ne_zero_of_mul hne
  have hs' : ∀ (W : 𝓢(ℝ,ℂ)) (hsW : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (t : ℝ),
      Function.support (CenteredMomentLattice.normPowerProfile W a b ha hsW (W.smooth ⊤) t :
        ℝ → ℂ) ⊆ Set.Icc a b := by
    intro W hsW t x hx
    apply hsW
    intro h0
    apply hx
    rw [CenteredMomentLattice.normPowerProfile_apply, h0, mul_zero]
  have hL := s.hL
  exact tuple_lower s.R s.ν s.Wslot s.P (fun i => lt_of_lt_of_le one_pos (s.hP i)) s.hW _ _ a b ha
    (hs' s.W₁ s.hs₁ s.t₁) (hs' s.W₂ s.hs₂ s.t₂) s.X₁ s.X₂ s.Y₁ s.Y₂ (hL.trans_le s.hX₁)
    (hL.trans_le s.hX₂) (hL.trans_le s.hY₁) (hL.trans_le s.hY₂) (s.hpX.trans s.hpY.symm)
    s.d.1 s.d.2 1 v hpc

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- **`hcol` on a canonical source**, with `clow = a²`. -/
theorem hcol_of_canonical (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (hX₁ : rs.X₁ = s.X₁) (hX₂ : rs.X₂ = s.X₂) (hP : ∀ i, s.P i = Z^(rs.w i)) :
    ∀ I, sourceCoefficient s ha 1 I ≠ 0 →
      θ.a^2 * rs.vol ≤ ((s.d.1.absNorm : ℝ) * (s.d.2.absNorm : ℝ)) * (Ideal.absNorm I : ℝ) := by
  intro I hI
  have h := column_lower s ha I hI
  have hd1 : 0 < (s.d.1.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hd.1)
  have hd2 : 0 < (s.d.2.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hd.2)
  have hvol : rs.vol = s.X₁ * s.X₂ * ∏ i, s.P i := by
    unfold GSrc.vol; rw [hX₁, hX₂]; simp only [hP]
  rw [hvol]
  linarith

/-! ### (9) The twist determines the label data -/

/-- The ideal of the second twist. -/
def twistIdeal (C D : Id) (U : Finset (CommonIndex C D)) : Id :=
  (∏ P : CommonIndex C D, P.val ^ min (leftExponent C D P) (rightExponent C D P)) *
    ∏ P ∈ nonunitPartitionSet C D U, P.val

theorem lA_eq_primary (C D : Id) (U : Finset (CommonIndex C D)) :
    Packet.secondTwist C D U = primaryGenerator (twistIdeal C D U) := by
  unfold Packet.secondTwist twistIdeal
  rw [primaryGenerator_mul]
  have h1 : commonFrequencyGenerator C D =
      primaryGenerator (∏ P : CommonIndex C D, P.val ^ min (leftExponent C D P) (rightExponent C D P)) := by
    unfold commonFrequencyGenerator
    change _ = primaryGeneratorHom _
    rw [map_prod]
    apply Finset.prod_congr rfl; intro P _
    rw [map_pow]; rfl
  have h2 : nonunitFrequencyGenerator C D U =
      primaryGenerator (∏ P ∈ nonunitPartitionSet C D U, P.val) := by
    unfold nonunitFrequencyGenerator
    change _ = primaryGeneratorHom _
    rw [map_prod]
    rfl
  rw [h1, h2]

theorem span_lA (S : Finset Id) (l : Lab S) :
    Ideal.span {lA S l} = twistIdeal l.1.val.1 l.1.val.2 l.2 := by
  have hne := lA_ne S l
  unfold lA at hne ⊢
  rw [lA_eq_primary] at hne ⊢
  exact (primaryGenerator_spec _ hne).1

/-- **Field `hspanInj`.** -/
theorem spanInj_holds (S : Finset Id) (l l' : Lab S)
    (h : Ideal.span {lA S l} = Ideal.span {lA S l'}) : lA S l = lA S l' := by
  rw [span_lA, span_lA] at h
  unfold lA
  rw [lA_eq_primary, lA_eq_primary, h]

/-! ### (9') Multiplicities -/

theorem card_Lab_fiber_le (S : Finset Id) (G : Id) (hG : G ≠ ⊥)
    (sel : Lab S → Id)
    (hcol : ∀ l : Lab S, sel l = G →
      l.1.val.1 ∣ G^2 ∧ l.1.val.2 ∣ G^2 ∧
        (Fintype.card (CommonIndex l.1.val.1 l.1.val.2) ≤ (IdealMobiusDivisorSum.primeSupport G).card)) :
    ((Finset.univ : Finset (Lab S)).filter (fun l => sel l = G)).card ≤
      (IdealMobiusDivisorSum.idealDivisors (G^2)).card^2 * 2^(IdealMobiusDivisorSum.primeSupport G).card := by
  have hG2 : G^2 ≠ ⊥ := pow_ne_zero 2 hG
  set T := (Finset.univ : Finset (Lab S)).filter (fun l => sel l = G)
  set P := IdealMobiusDivisorSum.idealDivisors (G^2) ×ˢ IdealMobiusDivisorSum.idealDivisors (G^2)
  -- fibres over the pair `(C₂, D₂)`
  have hmaps : ∀ l ∈ T, (l.1.val.1, l.1.val.2) ∈ P := by
    intro l hl
    obtain ⟨h1, h2, -⟩ := hcol l (Finset.mem_filter.mp hl).2
    exact Finset.mem_product.mpr ⟨(IdealMobiusDivisorSum.mem_idealDivisors hG2).mpr h1,
      (IdealMobiusDivisorSum.mem_idealDivisors hG2).mpr h2⟩
  have hfib : ∀ q ∈ P, (T.filter (fun l => (l.1.val.1, l.1.val.2) = q)).card ≤
      2^(IdealMobiusDivisorSum.primeSupport G).card := by
    intro q _
    by_cases hq : ∃ l ∈ T, (l.1.val.1, l.1.val.2) = q
    · obtain ⟨l₀, hl₀, hq₀⟩ := hq
      -- all labels in the fibre share the same `p` (`p = q`), so they are determined by `U`
      have hsub : T.filter (fun l => (l.1.val.1, l.1.val.2) = q) ⊆
          (Finset.univ : Finset (Finset (CommonIndex l₀.1.val.1 l₀.1.val.2))).image
            (fun U => (⟨l₀.1, U⟩ : Lab S)) := by
        intro l hl
        obtain ⟨-, hlq⟩ := Finset.mem_filter.mp hl
        have hp : l.1 = l₀.1 := by
          apply Subtype.ext
          rw [← hq₀] at hlq
          exact Prod.ext (congrArg Prod.fst hlq) (congrArg Prod.snd hlq)
        rw [Finset.mem_image]
        obtain ⟨p, U⟩ := l
        simp only at hp
        subst hp
        exact ⟨U, Finset.mem_univ _, rfl⟩
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
      rw [Finset.card_univ, Fintype.card_finset]
      exact Nat.pow_le_pow_right (by norm_num) (hcol l₀ (Finset.mem_filter.mp hl₀).2).2.2
    · push_neg at hq
      rw [Finset.card_eq_zero.mpr]
      · exact Nat.zero_le _
      · apply Finset.filter_eq_empty_iff.mpr
        intro l hl hlq
        exact hq l hl hlq
  calc T.card = ∑ q ∈ P, (T.filter (fun l => (l.1.val.1, l.1.val.2) = q)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _q ∈ P, 2^(IdealMobiusDivisorSum.primeSupport G).card := Finset.sum_le_sum hfib
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, Finset.card_product]; ring

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
