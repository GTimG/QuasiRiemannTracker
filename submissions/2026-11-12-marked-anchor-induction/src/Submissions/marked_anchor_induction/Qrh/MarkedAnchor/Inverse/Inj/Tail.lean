/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/{InitialHighFrequencyTailWeights,
InitialHighFrequencyTailCoefficient,InitialHighFrequencyTailFiber,InitialHighFrequencyTail,
InitialHighFrequencyTailRapid,InitialDyadicTailBound}.lean` (Apache-2.0). Modified by Sil
(2026-11-12): the mark `primeMark slots lists a` on pairwise disjoint lists is replaced by an
arbitrary mark `M` with `‖M S‖ ≤ 2^|S|` (the only property used, via
`primeMark_norm_le_divisor_count`); the injective mark is reduced to it by the coloring bound
`‖primeMarkInj‖ ≤ |slots|^|slots| 2^|S|` and the degree-2 homogeneity of the physical block.
Proofs otherwise unchanged. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Oracle
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailBound

/-!
# Inverse.Inj.Tail — the high-frequency tail of the physical block for the injective mark

* `primeMarkInj_norm_le_two_pow` — `‖primeMarkInj S L a U‖ ≤ |S|^|S| · 2^|U|` (coloring);
* `physicalTerm_smul`, `physicalBlock_smul` — the physical block is homogeneous of degree 2 in
  real rescalings of the mark;
* `actual_high_mass_tail_gen` — baseline `actual_high_mass_tail` for any mark with
  `‖M S‖ ≤ 2^|S|`;
* **`actual_high_mass_tail_inj`** — the same for `primeMarkInj` (lists may overlap), constant
  `× (K^K)^2`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialDyadicAssembly InverseInitialProfile
open InverseInitialRetainedSupport InverseInitialHighFrequencyTail
open InverseInitialKernelBridge InverseInitialEnergyCallerWeights FirstCauchyArithmetic
open InverseInitialDyadicTailBound
open Qrh.MarkedAnchor.Inverse
local notation "O" => ActualEisensteinCubic.O

/-! ## The injective mark is bounded by `2^|U|` up to `|S|^|S|` -/

theorem primeMarkInj_norm_le_two_pow {ι σ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ]
    (S : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (ha : ∀ i ∈ S, ∀ x ∈ L i, ‖a i x‖ ≤ 1)
    (U : Finset ι) :
    ‖primeMarkInj S L a U‖ ≤ ((S.card ^ S.card : ℕ) : ℝ) * 2^U.card := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    rw [primeMarkInj_empty]
    simp only [norm_one, Finset.card_empty, pow_zero, Nat.cast_one, one_mul]
    exact one_le_pow₀ (by norm_num)
  have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨⟨_, hS.choose_spec⟩⟩
  set n : ℕ := Fintype.card S with hn
  set c : ℕ := n ^ (Fintype.card ι - n) with hc
  set N : ℕ := Fintype.card (ι → S) with hN
  have hcpos : 0 < c := Nat.pow_pos hpos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hNc : (N : ℝ) ≤ (n ^ n : ℕ) * c := by
    have : N ≤ n ^ n * c := by
      rw [hN, Fintype.card_fun, hc, ← pow_add, ← hn]
      exact Nat.pow_le_pow_right hpos (by omega)
    exact_mod_cast this
  have hcard : S.card = n := by rw [hn, Fintype.card_coe]
  have he := coloring_mark S L a U
  have hcol (col : ι → S) : ‖primeMark S (coloredLists S L col) a U‖ ≤ (2:ℝ)^U.card :=
    primeMark_norm_le_divisor_count S (coloredLists S L col) a U (colored_disjoint S L col)
      (fun i hi x hx => ha i hi x (coloredLists_subset S L col i hx))
  have hsum : ‖∑ col : ι → S, primeMark S (coloredLists S L col) a U‖ ≤ (N : ℝ) * 2^U.card := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun col _ => hcol col)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  rw [he, norm_mul, Complex.norm_natCast] at hsum
  rw [hcard]
  have h2 : (0:ℝ) ≤ 2^U.card := by positivity
  have hmain : (c : ℝ) * ‖primeMarkInj S L a U‖ ≤ (c : ℝ) * (((n ^ n : ℕ) : ℝ) * 2^U.card) := by
    refine hsum.trans ?_
    calc (N : ℝ) * 2^U.card ≤ ((n ^ n : ℕ) * c : ℝ) * 2^U.card :=
          mul_le_mul_of_nonneg_right hNc h2
      _ = _ := by ring
  exact le_of_mul_le_mul_left hmain hcR

/-! ## Degree-2 homogeneity of the physical block in the mark -/

section Homog
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem physicalTerm_smul (Ψ : O →* ℂ) (j : O) (c : ℝ) (M : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (x : Point ι) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j (fun S => (c : ℂ) * M S) W₁ W₂ Φ Z D m x ρ =
      ((c^2 : ℝ) : ℂ) * physicalTerm p hp hcop hg Ψ j M W₁ W₂ Φ Z D m x ρ := by
  unfold physicalTerm initialColumn
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem physicalBlock_smul (source : Finset (Point ι)) (w : Point ι → ℂ) (Ψ : O →* ℂ) (j : O)
    (c : ℝ) (M : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalBlock p hp hcop hg source w Ψ j (fun S => (c : ℂ) * M S) W₁ W₂ Φ Z D m =
      ((c^2 : ℝ) : ℂ) * physicalBlock p hp hcop hg source w Ψ j M W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  simp only [physicalTerm_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

end Homog

/-! ## The tail chain for a mark with `‖M S‖ ≤ 2^|S|` -/

section Gen
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
theorem marked_support_norm_bound_gen
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (M : Finset ι → ℂ) (hM : ∀ S, ‖M S‖ ≤ (2:ℝ)^S.card)
    (S : Finset ι) (L : ℝ) (hL : 1≤L) (hS : primeProductNorm p S≤L) :
    ‖M S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (hM S).trans (by exact_mod_cast hc)

theorem originalCoefficient_marked_bound_gen
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (j : O)
    (M : Finset ι → ℂ) (hM : ∀ S, ‖M S‖ ≤ (2:ℝ)^S.card)
    (x : Point ι) (ρ : SecondRayIndex) (L : ℝ) (hL : 1≤L)
    (hleft : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.left≤L)
    (hright : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.right≤L) :
    ‖originalCoefficient p hp hcop hg Ψ j M x ρ‖≤
      ‖secondRayCoefficient ρ‖*(128*L)^2 := by
  have hmark (N : Finset ι)
      (hN : primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N≤L) :
      ‖M (x.common∪(x.overlap∪N))‖≤128*L := by
    apply marked_support_norm_bound_gen p hp hinj M hM _ L hL
    apply (primeProductNorm_union_le_mul p hp _ _).trans
    apply (mul_le_mul_of_nonneg_left (primeProductNorm_union_le_mul p hp _ _)
      (primeProductNorm_pos p hp _).le).trans
    simpa only [mul_assoc] using hN
  have hl := (initialColumn_mark_norm p hp hcop hg hc (secondRayMinus Ψ ρ)
    (fun n=>(secondRayMinus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>M (x.common∪A))
    (x.overlap∪x.left)).trans (hmark x.left hleft)
  have hr := (initialColumn_mark_norm p hp hcop hg hc (secondRayPlus Ψ ρ)
    (fun n=>(secondRayPlus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>M (x.common∪A))
    (x.overlap∪x.right)).trans (hmark x.right hright)
  have hb := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hm := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hv : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  simp only [originalCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*(128*L)*(128*L) := by gcongr
    _ = _ := by ring

end Gen

theorem original_frequency_fiber_tail_gen (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (M : Finset ι → ℂ), (∀ S, ‖M S‖ ≤ (2:ℝ)^S.card) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (k : Fin 5→Finset ι) (F : Finset O) (w : Point ι→ℂ) (ρ : SecondRayIndex),
    keyNorms p k 1≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L →
    (∀h∈F,Valid (sourcePoint k h)) → (∀h∈F,‖w (sourcePoint k h)‖≤Γ) →
    (∀h∈F,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
      keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2) →
    ‖∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      M W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2)*Z^(m-D)*B₁*B₂*
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail_uniform A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι _ p hp _ hcop hg hinj hc Ψ hΨ j M hM
    W₁ W₂ Φ Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k F w ρ hd hleft hright hvalid hw htail
  have hn (i : Fin 5) : 1≤keyNorms p k i := primeProductNorm_ge_one p hp _
  have he : (∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      M W₁ W₂ Φ Z D m (sourcePoint k h) ρ) =
      ∑h∈F,(w (sourcePoint k h)*originalCoefficient p hp hcop hg Ψ j
        M (sourcePoint k h) ρ)*
        physicalKernel W₁ W₂ Φ Z D m
        ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
          keyNorms p k 3,keyNorms p k 4] := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [physicalTerm_original_coefficient p hp hcop hg Ψ j _ W₁ W₂ Φ Z D m _ (hvalid h hh) ρ,
      coordinates_sourcePoint]
    ring
  rw [he]
  apply hbound W₁ W₂ Φ Z D m (keyNorms p k 0) (keyNorms p k 1)
    (keyNorms p k 2) (keyNorms p k 3) (keyNorms p k 4) L T
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2) B₁ B₂ hZ (hn 0) (hn 1) (hn 2)
    (hn 3) (hn 4) hL hd hleft hright hT (by positivity) hB₁ hB₂ (hW₁ _) (hW₂ _) F _ htail
  intro h hh
  rw [norm_mul]
  have hc := originalCoefficient_marked_bound_gen p hp hcop hg hinj hc Ψ hΨ j M hM
    (sourcePoint k h) ρ L hL hleft hright
  calc
    _ ≤ Γ*(‖secondRayCoefficient ρ‖*(128*L)^2) := by gcongr; exact hw h hh
    _ = _ := by ring

theorem original_physical_tail_gen (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (M : Finset ι → ℂ), (∀ S, ‖M S‖ ≤ (2:ℝ)^S.card) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,T≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j M W₁ W₂ Φ Z D m‖ ≤
      (128*L)^7*Γ*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)*Z^(m-D)*B₁*B₂*
        (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hfiber⟩ := original_frequency_fiber_tail_gen A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι _ p hp _ hcop hg hinj hc Ψ hΨ j M hM W₁ W₂ Φ
    Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ pool S w hvalid hw hpool hnorm hleft hright htail
  let R : ℝ := Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
    ((min 1 (Z^m/L^3))^2*(1+T)^A)
  have hR : 0≤R := by dsimp [R]; positivity
  let B : ℝ := Γ*(128*L)^2*R
  have hB : 0≤B := by dsimp [B]; positivity
  have hkey (k) (hk : k∈sourceKeys S) (ρ : SecondRayIndex) :
      ‖∑h∈sourceFrequencies S k,
        w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j M
          W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤ B*‖secondRayCoefficient ρ‖ := by
    obtain ⟨x,hx,hk'⟩ := Finset.mem_image.mp hk
    have hkN (i) : keyNorms p k i=primeProductNorm p (sourceKey x i) := by rw [←hk'];rfl
    have hf (h) (hh : h∈sourceFrequencies S k) := (mem_sourceFrequencies S k h).mp hh
    have hkl : keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L := by
      simpa [←hk',keyNorms,sourceKey] using hleft x hx
    have hkr : keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L := by
      simpa [←hk',keyNorms,sourceKey] using hright x hx
    have htailk : ∀h∈sourceFrequencies S k,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
        keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2 := by
      intro h hh
      simpa only [sourcePoint,keyNorms] using htail (sourcePoint k h) (hf h hh)
    have hb := hfiber p hp hcop hg hinj hc Ψ hΨ j M hM W₁ W₂ Φ
      Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k (sourceFrequencies S k) w ρ
      (by rw [hkN];exact hnorm x hx 1) hkl hkr
      (fun h hh=>hvalid (sourcePoint k h) (hf h hh))
      (fun h hh=>hw (sourcePoint k h) (hf h hh)) htailk
    apply hb.trans_eq
    dsimp [B,R]
    ring
  have hsum := original_source_norm_fibers S Finset.univ
    (fun x ρ=>w x*physicalTerm p hp hcop hg Ψ j M W₁ W₂ Φ Z D m x ρ)
    (fun ρ=>B*‖secondRayCoefficient ρ‖) (fun k hk ρ _=>hkey k hk ρ)
  change ‖∑x∈S,∑ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j
    M W₁ W₂ Φ Z D m x ρ‖≤_
  apply hsum.trans
  rw [←Finset.mul_sum]
  calc
    _ ≤ (128*L)^5*(B*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)) :=
      mul_le_mul_of_nonneg_right (sourceKeys_card p hp hinj pool S L hL hpool hnorm) (by positivity)
    _ = _ := by dsimp [B,R]; ring

theorem original_physical_tail_rapid_gen (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (M : Finset ι → ℂ), (∀ S, ‖M S‖ ≤ (2:ℝ)^S.card) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L Γ B₁ B₂ : ℝ),
    1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap → -m≤Lcap → m-D≤Lcap → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j M W₁ W₂ Φ Z D m‖ ≤
      C₀*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨A,hA⟩ := initial_tail_rapid_order Lcap saving τ hτ
  obtain ⟨s,C₀,hC₀,hraw⟩ := original_physical_tail_gen A
  let R : ℝ := ∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖
  have hR : 0≤R := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  refine ⟨s,128^7*(R+1)*C₀,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc Ψ hΨ j M hM W₁ W₂ Φ
    Z D m L Γ B₁ B₂ hZ hL hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool S w
    hvalid hw hpool hnorm hleft hright htail
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := hraw p hp hcop hg hinj hc Ψ hΨ j M hM W₁ W₂ Φ
    Z D m L (Z^τ) Γ B₁ B₂ hz hL (by positivity) hΓ hB₁ hB₂ hW₁ hW₂
    pool S w hvalid hw hpool hnorm hleft hright htail
  have hs : 0≤s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply hb.trans
  calc
    _ = ((128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A))*
        (Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by dsimp [R];ring
    _ ≤ (128^7*Z^(-saving))*(Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) :=
      mul_le_mul_of_nonneg_right (hA Z L m D hZ hL hcap hsize hm hmd) (by positivity)
    _ ≤ (128^7*Z^(-saving))*(Γ*(R+1)*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by
      gcongr
      linarith
    _ = _ := by ring

theorem actual_high_mass_tail_gen (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (M : Finset ι → ℂ), (∀ S, ‖M S‖ ≤ (2:ℝ)^S.card) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m η bW Γ B₁ B₂ : ℝ),
    1<Z → 0≤η → 0<bW → 64*bW^2≤Z^η →
    0≤Lcap → bW*Z^D≤Z^Lcap → -m≤Lcap → m-D≤Lcap →
    0≤Γ → 0≤B₁ → 0≤B₂ → (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    Function.support W₁⊆Set.Iic bW → Function.support W₂⊆Set.Iic bW →
    ∀ (pool : Finset ι) (S : Finset (Source (ι:=ι) 0)) (w : Source (ι:=ι) 0→ℂ),
    (∀x∈S,x.common⊆pool) → (∀x∈S,x.overlap⊆pool) →
    (∀x∈S,x.divisor⊆x.common) → (∀x∈S,x.frequency≠0) → (∀x∈S,‖w x‖≤Γ) →
    ∀ (a b : Fin 4→ℝ), (∀i,0<a i) → (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) →
    ‖physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j M W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨s,C,hC,hrapid⟩ := original_physical_tail_rapid_gen Lcap saving τ hτ
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr Ψ hΨ j M hM W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  let wt : Point ι→ℂ := ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ))
    (sourceNorms p x):ℂ))∘erasePoint)
  let live (x : Point ι) : Prop := ∃ρ : SecondRayIndex,
    wt x*physicalTerm p hp hcop hg Ψ j M W₁ W₂ Φ Z D m x ρ≠0
  let F := (pointSource pool S).filter live
  have hmem (x) (hx : x∈F) : x∈pointSource pool S := (Finset.mem_filter.mp hx).1
  have hvalid (x) (hx : x∈F) : Valid x := pointSource_valid pool S hdiv hfreq x (hmem x hx)
  have hold (x) (hx : x∈F) : erasePoint x∈S := pointSource_erase_mem pool S x (hmem x hx)
  have hgeometry (x) (hx : x∈F) :
      (coordinates p x 0≤bW*Z^D ∧ coordinates p x 1≤bW*Z^D ∧
       coordinates p x 2≤bW*Z^D ∧ coordinates p x 4≤bW*Z^D ∧ coordinates p x 5≤bW*Z^D) ∧
      (coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D ∧
       coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D) ∧
      windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0 := by
    obtain ⟨ρ,hρ⟩ := (Finset.mem_filter.mp hx).2
    have hpterm := (mul_ne_zero_iff.mp hρ).2
    refine ⟨live_ideal_caps p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,
      live_whole_columns p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,?_⟩
    intro hz
    apply (mul_ne_zero_iff.mp hρ).1
    simp only [wt,Function.comp_apply,hz,Complex.ofReal_zero,mul_zero]
  have hn (x : Point ι) (i : Fin 5) := sourceKey_norm_coordinate p x i
  have hwhole (x) (hx : x∈F) :
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤bW*Z^D ∧
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤bW*Z^D := by
    have he := (hgeometry x hx).2.1
    have hn0 := hn x 0
    have hn2 := hn x 2
    have hn3 := hn x 3
    have hn4 := hn x 4
    simp [sourceKey,idealIndex] at hn0 hn2 hn3 hn4
    rw [←hn0,←hn2,←hn3,←hn4] at he
    exact he
  have hfilter := physicalBlock_filter_of_live p hp hcop hg (pointSource pool S) live wt Ψ j
    M W₁ W₂ Φ Z D m (fun x hx ρ hn=>⟨ρ,hn⟩)
  change ‖physicalBlock p hp hcop hg (pointSource pool S) wt Ψ j _ W₁ W₂ Φ Z D m‖≤_
  rw [hfilter]
  have hr := hrapid p hp hcop hg hinj hc Ψ hΨ j M hM W₁ W₂ Φ
    Z D m (max 1 (bW*Z^D)) Γ B₁ B₂ hZ.le (le_max_left _ _) hcap
    (max_le (Real.one_le_rpow hZ.le hcap) hsize) hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool F wt hvalid
  suffices hbound : ‖physicalBlock p hp hcop hg F wt Ψ j M W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) by
    have hset : @Finset.filter (Point ι) live (fun x=>Classical.propDecidable (live x))
        (pointSource pool S)=F := by
      ext x
      simp only [Finset.mem_filter,F]
    rw [hset]
    exact hbound
  refine hr ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (mass_weight_bound p a b _ ha w (erasePoint x) (hrange _ (hold x hx))).trans (hw _ (hold x hx))
  · intro x hx
    exact pointSource_supports pool S hcommon hoverlap hdiv x (hmem x hx)
  · intro x hx i
    rw [sourceKey_norm_coordinate]
    have he := (hgeometry x hx).1
    apply le_trans _ (le_max_right 1 (bW*Z^D))
    fin_cases i
    · exact he.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2
  · intro x hx
    exact (hwhole x hx).1.trans (le_max_right _ _)
  · intro x hx
    exact (hwhole x hx).2.trans (le_max_right _ _)
  · intro x hx
    exact live_mass_radial_gate p hp a b Z D m η τ bW hZ hη hbW hfixed x
      (hvalid x hx) (hgeometry x hx).2.1.1 (hgeometry x hx).2.1.2 (hgeometry x hx).2.2

/-- **The high-mass tail for the injective mark** (lists may overlap): the baseline
`actual_high_mass_tail` with the constant multiplied by `(K^K)^2`. -/
theorem actual_high_mass_tail_inj (Lcap saving τ : ℝ) (hτ : 0<τ) (K : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (weights : σ→ι→ℂ),
    slots.card ≤ K → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m η bW Γ B₁ B₂ : ℝ),
    1<Z → 0≤η → 0<bW → 64*bW^2≤Z^η →
    0≤Lcap → bW*Z^D≤Z^Lcap → -m≤Lcap → m-D≤Lcap →
    0≤Γ → 0≤B₁ → 0≤B₂ → (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    Function.support W₁⊆Set.Iic bW → Function.support W₂⊆Set.Iic bW →
    ∀ (pool : Finset ι) (S : Finset (Source (ι:=ι) 0)) (w : Source (ι:=ι) 0→ℂ),
    (∀x∈S,x.common⊆pool) → (∀x∈S,x.overlap⊆pool) →
    (∀x∈S,x.divisor⊆x.common) → (∀x∈S,x.frequency≠0) → (∀x∈S,‖w x‖≤Γ) →
    ∀ (a b : Fin 4→ℝ), (∀i,0<a i) → (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) →
    ‖physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j (primeMarkInj slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨s,C,hC,hgen⟩ := actual_high_mass_tail_gen Lcap saving τ hτ
  have hKK : (0:ℝ) < ((K ^ K : ℕ) : ℝ) := by exact_mod_cast natPow_self_pos K
  refine ⟨s,((K ^ K : ℕ) : ℝ)^2*C,by positivity,?_⟩
  intro ι σ _ _ _ p hp _ hcop hg hinj hc hpr Ψ hΨ j slots lists weights hK hwgt W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  set A : ℝ := ((K ^ K : ℕ) : ℝ) with hA
  have hA0 : A ≠ 0 := hKK.ne'
  have hle : ((slots.card ^ slots.card : ℕ) : ℝ) ≤ A := by
    rw [hA]
    exact_mod_cast natPow_self_le hK
  let M : Finset ι → ℂ := fun U => ((A⁻¹ : ℝ) : ℂ) * primeMarkInj slots lists weights U
  have hM : ∀ U, ‖M U‖ ≤ (2:ℝ)^U.card := by
    intro U
    have h := primeMarkInj_norm_le_two_pow slots lists weights hwgt U
    simp only [M, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hKK]
    rw [inv_mul_le_iff₀ hKK]
    exact h.trans (mul_le_mul_of_nonneg_right hle (by positivity))
  have hmark : primeMarkInj slots lists weights = fun U => ((A : ℝ) : ℂ) * M U := by
    funext U
    simp only [M, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hA0, Complex.ofReal_one,
      one_mul]
  rw [hmark, physicalBlock_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg A)]
  have hb := hgen p hp hcop hg hinj hc hpr Ψ hΨ j M hM W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  calc A^2 * ‖_‖ ≤ A^2 * (C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg A)
    _ = _ := by ring

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.actual_high_mass_tail_inj
