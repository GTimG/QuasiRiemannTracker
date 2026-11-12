/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.PairPoisson
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.GaussRoot

/-!
# Inverse.Poisson.Grouping — the exact physical-row identity

For one label `f` the smoothed Gauss-row energy of the canonical row equals, EXACTLY,

`∑'_k W(‖k‖²/Y) |∑_U c_U χ_U(k)|² = ∑_{g ⊆ pool} ∑_{a, b ⊆ pool \ g, a ∩ b = ∅} groupedTerm g a b`,

`groupedTerm g a b = (Y/√(Na Nb)) ∑_{E ⊆ g} μ(E)/N e ∑'_h Ŵ(Y Nh/(N e Na Nb))
    · |c_g|² · quadraticCrossPhase(a,b) · χ_a(-1) · conj P_a(y) · P_b(y)`,
`y = f² · (e g') · g' · h`, `e g' = ∏_g p` (`g' = cofactor g E`),

with `P_A(y) = μ(A) G(A) Ψ(A) mask_A(m) conj χ_A(y) H(g ∪ A)` (`physCoeff`). The diagonal
`U₁ = U₂` is the term `a = b = ∅`. This combines the second Poisson summation (`PairPoisson`),
the phase identity (`Phase`) and the Gauss-root identification (`GaussRoot`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

local notation "O" => ActualEisensteinCubic.O

/-! ## Reindexing the column pairs by their common part -/

section Reindex
variable {α : Type*} [DecidableEq α]

theorem pair_fibre (R g : Finset α) (hg : g ⊆ R) (F : Finset α → Finset α → ℂ) :
    ∑ x ∈ (R.powerset ×ˢ R.powerset).filter (fun x => x.1 ∩ x.2 = g), F x.1 x.2 =
      ∑ a ∈ (R \ g).powerset, ∑ b ∈ (R \ g).powerset,
        if Disjoint a b then F (g ∪ a) (g ∪ b) else 0 := by
  rw [← Finset.sum_product' (f := fun a b => if Disjoint a b then F (g ∪ a) (g ∪ b) else 0),
    ← Finset.sum_filter]
  refine Finset.sum_bij' (fun x _ => (x.1 \ x.2, x.2 \ x.1)) (fun y _ => (g ∪ y.1, g ∪ y.2))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    refine ⟨⟨?_, ?_⟩, disjoint_sdiff_sdiff⟩
    · intro i hi
      simp only [Finset.mem_sdiff] at hi ⊢
      refine ⟨h1 hi.1, fun hig => hi.2 ?_⟩
      rw [← h3] at hig
      exact (Finset.mem_inter.mp hig).2
    · intro i hi
      simp only [Finset.mem_sdiff] at hi ⊢
      refine ⟨h2 hi.1, fun hig => hi.2 ?_⟩
      rw [← h3] at hig
      exact (Finset.mem_inter.mp hig).1
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hy ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    refine ⟨⟨Finset.union_subset hg (h1.trans Finset.sdiff_subset),
      Finset.union_subset hg (h2.trans Finset.sdiff_subset)⟩, ?_⟩
    ext i
    have ha : i ∈ y.1 → i ∉ g := fun h => (Finset.mem_sdiff.mp (h1 h)).2
    have hb : i ∈ y.2 → i ∉ g := fun h => (Finset.mem_sdiff.mp (h2 h)).2
    have hab : i ∈ y.1 → i ∉ y.2 := fun h => Finset.disjoint_left.mp h3 h
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  · intro x hx
    simp only [Finset.mem_filter] at hx
    ext i
    · simp only [Finset.mem_union, Finset.mem_sdiff, ← hx.2, Finset.mem_inter]
      tauto
    · simp only [Finset.mem_union, Finset.mem_sdiff, ← hx.2, Finset.mem_inter]
      tauto
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    ext i
    · have ha : i ∈ y.1 → i ∉ g := fun h => (Finset.mem_sdiff.mp (h1 h)).2
      have hb : i ∈ y.2 → i ∉ g := fun h => (Finset.mem_sdiff.mp (h2 h)).2
      have hab : i ∈ y.1 → i ∉ y.2 := fun h => Finset.disjoint_left.mp h3 h
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    · have ha : i ∈ y.1 → i ∉ g := fun h => (Finset.mem_sdiff.mp (h1 h)).2
      have hb : i ∈ y.2 → i ∉ g := fun h => (Finset.mem_sdiff.mp (h2 h)).2
      have hab : i ∈ y.1 → i ∉ y.2 := fun h => Finset.disjoint_left.mp h3 h
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
  · intro x hx
    simp only [Finset.mem_filter] at hx
    have hd : Disjoint (x.1 \ x.2) (x.2 \ x.1) := disjoint_sdiff_sdiff
    have e1 : g ∪ x.1 \ x.2 = x.1 := by
      ext i; simp only [Finset.mem_union, Finset.mem_sdiff, ← hx.2, Finset.mem_inter]; tauto
    have e2 : g ∪ x.2 \ x.1 = x.2 := by
      ext i; simp only [Finset.mem_union, Finset.mem_sdiff, ← hx.2, Finset.mem_inter]; tauto
    simp only [e1, e2]

/-- Every pair of columns is `(g ∪ a, g ∪ b)` with `g` the common part and `a, b` disjoint. -/
theorem pair_common_reindex (R : Finset α) (F : Finset α → Finset α → ℂ) :
    ∑ U₁ ∈ R.powerset, ∑ U₂ ∈ R.powerset, F U₁ U₂ =
      ∑ g ∈ R.powerset, ∑ a ∈ (R \ g).powerset, ∑ b ∈ (R \ g).powerset,
        if Disjoint a b then F (g ∪ a) (g ∪ b) else 0 := by
  rw [← Finset.sum_product' (f := F)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : Finset α × Finset α => x.1 ∩ x.2)
    (t := R.powerset)]
  · apply Finset.sum_congr rfl
    intro g hg
    exact pair_fibre R g (Finset.mem_powerset.mp hg) F
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx ⊢
    exact Finset.inter_subset_left.trans hx.1

end Reindex

/-! ## The common column cofactor `g' = ∏_g p / e` -/

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem generator_dvd_prod (g E : Finset ι) (hE : E ⊆ g) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) E ∣ ∏ k ∈ g, p k := by
  have hspan : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      Ideal.span {∏ k ∈ E, p k} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
      Ideal.prod_span_singleton]
  have h1 : primeSubsetGenerator (fun i => Ideal.span {p i}) E ∣ ∏ k ∈ E, p k :=
    Ideal.span_singleton_le_span_singleton.mp (le_of_eq hspan.symm)
  exact h1.trans (Finset.prod_dvd_prod_of_subset E g p hE)

/-- The cofactor `g' = (∏_g p) / e` (`= g/d`). -/
def cofactor (g E : Finset ι) : O :=
  if h : primeSubsetGenerator (fun i => Ideal.span {p i}) E ∣ ∏ k ∈ g, p k then
    Classical.choose h else 0

theorem cofactor_spec (g E : Finset ι) (hE : E ⊆ g) :
    ∏ k ∈ g, p k = primeSubsetGenerator (fun i => Ideal.span {p i}) E * cofactor p g E := by
  have h := generator_dvd_prod p g E hE
  rw [cofactor, dite_cond_eq_true (eq_true h)]
  exact Classical.choose_spec h

/-! ## The grouped physical-row identity -/

/-- The grouped term of the common column `g` and the disjoint residual columns `a, b`. -/
def groupedTerm (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (g a b : Finset ι) : ℂ :=
  let n := ∏ i ∈ activeSupport a b, p i
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ g.powerset,
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' k : O, paperRadialFourier W
          (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
          (star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
            canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g *
            quadraticCrossPhase p hg a b *
            finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1) *
            star (physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A))
              (f ^ 2 * (e * cofactor p g E) * cofactor p g E * k) a) *
            physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A))
              (f ^ 2 * (e * cofactor p g E) * cofactor p g E * k) b)

theorem assoc_helper {β : Type*} (x A : ℂ) (s : Finset β) (M : β → ℂ) (K T G : β → O → ℂ)
    (hT : ∀ E ∈ s, ∀ h, x * T E h = G E h) :
    x * (A * ∑ E ∈ s, M E * ∑' h : O, K E h * T E h) =
      A * ∑ E ∈ s, M E * ∑' h : O, K E h * G E h := by
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro h
  rw [mul_left_comm, hT E hE h]

variable (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)

include hc hpr in
theorem pair_term_eq (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (g a b : Finset ι) (hga : Disjoint a g) (hgb : Disjoint b g) (hab : Disjoint a b) :
    star (canonCoeff p hp hcop hg Ψ m f H (g ∪ a)) * canonCoeff p hp hcop hg Ψ m f H (g ∪ b) *
        pairDual p hp hinj hg W Y (g ∪ a) (g ∪ b) =
      groupedTerm p hp hcop hg Ψ m f H W Y g a b := by
  have hI : (g ∪ a) ∩ (g ∪ b) = g := by
    ext i
    have h1 : i ∈ a → i ∉ g := fun h => Finset.disjoint_left.mp hga h
    have h2 : i ∈ b → i ∉ g := fun h => Finset.disjoint_left.mp hgb h
    have h3 : i ∈ a → i ∉ b := fun h => Finset.disjoint_left.mp hab h
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hA : (g ∪ a) \ (g ∪ b) = a := by
    ext i
    have h1 : i ∈ a → i ∉ g := fun h => Finset.disjoint_left.mp hga h
    have h3 : i ∈ a → i ∉ b := fun h => Finset.disjoint_left.mp hab h
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hB : (g ∪ b) \ (g ∪ a) = b := by
    ext i
    have h2 : i ∈ b → i ∉ g := fun h => Finset.disjoint_left.mp hgb h
    have h3 : i ∈ a → i ∉ b := fun h => Finset.disjoint_left.mp hab h
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  unfold pairDual groupedTerm
  dsimp only
  simp only [Finset.prod_coe_sort, hI, hA, hB]
  refine assoc_helper
    (star (canonCoeff p hp hcop hg Ψ m f H (g ∪ a)) * canonCoeff p hp hcop hg Ψ m f H (g ∪ b))
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ : ℂ)) g.powerset
    (fun E => (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      ((‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ) : ℂ))
    (fun E k => paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ ^ 2)))
    (fun E k => activeGaussRowFactor p hp hinj hg a b
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k) _ ?_
  intro E hE h
  exact pair_gauss_identity p hp hcop hg hc hpr hinj Ψ m f H g a b hga hgb hab
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (cofactor p g E) h
    (cofactor_spec p g E (Finset.mem_powerset.mp hE))

include hinj hc hpr in
/-- The exact physical-row identity for one label `f`. -/
theorem grouped_identity (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' k : O, W (‖eisEmbedding k‖ ^ 2 / Y) *
      (↑(‖∑ U ∈ pool.powerset, canonCoeff p hp hcop hg Ψ m f H U *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U k‖ ^ 2) : ℂ)) =
      ∑ g ∈ pool.powerset, ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
        if Disjoint a b then groupedTerm p hp hcop hg Ψ m f H W Y g a b else 0 := by
  rw [smoothed_column_poisson p hp hinj hg hc pool _ W Y hY, pair_common_reindex]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : Disjoint a b
  · rw [if_pos hab, if_pos hab]
    have hga : Disjoint a g := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp ha)
      Finset.sdiff_disjoint
    have hgb : Disjoint b g := Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hb)
      Finset.sdiff_disjoint
    exact pair_term_eq p hp hinj hcop hg hc hpr Ψ m f H W Y g a b hga hgb hab
  · rw [if_neg hab, if_neg hab]

end
end Qrh.MarkedAnchor.Inverse.Poisson
