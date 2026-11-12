/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Descent/Canonical.lean`,
`Inversion/InitialArithmetic.lean`, `Inversion/InitialEnergyCaller{Family,Modes,Source,Sector}.lean`
(Apache-2.0). Modified by Sil (2026-11-12): the full prime mark `primeMark` is replaced by the
injective mark `primeMarkInj` (priority and residual laws from `Inj.Mark`); proofs otherwise
unchanged. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Oracle
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSector

/-!
# Inverse.Inj.Column — the column calculus of the caller chain with the injective mark

`physicalBlock` is generic in the mark; its rectangular expansion
(`physicalBlock_rectangular_common_measure_inj`) splits the injective mark of `common ∪ overlap ∪ N`
by the priority law into `primeMarkInj J (common ∪ overlap) · finiteCanonicalMarkedRowInj (slots\J)`
(`markedModeColumnInj`, `rowModeInj`), exactly as the baseline does for `primeMark`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open OAI OAI.SevenEighths OAI.JointLogSeparation
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge InverseInitialEnergyCallerFamily InverseInitialEnergyCallerModes
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerOpposite
open Qrh.MarkedAnchor.Inverse
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-! ## Descent/Canonical -/

theorem secondChildSum_marked_canonical_inj
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMarkInj slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMarkInj J lists a (A ∪ V) *
      finiteCanonicalMarkedRowInj p hp hcop hg (F \ V) Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ (A ∪ V)) a W (X / primeProductNorm p V) := by
  unfold secondChildSum finiteCanonicalMarkedRowInj fixedChildRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  have hd : Disjoint V N := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hn)).2 hi)
  have hn : primeProductNorm p (V ∪ N) / X = primeProductNorm p N / (X / primeProductNorm p V) := by
    rw [primeProductNorm_union p V N hd]
    simp only [div_div_eq_mul_div]
    ring
  have hmark := primeMarkInj_priority' slots lists a (A ∪ V) N
  simp only [primeMarkInj_residual_lists] at hmark
  simp only [secondChildColumn, ← Finset.union_assoc, hn]
  rw [hmark]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRowInj_restore_pool
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRowInj p hp hcop hg (pool \ B) Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a W X :=
  fixedChildRow_restore_killed_pool p hp hcop hg pool B Ψ m f k _ hB

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRowInj_restore_lists
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots (fun i => lists i \ B) a W X =
      finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRowInj fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hd : Disjoint B U
  · have he : U \ B = U := Finset.sdiff_eq_self_of_disjoint hd.symm
    simp only [secondChildColumn, ← primeMarkInj_residual_lists, he]
  · obtain ⟨i, hiB, hiU⟩ := Finset.not_disjoint_iff.mp hd
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB),
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB)]

theorem secondChildSum_marked_fixed_pool_inj
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMarkInj slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMarkInj J lists a (A ∪ V) *
      finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V) := by
  rw [secondChildSum_marked_canonical_inj]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  have hV (i : ι) (hi : i ∈ V) : (m * r) * (c * e * ∏ j ∈ V, p j) ∈ Ideal.span {p i} :=
    Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hi) (c * e)) (m * r))
  rw [finiteCanonicalMarkedRowInj_restore_pool p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV]
  have hlists : (fun i => lists i \ (A ∪ V)) = (fun i => (lists i \ A) \ V) := by
    funext i
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hlists]
  exact finiteCanonicalMarkedRowInj_restore_lists p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV

/-! ## Inversion/InitialArithmetic and InitialEnergyCallerFamily -/

theorem initial_marked_child_inj (F V A : Finset ι) (Ψ : Eis →* ℂ) (j t d h : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMarkInj slots lists a (A∪V∪U)*
          W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMarkInj J lists a (A∪V)*
      finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V) := by
  simpa only [secondChildSum,one_mul,←Finset.union_assoc] using
    secondChildSum_marked_fixed_pool_inj p hp hcop hg F V A Ψ j t 1 1 d h slots lists a W X

theorem marked_child_original_lists_inj (F G E V : Finset ι) (hE : E⊆G)
    (Ψ : Eis →* ℂ) (j d t h : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMarkInj slots lists a (G∪V∪U)*W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMarkInj J lists a (G∪V)*
      finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) lists a W (X/primeProductNorm p V) := by
  rw [initial_marked_child_inj p hp hcop hg F V G Ψ j t d h slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRowInj_restore_lists p hp hcop hg F G Ψ (j*t)
    (d*∏ i∈V,p i) (d*h) (slots\J) lists a W (X/primeProductNorm p V)
    (common_killed p G E V hE j d t hd ht)]

omit [DecidableEq σ] in
theorem normalized_child_uniform_inj
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        slots lists a W X =
      finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
        (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) slots lists a W X := by
  have hgen : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) d hd hgen
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  obtain ⟨v,hv,hcol⟩ := initial_poisson_child_normalized p hp hcop hg hpr G E V Ψ j d t h hd ht
  have huv : v=u := by
    apply Units.val_injective
    exact mul_right_cancel₀ hgen (hv.symm.trans hu)
  subst v
  unfold finiteCanonicalMarkedRowInj fixedChildRow
  apply Finset.sum_congr rfl
  intro N hN
  exact hcol _ N

theorem fresh_initial_split_fixed_family_inj
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (hE : E⊆G) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      (∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMarkInj slots lists a (G∪V∪U)*W (primeProductNorm p U/X)) N) =
      ∑ J∈slots.powerset,primeMarkInj J lists a (G∪V)*
        finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
          (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
          (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) (slots\J) lists a W X := by
  obtain ⟨u,hu,hnorm⟩ := normalized_child_uniform_inj p hp hcop hg hpr G E V d t hd ht (σ:=σ)
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  have hV : primeProductNorm p V≠0 := (primeProductNorm_pos p hp V).ne'
  have hx : primeProductNorm p V*X/primeProductNorm p V=X := by
    field_simp
  have he := marked_child_original_lists_inj p hp hcop hg F G E V hE Ψ j d t h hd ht
    slots lists a W (primeProductNorm p V*X)
  rw [hx] at he
  calc
    _ = ∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMarkInj slots lists a (G∪V∪U)*
            W (primeProductNorm p (V∪U)/(primeProductNorm p V*X))) N := by
      apply Finset.sum_congr rfl
      intro N hN
      have hdN : Disjoint V N := Finset.disjoint_left.mpr (by
        intro i hiV hiN
        exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hiN)).2 hiV)
      simp only [secondChildColumn]
      rw [primeProductNorm_union p V N hdN]
      rw [mul_div_mul_left _ _ hV]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hnorm F Ψ j h (slots\J) lists a W X]

/-! ## InitialEnergyCallerModes -/

theorem canonicalColumn_marked_sum_inj
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Point ι) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) :
    (∑ N∈(F\x.overlap).powerset,
      canonicalColumn p hp hcop hg hpr Ψ j (primeMarkInj slots lists a) x h
        (fun A=>W (columnRatio p A Z D B v)) N) =
      ∑ J∈slots.powerset,primeMarkInj J lists a (x.common∪x.overlap)*
        finiteCanonicalMarkedRowInj p hp hcop hg F Ψ (j*quotient p x)
          (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
          (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:Eis)^5*h))
          (slots\J) lists a W (Z^(columnCenter D B v)) := by
  have hgen (A : Finset ι) : primaryGenerator (sourceIdeal p A)≠0 := by
    rw [sourceIdeal_gen p hp hpr A]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hd : Ideal.span {primaryGenerator (sourceIdeal p x.divisor)}=sourceIdeal p x.divisor :=
    (primaryGenerator_spec _ (hgen _)).1
  have ht : Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) :=
    (primaryGenerator_spec _ (hgen _)).1
  obtain ⟨u,hu,hsplit⟩ := fresh_initial_split_fixed_family_inj p hp hcop hg hpr
    x.common x.divisor x.overlap hE (primaryGenerator (sourceIdeal p x.divisor))
    (quotient p x) hd ht (σ:=σ)
  have hu1 : u=1 := by
    apply Units.val_injective
    apply mul_right_cancel₀ (hgen x.divisor)
    simpa only [Units.val_one,one_mul] using hu.symm
  subst u
  have he := hsplit F Ψ j ((unitSector p hp hpr x:Eis)^5*h) slots lists a W
    (Z^(columnCenter D B v))
  simp only [Units.val_one,one_pow,one_mul] at he
  convert he using 1
  · apply Finset.sum_congr rfl
    intro N hN
    simp only [canonicalColumn,primaryGenerator_mul,sourceIdeal_gen p hp hpr x.overlap,
      secondChildColumn,columnRatio_actual,Finset.union_assoc]
  · rfl

/-- `markedModeColumn` with the injective mark. -/
def markedModeColumnInj (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis) (x : Source (ι:=ι) 0)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) : ℂ :=
  ∑ J∈slots.powerset,primeMarkInj J lists a (x.common∪x.overlap)*
    finiteCanonicalMarkedRowInj p hp hcop hg F Ψ
      (j*quotient p (sourcePoint x ∅ ∅))
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*
        ((unitSector p hp hpr (sourcePoint x ∅ ∅):Eis)^5*h))
      (slots\J) lists a W (Z^(columnCenter D B v))

theorem canonicalPairMode_rectangle_inj
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
    (∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMarkInj slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z) =
    (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
      secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
    (star (markedModeColumnInj p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
        slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
      markedModeColumnInj p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
        slots lists a (childLogTest ω₂ (height 5)) Z D B v) := by
  dsimp only
  let x₀ := sourcePoint x ∅ ∅
  have hpoint (N M : Finset ι) :
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMarkInj slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z =
      (outerCoefficient p hp hcop hg Ψ j x₀ ρ *
        secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
          (relativeLog (coordinates p x₀) Z D B v θ H)) *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j (primeMarkInj slots lists a) x₀
        x.frequency
        (fun A=>childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope
          z.1 z.2) 4) (columnRatio p A Z D B v)) N) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j (primeMarkInj slots lists a) x₀
        (-x.frequency)
        (fun A=>childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope
          z.1 z.2) 5) (columnRatio p A Z D B v)) M := by
    unfold InverseInitialPhysicalMeasure.canonicalPairMode
    dsimp only
    rw [sourcePoint_outer_phase p x N M
      (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) Z D B v θ H]
    simp only [canonicalColumn]
    simp only [sourcePoint_unitSector p hp hpr x N M]
    simp only [outerCoefficient,sourcePoint,divisor,quotient,x₀]
  simp_rw [hpoint,←Finset.mul_sum]
  rw [←Finset.sum_mul,←Finset.mul_sum,←star_sum]
  have hleft := canonicalColumn_marked_sum_inj p hp hcop hg hpr x₀ hE F (secondRayMinus Ψ ρ) j
    x.frequency slots lists a (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope
      secondKernelSlope z.1 z.2) 4)) Z D B v
  have hright := canonicalColumn_marked_sum_inj p hp hcop hg hpr x₀ hE F (secondRayPlus Ψ ρ) j
    (-x.frequency) slots lists a (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope
      secondKernelSlope z.1 z.2) 5)) Z D B v
  dsimp only [x₀,sourcePoint] at hleft hright ⊢
  rw [hleft,hright]
  simp only [markedModeColumnInj,sourcePoint]
  ring

/-! ## InitialEnergyCallerSource -/

/-- `rowMode` with the injective mark. -/
def rowModeInj (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Source (ι:=ι) 0) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
  (star (markedModeColumnInj p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
      slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
    markedModeColumnInj p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
      slots lists a (childLogTest ω₂ (height 5)) Z D B v)

theorem canonicalBlock_rows_inj
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (w : Source (ι:=ι) 0→ℂ)
    (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    canonicalBlock p hp hcop hg hpr (pointSource F S) (w ∘ erasePoint) Ψ j
      (primeMarkInj slots lists a) ω₁ ω₂ Z D B v θ H z =
      ∑ x∈S,∑ ρ : SecondRayIndex,w x*rowModeInj p hp hcop hg hpr F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H x ρ z := by
  unfold canonicalBlock
  rw [pointSource_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Function.comp_apply,erase_sourcePoint]
  calc
    _ = ∑ N∈(F\x.overlap).powerset,∑ ρ : SecondRayIndex,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMarkInj slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := by
      apply Finset.sum_congr rfl
      intro N hN
      exact Finset.sum_comm
    _ = ∑ ρ : SecondRayIndex,∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMarkInj slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp_rw [←Finset.mul_sum]
      rw [canonicalPairMode_rectangle_inj p hp hcop hg hpr x (hE x hx) F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H ρ z]
      rfl

theorem physicalBlock_rectangular_common_measure_inj
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (hf : ∀ x∈S,x.frequency≠0)
    (w : Source (ι:=ι) 0→ℂ) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hsupport : BlockSupport p (pointSource F S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂) :
    physicalBlock p hp hcop hg (pointSource F S) (w ∘ erasePoint) Ψ j
      (primeMarkInj slots lists a)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
    (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        (∑ x∈S,∑ ρ : SecondRayIndex,w x*rowModeInj p hp hcop hg hpr F Ψ j
          slots lists a ω₁ ω₂ Z D B v θ H x ρ z) := by
  rw [physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid (pointSource F S) (pointSource_valid F S hE hf)
    (w ∘ erasePoint) Ψ j (primeMarkInj slots lists a) ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [canonicalBlock_rows_inj p hp hcop hg hpr F S hE w Ψ j slots lists a ω₁ ω₂ Z D B v θ H z]

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.physicalBlock_rectangular_common_measure_inj
