/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/{Descent/MarkBounds,
Inversion/InitialZeroMode,Inversion/InitialZeroModeBudget}.lean` (Apache-2.0). Modified by Sil
(2026-11-12): the mark `primeMark slots lists a` on pairwise disjoint lists is replaced by an
arbitrary mark `M` with `‖M S‖ ≤ 2^|S|` (the only property used); the injective mark is reduced
to it by `primeMarkInj_norm_le_two_pow` and the degree-2 homogeneity of the physical modes.
Proofs otherwise unchanged. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Tail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialZeroModeBudget

/-!
# Inverse.Inj.ZeroMode — the zero mode of the physical block for the injective mark

* `two_pow_card_small_power` — `2^|U| ≤ C N(U)^ε`;
* `marked_coefficient_mass_gen`, `marked_normalized_zero_gen`, `physical_marked_zero_bound_gen`
  — the baseline zero-mode bounds for any mark with `‖M S‖ ≤ 2^|S|`;
* `initialPhysicalMode_smul`; **`physical_marked_zero_bound_inj`** (constant `× (K^K)^2`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment InverseInitialZeroMode InverseInitialArithmetic
open Qrh.MarkedAnchor.Inverse
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem two_pow_card_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (U : Finset ι),
      (2:ℝ)^U.card ≤ C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  exact hh

theorem marked_coefficient_mass_gen (eps b B:ℝ)(heps:0<eps)(hb:0<b)(_hB:0≤B):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[DecidableEq ι]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (M:Finset ι→ℂ),(∀S,‖M S‖≤(2:ℝ)^S.card)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X:ℝ,0<X→
      (∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>M A*W (primeProductNorm p A/X)) A‖^2)≤C*X^(1+eps) := by
  obtain ⟨Cm,hCm,hm⟩:=two_pow_card_small_power (eps/2) (by positivity)
  refine ⟨128*b*(Cm*b^(eps/2)*B)^2+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj pool Ψ hΨ m c d M hM W hW hs X hX
  let T:=pool.powerset.filter (fun A=>W (primeProductNorm p A/X)≠0)
  have hXb:0<b*X:=mul_pos hb hX
  have hnorm:∀A∈T,primeProductNorm p A≤b*X:=by
    intro A hA
    exact (div_le_iff₀ hX).mp (hs _ (Finset.mem_filter.mp hA).2)
  have hcard:(T.card:ℝ)≤128*(b*X):=by
    by_cases hsmall:1≤b*X
    · apply (Nat.cast_le.mpr (Finset.card_le_card (show T⊆boundedPrimeSupports p pool (b*X) from ?_))).trans
        (boundedPrimeSupports_card p hinj pool (b*X) hsmall)
      intro A hA
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,hnorm A hA⟩
    · have hz:T=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        exact hsmall ((primeProductNorm_ge_one p hp A).trans (hnorm A hA))
      rw [hz]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have he:(∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>M A*W (primeProductNorm p A/X)) A‖^2)=
      ∑A∈T,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>M A*W (primeProductNorm p A/X)) A‖^2:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    have hz:W (primeProductNorm p A/X)=0:=by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
    simp only [secondInputCoefficient,hz,mul_zero,norm_zero,zero_pow (by decide:2≠0)]
  have hcoeff:∀A∈T,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>M A*W (primeProductNorm p A/X)) A‖≤Cm*(b*X)^(eps/2)*B:=by
    intro A hA
    apply (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d _ A).trans
    rw [norm_mul]
    apply mul_le_mul _ (hW _) (norm_nonneg _) (by positivity)
    exact ((hM A).trans (hm p hp hcop A)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (primeProductNorm_pos p hp A).le (hnorm A hA) (by positivity)) hCm.le)
  rw [he]
  calc
    _≤∑_A∈T,(Cm*(b*X)^(eps/2)*B)^2:=by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff A hA) 2
    _=(T.card:ℝ)*(Cm*(b*X)^(eps/2)*B)^2:=by simp
    _≤(128*(b*X))*(Cm*(b*X)^(eps/2)*B)^2:=mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _=(128*b*(Cm*b^(eps/2)*B)^2)*X^(1+eps):=by
      rw [Real.mul_rpow hb.le hX.le,Real.rpow_add hX,Real.rpow_one]
      have hh:(X^(eps/2))^2=X^eps:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hX.le]
        congr 1
        norm_num
      calc
        _=(128*b*(Cm*b^(eps/2)*B)^2)*(X*(X^(eps/2))^2):=by ring
        _=_:=by rw [hh]
    _≤_:=by nlinarith [Real.rpow_nonneg hX.le (1+eps)]

theorem marked_normalized_zero_gen (eps b B:ℝ)(heps:0<eps)(hb:0<b)(hB:0≤B)
    (Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[DecidableEq ι]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (M:Finset ι→ℂ),(∀S,‖M S‖≤(2:ℝ)^S.card)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X Y:ℝ,0<X→0<Y→
      ∀K:Finset ι→Finset ι→Finset O,
      (∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈K G E)→
      ‖(X⁻¹:ℂ)*truncatedSecondZero p hg pool Ψ m c d
        (fun A=>M A*W (primeProductNorm p A/X)) Φ Y K‖≤C*Y*X^eps := by
  obtain ⟨Cm,hCm,hm⟩:=marked_coefficient_mass_gen eps b B heps hb hB
  refine ⟨Cm*‖paperRadialFourier Φ 0‖+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj pool Ψ hΨ m c d M hM W hW hs X Y hX hY K hK
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  have hz:=truncatedSecondZero_norm_le p hg hinj pool Ψ m c d
    (fun A=>M A*W (primeProductNorm p A/X)) Φ Y K hK
  rw [abs_of_pos hY] at hz
  apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hX.le)).trans
  have hm':=hm p hp hcop hg hinj pool Ψ hΨ m c d M hM W hW hs X hX
  calc
    _≤X⁻¹*(Y*‖paperRadialFourier Φ 0‖*(Cm*X^(1+eps))):=by gcongr
    _=(Cm*‖paperRadialFourier Φ 0‖)*Y*X^eps:=by
      rw [Real.rpow_add hX,Real.rpow_one]
      field_simp
    _≤_:=by nlinarith [mul_nonneg hY.le (Real.rpow_nonneg hX.le eps)]

theorem physical_marked_zero_bound_gen (loss L b B:ℝ)(hloss:0<loss)(hL:0≤L)
    (hb:0<b)(hB:0≤B)(Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[DecidableEq ι]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(_hpr:∀i,λ₀^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(j:O)
      (M:Finset ι→ℂ),(∀S,‖M S‖≤(2:ℝ)^S.card)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→
      ∀Z D m:ℝ,1≤Z→D≤L→
      ‖∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,
          initialPhysicalMode p hp hcop hg Ψ j M
            W Φ Z D m G U T E 0 else 0‖≤C*Z^(m+loss) := by
  let eps:=loss/(L+1)
  have heps:0<eps:=div_pos hloss (by linarith)
  obtain ⟨C,hC,hbound⟩:=marked_normalized_zero_gen eps b B heps hb hB Φ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool Ψ hΨ j M hM W hW hs Z D m hZ hD
  have hZ0:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  rw [physical_zero_sum p hp hcop hg hinj hc hpr]
  have heq:((Z^(-D):ℝ):ℂ)=((Z^D:ℝ):ℂ)⁻¹:=by
    rw [Real.rpow_neg hZ0.le,Complex.ofReal_inv]
  rw [heq]
  have hb':=hbound p hp hcop hg hinj pool Ψ hΨ j 1 1 M hM
    W hW hs (Z^D) (Z^m) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (fun _ _=>{0}) (by intros; simp)
  change ‖_‖≤C*Z^(m+loss)
  apply hb'.trans
  rw [←Real.rpow_mul hZ0.le, mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  have hprod:D*eps≤loss:=by
    apply (mul_le_mul_of_nonneg_right hD heps.le).trans
    dsimp [eps]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith:0<L+1)).mpr
    nlinarith
  linarith

section Homog
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem initialPhysicalMode_smul (Ψ : O →* ℂ) (j : O) (c : ℝ) (M : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι) (h : O) :
    initialPhysicalMode p hp hcop hg Ψ j (fun S => (c : ℂ) * M S) V Φ Z D m G U T E h =
      ((c^2 : ℝ) : ℂ) * initialPhysicalMode p hp hcop hg Ψ j M V Φ Z D m G U T E h := by
  unfold initialPhysicalMode initialColumn
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  push_cast
  ring

end Homog

/-- **The zero mode for the injective mark** (lists may overlap), constant `× (K^K)^2`. -/
theorem physical_marked_zero_bound_inj (loss L b B:ℝ)(hloss:0<loss)(hL:0≤L)
    (hb:0<b)(hB:0≤B)(Φ:𝓢(ℝ,ℂ))(K:ℕ):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type}[Fintype ι][DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(_hpr:∀i,λ₀^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(j:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      slots.card≤K→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→
      ∀Z D m:ℝ,1≤Z→D≤L→
      ‖∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,
          initialPhysicalMode p hp hcop hg Ψ j (primeMarkInj slots lists a)
            W Φ Z D m G U T E 0 else 0‖≤C*Z^(m+loss) := by
  obtain ⟨C,hC,hgen⟩ := physical_marked_zero_bound_gen loss L b B hloss hL hb hB Φ
  have hKK : (0:ℝ) < ((K ^ K : ℕ) : ℝ) := by exact_mod_cast natPow_self_pos K
  refine ⟨((K ^ K : ℕ) : ℝ)^2*C,by positivity,?_⟩
  intro ι σ _ _ _ p hp _ hcop hg hinj hc hpr pool Ψ hΨ j slots lists a hK ha W hW hs Z D m hZ hD
  set A : ℝ := ((K ^ K : ℕ) : ℝ) with hA
  have hA0 : A ≠ 0 := hKK.ne'
  have hle : ((slots.card ^ slots.card : ℕ) : ℝ) ≤ A := by
    rw [hA]
    exact_mod_cast natPow_self_le hK
  let M : Finset ι → ℂ := fun U => ((A⁻¹ : ℝ) : ℂ) * primeMarkInj slots lists a U
  have hM : ∀ U, ‖M U‖ ≤ (2:ℝ)^U.card := by
    intro U
    have h := primeMarkInj_norm_le_two_pow slots lists a ha U
    simp only [M, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hKK]
    rw [inv_mul_le_iff₀ hKK]
    exact h.trans (mul_le_mul_of_nonneg_right hle (by positivity))
  have hmark : primeMarkInj slots lists a = fun U => ((A : ℝ) : ℂ) * M U := by
    funext U
    simp only [M, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hA0, Complex.ofReal_one,
      one_mul]
  have hsum : (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,
        initialPhysicalMode p hp hcop hg Ψ j (fun U => ((A : ℝ) : ℂ) * M U)
          W Φ Z D m G U T E 0 else 0) =
      ((A^2 : ℝ) : ℂ) * ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,
        initialPhysicalMode p hp hcop hg Ψ j M W Φ Z D m G U T E 0 else 0 := by
    simp only [initialPhysicalMode_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun G _ => Finset.sum_congr rfl (fun U _ =>
      Finset.sum_congr rfl (fun T _ => ?_)))
    split_ifs
    · rw [Finset.mul_sum]
    · simp
  rw [hmark, hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg A)]
  have hb' := hgen p hp hcop hg hinj hc hpr pool Ψ hΨ j M hM W hW hs Z D m hZ hD
  calc A^2 * ‖_‖ ≤ A^2 * (C*Z^(m+loss)) := mul_le_mul_of_nonneg_left hb' (sq_nonneg A)
    _ = _ := by ring

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.physical_marked_zero_bound_inj
