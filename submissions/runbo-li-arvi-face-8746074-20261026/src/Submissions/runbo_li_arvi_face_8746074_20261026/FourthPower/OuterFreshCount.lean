/- Copyright (c) 2026 Sil. Apache-2.0.
One outer fixed-inducing root count retains the old forcing ideal and the
fresh selected divisor. Q-primes cost only the fixed radical(Q) factor.
The structural inputs below still need the actual supplier adapter; no
combined count, source, energy, or endpoint estimate is assumed.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.PrincipalCubic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshCount
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge UniqueFactorizationMonoid CenteredExceptionalCount
open CenteredExceptionalProfile CenteredMomentForcing CenteredMomentFixedQForcingCount
open CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem squarefree_prime_product (J : Id) (hJ : Squarefree J) :
    (∏ P : ↥((normalizedFactors J).toFinset), P.val) = J := by
  rw [Finset.prod_coe_sort ((normalizedFactors J).toFinset) (fun P : Id => P)]
  change ((normalizedFactors J).toFinset.val.map id).prod = J
  rw [Multiset.map_id,Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ)]
  exact Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

/-- Q-prime removal for an arbitrary actual moving parameter A. The old
baseline specialized movingElement theorem is not used on the wrong A. -/
theorem fixed_support_count_fixedQ (η : Character) (Q : Id)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, FixedInducingRow η Q m A z)
    (J : Id) (hJ : Squarefree J)
    (hgood : ∀ P ∈ normalizedFactors J, goodLambda ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card : ℝ) ≤ (Ideal.absNorm (commonRadical Q Q) : ℝ)^(2/3 : ℝ)*
      (768*(6 : ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6 : ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm J : ℝ))/6)) := by
  let P : ↥((normalizedFactors J).toFinset) → Id := fun i => i.val
  have hp (i : ↥((normalizedFactors J).toFinset)) : Prime (P i) :=
    prime_of_normalized_factor _ (Multiset.mem_toFinset.mp i.property)
  have hinj : Function.Injective P := Subtype.val_injective
  have hprod : forcingIdeal P (fun _ => 1) (fun _ => 1) Finset.univ = J := by
    simpa [forcingIdeal,forcingSet,P] using squarefree_prime_product J hJ
  let G := goodIdeal Q P (fun _ => 1) (fun _ => 1) Finset.univ
  have hG0 : G ≠ 0 := goodIdeal_ne_zero Q P hp _ _ _
  have hGn : (0 : ℝ) < Ideal.absNorm G := norm_pos hG0
  have hGsq : Squarefree G := goodIdeal_squarefree Q P hp hinj _ _ _
  have hGgood (R : Id) (hR : R ∈ normalizedFactors G) :
      goodLambda ∉ R ∧ (2 : O) ∉ R ∧ IsCoprime Q R ∧
        IsCoprime η.modulus R ∧ valuation (Ideal.span {A}) R % 6 = 2 := by
    obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp
      (goodSet Q P (fun _ => 1) (fun _ => 1) Finset.univ) R hR
    have hQi := (Finset.mem_filter.mp hi).2
    obtain ⟨hl,h2,hη,hval⟩ := hgood (P i) (Multiset.mem_toFinset.mp i.property)
    exact ⟨hl,h2,hQi,hη,hval⟩
  have hb := fixed_support_exceptional_count η Q hQ0 hQ hQ72 m A hm hA hmLam hm2
    rows hrows hex G hGsq hGgood Z Cr M (2*Real.logb Z (Ideal.absNorm G : ℝ))
    (zero_lt_one.trans hZ) hCr (by
      rw [show (2*Real.logb Z (Ideal.absNorm G : ℝ))/2 =
        Real.logb Z (Ideal.absNorm G : ℝ) by ring,
        Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hGn]) hN
  have hb' : (rows.card : ℝ) ≤
      768*(6 : ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6 : ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm G : ℝ))/6) := by
    have he : (M-2*(2*Real.logb Z (Ideal.absNorm G : ℝ)))/6 =
        (M-4*Real.logb Z (Ideal.absNorm G : ℝ))/6 := by ring
    simpa only [he] using hb
  have hJnorm : (Ideal.absNorm J : ℝ) ≤
      (Ideal.absNorm G : ℝ)*Ideal.absNorm (commonRadical Q Q) := by
    simpa only [hprod] using forcing_norm_le Q hQ0 P hp hinj
      (fun _ => 1) (fun _ => 1) Finset.univ
  have hJn : (0 : ℝ) < Ideal.absNorm J := norm_pos hJ.ne_zero
  have hr : (0 : ℝ) < Ideal.absNorm (commonRadical Q Q) :=
    norm_pos (commonRadical_ne_zero Q Q)
  have hcost := fixed_radical_power_loss Z M _ _ _ hZ hJn hGn hr hJnorm
  apply hb'.trans
  calc
    _ ≤ (768*(6 : ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6 : ℝ))*
        ((Ideal.absNorm (commonRadical Q Q) : ℝ)^(2/3 : ℝ)*
          Z^((M-4*Real.logb Z (Ideal.absNorm J : ℝ))/6)) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by ring

theorem valuation_zero_of_coprime_support (H I : Id) (hc : IsCoprime H I)
    (P : Id) (hP : P ∈ normalizedFactors H) : valuation I P = 0 := by
  have hp := prime_of_normalized_factor P hP
  apply Multiset.count_eq_zero.mpr
  intro hi
  exact hp.not_isUnit (hc.isRelPrime
    (dvd_of_mem_normalizedFactors hP) (dvd_of_mem_normalizedFactors hi))

/-- Multiplication by the two genuine cubic twists changes no inherited
old-prime valuation. In particular the old forcing saving is retained. -/
theorem old_valuation_two (H : Id) (A₂ f d : O)
    (hA : A₂ ≠ 0) (hf : f ≠ 0) (hd : d ≠ 0)
    (hHf : IsCoprime H (Ideal.span {f})) (hHD : IsCoprime H (Ideal.span {d}))
    (hval : ∀ P ∈ normalizedFactors H, valuation (Ideal.span {A₂}) P % 6 = 2)
    (P : Id) (hP : P ∈ normalizedFactors H) :
    valuation (Ideal.span {A₂*f^2*d^2}) P % 6 = 2 := by
  have hIA := Ideal.span_singleton_eq_bot.not.mpr hA
  have hIf := Ideal.span_singleton_eq_bot.not.mpr hf
  have hId := Ideal.span_singleton_eq_bot.not.mpr hd
  have hzF := valuation_zero_of_coprime_support H (Ideal.span {f}) hHf P hP
  have hzD := valuation_zero_of_coprime_support H (Ideal.span {d}) hHD P hP
  have hspan : Ideal.span {A₂*f^2*d^2} =
      (Ideal.span {A₂}*(Ideal.span {f})^2)*(Ideal.span {d})^2 := by
    simp only [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow]
  rw [hspan,valuation_mul _ _ _ (mul_ne_zero hIA (pow_ne_zero _ hIf))
    (pow_ne_zero _ hId),valuation_mul _ _ _ hIA (pow_ne_zero _ hIf),
    valuation_pow,valuation_pow,hzF,hzD]
  simpa only [Nat.mul_zero,add_zero] using hval P hP

theorem fresh_valuation_two (A₂ f d : O) (hA : A₂ ≠ 0) (hf : f ≠ 0)
    (hD : Squarefree (Ideal.span {d}))
    (hAD : IsCoprime (Ideal.span {A₂}) (Ideal.span {d}))
    (hfD : IsCoprime (Ideal.span {f}) (Ideal.span {d}))
    (P : Id) (hP : P ∈ normalizedFactors (Ideal.span {d})) :
    valuation (Ideal.span {A₂*f^2*d^2}) P % 6 = 2 := by
  apply PrincipalCubic.fresh_element_valuation (A₂*f^2) d
    (mul_ne_zero hA (pow_ne_zero _ hf)) hD
  · rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow]
    exact hAD.mul_left hfD.pow_left
  · exact hP

/-- The combined forcing ideal is not a premise: its squarefreeness and
both sets of valuations are proved from the separate structural facts. -/
theorem combined_structure (H : Id) (hH : Squarefree H) (A₂ f d : O)
    (hA : A₂ ≠ 0) (hf : f ≠ 0) (hd : d ≠ 0)
    (hD : Squarefree (Ideal.span {d}))
    (hHf : IsCoprime H (Ideal.span {f})) (hHD : IsCoprime H (Ideal.span {d}))
    (hAD : IsCoprime (Ideal.span {A₂}) (Ideal.span {d}))
    (hfD : IsCoprime (Ideal.span {f}) (Ideal.span {d}))
    (hval : ∀ P ∈ normalizedFactors H, valuation (Ideal.span {A₂}) P % 6 = 2) :
    Squarefree (H*Ideal.span {d}) ∧
      ∀ P ∈ normalizedFactors (H*Ideal.span {d}),
        valuation (Ideal.span {A₂*f^2*d^2}) P % 6 = 2 := by
  refine ⟨squarefree_mul_iff.mpr ⟨hHD.isRelPrime,hH,hD⟩,?_⟩
  intro P hP
  rw [normalizedFactors_mul hH.ne_zero hD.ne_zero] at hP
  rcases Multiset.mem_add.mp hP with hp | hp
  · exact old_valuation_two H A₂ f d hA hf hd hHf hHD hval P hp
  · exact fresh_valuation_two A₂ f d hA hf hD hAD hfD P hp

/-- One root count, before K4 completion, for the actual outer moving
parameter. There is no assumption of an improved count or physical energy.
The hypotheses below still need discharge by the actual supplier adapter. -/
theorem combined_count_exact (η : Character) (Q : Id)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A₂ f d : O) (hm : m ≠ 0) (hA : A₂ ≠ 0) (hf : f ≠ 0) (hd : d ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (H : Id) (hH : Squarefree H) (hD : Squarefree (Ideal.span {d}))
    (hHf : IsCoprime H (Ideal.span {f})) (hHD : IsCoprime H (Ideal.span {d}))
    (hAD : IsCoprime (Ideal.span {A₂}) (Ideal.span {d}))
    (hfD : IsCoprime (Ideal.span {f}) (Ideal.span {d}))
    (hval : ∀ P ∈ normalizedFactors H, valuation (Ideal.span {A₂}) P % 6 = 2)
    (hgoodH : ∀ P ∈ normalizedFactors H,
      goodLambda ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime η.modulus P)
    (hgoodD : ∀ P ∈ normalizedFactors (Ideal.span {d}),
      goodLambda ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime η.modulus P)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, FixedInducingRow η Q m (A₂*f^2*d^2) z)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card : ℝ) ≤ (Ideal.absNorm (commonRadical Q Q) : ℝ)^(2/3 : ℝ)*
      (768*(6 : ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6 : ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm H : ℝ)-
          4*Real.logb Z (Ideal.absNorm (Ideal.span {d}) : ℝ))/6)) := by
  obtain ⟨hJ,hJval⟩ := combined_structure H hH A₂ f d hA hf hd hD hHf hHD hAD hfD hval
  have hgood (P : Id) (hP : P ∈ normalizedFactors (H*Ideal.span {d})) :
      goodLambda ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime η.modulus P ∧
        valuation (Ideal.span {A₂*f^2*d^2}) P % 6 = 2 := by
    have hv := hJval P hP
    rw [normalizedFactors_mul hH.ne_zero hD.ne_zero] at hP
    rcases Multiset.mem_add.mp hP with hp | hp
    · obtain ⟨hl,h2,hη⟩ := hgoodH P hp
      exact ⟨hl,h2,hη,hv⟩
    · obtain ⟨hl,h2,hη⟩ := hgoodD P hp
      exact ⟨hl,h2,hη,hv⟩
  have hb := fixed_support_count_fixedQ η Q hQ0 hQ hQ72 m (A₂*f^2*d^2) hm
    (mul_ne_zero (mul_ne_zero hA (pow_ne_zero _ hf)) (pow_ne_zero _ hd)) hmLam hm2
    rows hrows hex (H*Ideal.span {d}) hJ hgood Z Cr M hZ hCr hN
  rw [map_mul,Nat.cast_mul,Real.logb_mul (norm_pos hH.ne_zero).ne'
    (norm_pos hD.ne_zero).ne'] at hb
  have he : (M-4*(Real.logb Z (Ideal.absNorm H : ℝ)+
      Real.logb Z (Ideal.absNorm (Ideal.span {d}) : ℝ)))/6 =
      (M-4*Real.logb Z (Ideal.absNorm H : ℝ)-
        4*Real.logb Z (Ideal.absNorm (Ideal.span {d}) : ℝ))/6 := by ring
  simpa only [he] using hb

/-- Explicit multiplicative form of the fresh saving. Fold is the
inherited logarithmic forcing quantity, which remains unchanged. -/
theorem fresh_gain_identity (Z M Fold N : ℝ) (hZ : 1 < Z) (hN : 0 < N) :
    Z^((M-Fold-4*Real.logb Z N)/6) = Z^((M-Fold)/6)*N^(-(2/3 : ℝ)) := by
  have he : (M-Fold-4*Real.logb Z N)/6 =
      (M-Fold)/6+Real.logb Z N*(-(2/3 : ℝ)) := by ring
  rw [he,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_mul (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

/-- The actual selected product window pays the claimed power saving.
This uses its lower norm endpoint; an upper endpoint alone would not do. -/
theorem fresh_gain_window (Z M Fold N δ : ℝ) (hZ : 1 < Z)
    (hN : Z^δ ≤ N) :
    Z^((M-Fold-4*Real.logb Z N)/6) ≤ Z^((M-Fold-4*δ)/6) := by
  have hl := Real.logb_le_logb_of_le hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) δ) hN
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

end
end Candidate.FourthPower.OuterFreshCount
