/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.Stages
import Candidate.C092.Intake.QRH.SourceCertificate.LowResponse

/-! P.1 cap induction and the H.5 cofactor exponent. The induction preserves the
ordered pair, including the swap, at the actual contraction and both endpoints. -/
namespace QRH.Cycle092Continuation
open QRH.Cycle090 QRH.SourceCertificate
noncomputable section

/-- On the whole native strip the source gain has the favorable sign. -/
theorem native_strip_gain {y : ℝ} (hy : sourceY ≤ y) (hy' : y ≤ sourceY / (H:ℝ)) :
    sourceGain y ≤ -(1/10000000 : ℝ) := by
  have h : 0 ≤ y-sourceY := sub_nonneg.mpr hy
  have h' : y-sourceY ≤ 1/100000 := by
    norm_num [sourceY, H, u] at hy' ⊢
    linarith
  rw [sourceGain, ite_eq_left (source_domain.2.2.le.trans hy)]
  unfold QRH.Cycle090.upperGain
  nlinarith [mul_nonneg h (sub_nonneg.mpr h'), pow_nonneg h 3]

theorem native_strip_width {y : ℝ} (n : ℝ) (hy : sourceY ≤ y) (hy' : y ≤ sourceY / (H:ℝ)) :
    sourceWidth n y < (1-n-y)/2 := by
  unfold sourceWidth
  linarith [native_strip_gain hy hy']

/-- Abstract only the analytic one-step law; the indexing and all domain
conditions for the two earlier calls are discharged here. -/
theorem ordered_source_induction (P : ℝ → ℝ → Prop)
    (native : ∀ n y, sourceY ≤ y → y ≤ sourceY/(H:ℝ) → y ≤ n → n ≤ sourceRatio*y → P n y)
    (step : ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      P (n/(H:ℝ)) (y/(H:ℝ)) →
      (∀ m, y/(H:ℝ) ≤ m → m ≤ sourceY → P (max (n/(H:ℝ)) m) (min (n/(H:ℝ)) m)) → P n y) :
    ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → P n y := by
  have hH := H_real_bounds.1
  have hH' := H_real_bounds.2.le
  have stretch {x : ℝ} (hx : 0 ≤ x) : x ≤ x/(H:ℝ) :=
    (le_div_iff₀ hH).mpr (mul_le_of_le_one_right hx hH')
  have hYY := stretch (source_domain.1.le.trans (source_domain.2.1.le.trans source_domain.2.2.le))
  have aux (j : ℕ) : ∀ n y : ℝ, sourceY0 ≤ y → sourceY*(H:ℝ)^j ≤ y → y ≤ sourceY/(H:ℝ) →
      y ≤ n → n ≤ sourceRatio*y → P n y := by
    induction j with
    | zero =>
      intro n y _ hc ht hn hr
      exact native n y (by simpa using hc) ht hn hr
    | succ j ih =>
      intro n y hb hc ht hn hr
      by_cases hi : sourceY ≤ y
      · exact native n y hi ht hn hr
      have hy := (not_le.mp hi).le
      have hsmall := stretch (source_domain.1.le.trans hb)
      have hnext : sourceY*(H:ℝ)^j ≤ y/(H:ℝ) := (le_div_iff₀ hH).mpr
        (by simpa only [pow_succ,mul_assoc] using hc)
      have hs := div_le_div_of_nonneg_right hn hH.le
      have htop := div_le_div_of_nonneg_right hy hH.le
      apply step n y hb hy hn hr
      · apply ih _ _ (hb.trans hsmall) hnext htop hs
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hr hH.le
      · intro m hm hm'
        have hb' := (hb.trans hsmall).trans (le_min hs hm)
        have hc' := hnext.trans (le_min hs hm)
        have ht' := (min_le_right (n/(H:ℝ)) m).trans (hm'.trans hYY)
        have hr' := source_swap_ratio hH hb hm hm' hn hr hH'
        apply ih _ _ hb' hc' ht' ((min_le_left _ _).trans (le_max_left _ _))
        rcases le_total (n/(H:ℝ)) m with hw | hw
        · simpa only [min_eq_left hw, max_eq_right hw] using hr'.2
        · simpa only [min_eq_right hw, max_eq_left hw] using hr'.1
  have hcast : ((Y*H^2904 : ℚ):ℝ) ≤ ((369/1000 : ℚ):ℝ) :=
    Rat.cast_le.mpr source_stage_crossing.1
  push_cast at hcast
  have hc : sourceY*(H:ℝ)^2904 ≤ sourceY0 := by
    have heq : (↑Y:ℝ) = sourceY := by norm_num [Y,sourceY]
    rw [← heq]
    exact hcast
  intro n y hb ht hn hr
  exact aux 2904 n y hb (hc.trans hb) (ht.trans hYY) hn hr

/-- Moving a same-bin core estimate from V to its central cap M. With the
cofactor exponent (M−V)/6 this costs no extra exponent even across H. -/
theorem cofactor_lift_exponent {V M h loss : ℝ} (hv : V ≤ M) :
    V+(M-V)/6+loss+(5/6)*max 0 (h-V) ≤ M+loss+(5/6)*max 0 (h-M) := by
  rcases le_total h V with a | a
  · rw [max_eq_left (sub_nonpos.mpr a), max_eq_left (sub_nonpos.mpr (a.trans hv))]; linarith
  rcases le_total h M with b | b
  · rw [max_eq_right (sub_nonneg.mpr a), max_eq_left (sub_nonpos.mpr b)]; linarith
  · rw [max_eq_right (sub_nonneg.mpr a), max_eq_right (sub_nonneg.mpr b)]; linarith

theorem cofactor_lift_rpow {U V M h loss : ℝ} (hU : 1 ≤ U) (hv : V ≤ M) :
    U^((M-V)/6) * U^(V+loss+(5/6)*max 0 (h-V)) ≤ U^(M+loss+(5/6)*max 0 (h-M)) := by
  rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hU)]
  apply Real.rpow_le_rpow_of_exponent_le hU
  linarith [cofactor_lift_exponent (h:=h) (loss:=loss) hv]

/-- H.5's joint Cauchy step. The index can be an arbitrary filtered set of
(row,divisor) pairs: phases (in particular the signed Möbius factor) stay
inside the original sum; its two arms and their weights stay distinct. -/
theorem raw_joint_cauchy {ι : Type*} (s : Finset ι) (b : ι → ℝ) (a l r : ι → ℂ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ‖∑ i ∈ s, (b i : ℂ) * a i * l i * star (r i)‖ ≤
    √(∑ i ∈ s, b i * ‖l i‖^2) * √(∑ i ∈ s, b i * ‖r i‖^2) := by
  have arm (f : ι → ℂ) : (∑ i ∈ s, (√(b i) * ‖f i‖)^2) = ∑ i ∈ s, b i * ‖f i‖^2 := by
    apply Finset.sum_congr rfl; intro i hi; rw [mul_pow, Real.sq_sqrt (hb i hi)]
  calc
    _ ≤ ∑ i ∈ s, ‖(b i : ℂ) * a i * l i * star (r i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (√(b i) * ‖l i‖) * (√(b i) * ‖r i‖) := by
      apply Finset.sum_le_sum; intro i hi
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi), norm_star]
      calc
        _ ≤ b i * 1 * ‖l i‖ * ‖r i‖ := by have hb₀ := hb i hi; have ha₁ := ha i hi; gcongr
        _ = _ := by rw [← Real.mul_self_sqrt (hb i hi)]; simp only [Real.sqrt_mul_self (Real.sqrt_nonneg _)]; ring
    _ ≤ _ := by
      simpa only [arm] using (Real.sum_mul_le_sqrt_mul_sqrt s (fun i => √(b i) * ‖l i‖) (fun i => √(b i) * ‖r i‖))

/-- Sum over the actual cofactor fiber, using its multiplicity, with no
replacement of the fiber by a representative or assumption of coprimality. -/
theorem cofactor_fiber_sum {ι : Type*} (s : Finset ι) (energy : ι → ℝ)
    {U V M h loss : ℝ} (hU : 1 ≤ U) (hv : V ≤ M)
    (hc : (s.card : ℝ) ≤ U^((M-V)/6))
    (he : ∀ i ∈ s, energy i ≤ U^(V+loss+(5/6)*max 0 (h-V))) :
    ∑ i ∈ s, energy i ≤ U^(M+loss+(5/6)*max 0 (h-M)) := by
  calc
    _ ≤ ∑ _i ∈ s, U^(V+loss+(5/6)*max 0 (h-V)) := Finset.sum_le_sum he
    _ = (s.card : ℝ) * U^(V+loss+(5/6)*max 0 (h-V)) := by simp
    _ ≤ U^((M-V)/6) * U^(V+loss+(5/6)*max 0 (h-V)) := by gcongr
    _ ≤ _ := cofactor_lift_rpow hU hv

#print axioms raw_joint_cauchy
#print axioms cofactor_fiber_sum

#print axioms native_strip_gain
#print axioms native_strip_width
#print axioms ordered_source_induction
#print axioms cofactor_lift_exponent
#print axioms cofactor_lift_rpow
end
end QRH.Cycle092Continuation
