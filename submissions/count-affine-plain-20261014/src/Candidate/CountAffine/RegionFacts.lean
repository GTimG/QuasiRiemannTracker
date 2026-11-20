/- A48 (AI-assisted, for liqsweep): the closed-form count's side conditions on its region,
derived from the exact certificates in RegionCert. Apache 2.0. -/
import Candidate.CountAffine.RegionCert

set_option autoImplicit false

namespace Cycle61.CountAffine
noncomputable section

/-- Polynomial gates on one rectangle. -/
structure Gates (δ p : ℝ) : Prop where
  den : 0 < tDen δ p
  sum : 0 < sI δ p + sP δ p
  tlo : 0 < condTlo δ p
  thi : 0 < condThi δ p
  rc : 0 < condRC δ p
  cap : 0 < condCap δ p
  b3 : 0 < condB3 δ p

theorem gates_of_region {δ p : ℝ} (h : inRegion δ p) : Gates δ p := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hδ : δ ∈ Set.Icc (29/64:ℝ) (63/128) := ⟨h1, h2⟩
    have hp : p ∈ Set.Icc (15/32:ℝ) (1/2) := ⟨h3, h4⟩
    exact ⟨condTD_R1_pos hδ hp, condS_R1_pos hδ hp, condTlo_R1_pos hδ hp, condThi_R1_pos hδ hp,
      condRC_R1_pos hδ hp, condCap_R1_pos hδ hp, condB3_R1_pos hδ hp⟩
  · have hδ : δ ∈ Set.Icc (115/256:ℝ) (29/64) := ⟨h1, h2⟩
    have hp : p ∈ Set.Icc (31/64:ℝ) (1/2) := ⟨h3, h4⟩
    exact ⟨condTD_R2_pos hδ hp, condS_R2_pos hδ hp, condTlo_R2_pos hδ hp, condThi_R2_pos hδ hp,
      condRC_R2_pos hδ hp, condCap_R2_pos hδ hp, condB3_R2_pos hδ hp⟩

theorem mC_eq {δ p : ℝ} (hD : tDen δ p ≠ 0) (hS : sI δ p + sP δ p ≠ 0) :
    mC δ p = mcNum δ p / (tDen δ p * (sI δ p + sP δ p)) := by
  unfold mC mcNum tStar
  field_simp

/-- All closed-form facts used by the count, on the region. -/
structure Facts (δ p : ℝ) : Prop where
  den : 0 < tDen δ p
  sum : 0 < sI δ p + sP δ p
  tlo : 1927/1850 ≤ tStar δ p
  thi : tStar δ p ≤ 3/2
  rc : 2337/3700 ≤ rC δ p
  cap : (B - 2*mC δ p)/lambda ≤ 1/25
  b3 : inverseLine δ p (tStar δ p - 41/100) ≤ RStar δ p

theorem facts_of_gates {δ p : ℝ} (g : Gates δ p) : Facts δ p := by
  have hD := g.den
  have hS := g.sum
  have hDS : 0 < tDen δ p * (sI δ p + sP δ p) := mul_pos hD hS
  have hl : 0 < lambda := by norm_num [lambda]
  refine ⟨hD, hS, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tStar
    rw [le_div_iff₀ hD]
    have := g.tlo; unfold condTlo at this; linarith
  · unfold tStar
    rw [div_le_iff₀ hD]
    have := g.thi; unfold condThi at this; linarith
  · have hr : rC δ p = (tNum δ p*(sI δ p + sP δ p) - mcNum δ p)/(tDen δ p * (sI δ p + sP δ p)) := by
      unfold rC
      rw [mC_eq hD.ne' hS.ne']
      unfold tStar
      field_simp
    rw [hr, le_div_iff₀ hDS]
    have := g.rc; unfold condRC at this; nlinarith
  · rw [div_le_iff₀ hl, mC_eq hD.ne' hS.ne']
    have hc := g.cap; unfold condCap at hc
    have hm : (B - lambda/25) ≤ 2*(mcNum δ p / (tDen δ p * (sI δ p + sP δ p))) := by
      rw [mul_div_assoc', le_div_iff₀ hDS]
      nlinarith
    linarith
  · have hid : RStar δ p - inverseLine δ p (tStar δ p - 41/100) = condB3 δ p / tDen δ p := by
      unfold RStar inverseLine condB3 tStar
      field_simp <;> ring
    have hpos : 0 < condB3 δ p / tDen δ p := div_pos g.b3 hD
    linarith

theorem facts_of_region {δ p : ℝ} (h : inRegion δ p) : Facts δ p :=
  facts_of_gates (gates_of_region h)

/-- A bilinear form on a square is bounded by its corners. -/
theorem bilinear_corners {A Bc C c e p p' : ℝ} (hce : c < e)
    (hp : p ∈ Set.Icc c e) (hp' : p' ∈ Set.Icc c e)
    (h1 : A + Bc*(c+c) + C*c*c ≤ 0) (h2 : A + Bc*(c+e) + C*c*e ≤ 0)
    (h3 : A + Bc*(e+e) + C*e*e ≤ 0) :
    A + Bc*(p+p') + C*p*p' ≤ 0 := by
  have hL : 0 < (e-c)^2 := by positivity
  have hid : (e-c)^2*(A + Bc*(p+p') + C*p*p') =
      (e-p)*(e-p')*(A + Bc*(c+c) + C*c*c) + ((p-c)*(e-p') + (e-p)*(p'-c))*(A + Bc*(c+e) + C*c*e) +
        (p-c)*(p'-c)*(A + Bc*(e+e) + C*e*e) := by ring
  have w1 : 0 ≤ (e-p)*(e-p') := mul_nonneg (by linarith [hp.2]) (by linarith [hp'.2])
  have w2 : 0 ≤ (p-c)*(e-p') + (e-p)*(p'-c) :=
    add_nonneg (mul_nonneg (by linarith [hp.1]) (by linarith [hp'.2]))
      (mul_nonneg (by linarith [hp.2]) (by linarith [hp'.1]))
  have w3 : 0 ≤ (p-c)*(p'-c) := mul_nonneg (by linarith [hp.1]) (by linarith [hp'.1])
  have := mul_nonpos_of_nonneg_of_nonpos w1 h1
  have := mul_nonpos_of_nonneg_of_nonpos w2 h2
  have := mul_nonpos_of_nonneg_of_nonpos w3 h3
  have hneg : (e-c)^2*(A + Bc*(p+p') + C*p*p') ≤ 0 := by rw [hid]; linarith
  by_contra hc
  have hc' := not_le.mp hc
  have := mul_pos hL hc'
  linarith

theorem gAnti_nonpos {δ p p' : ℝ} (h : inRegion δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) :
    gAnti δ p p' ≤ 0 := by
  unfold gAnti
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hδ : δ ∈ Set.Icc (29/64:ℝ) (63/128) := ⟨h1, h2⟩
    have c1 := anti_cc_R1_pos hδ
    have c2 := anti_ce_R1_pos hδ
    have c3 := anti_ee_R1_pos hδ
    unfold gAnti at c1 c2 c3
    exact bilinear_corners (c := 15/32) (e := 1/2) (by norm_num) ⟨h3, h4⟩ ⟨by linarith, hp'⟩
      (by linarith) (by linarith) (by linarith)
  · have hδ : δ ∈ Set.Icc (115/256:ℝ) (29/64) := ⟨h1, h2⟩
    have c1 := anti_cc_R2_pos hδ
    have c2 := anti_ce_R2_pos hδ
    have c3 := anti_ee_R2_pos hδ
    unfold gAnti at c1 c2 c3
    exact bilinear_corners (c := 31/64) (e := 1/2) (by norm_num) ⟨h3, h4⟩ ⟨by linarith, hp'⟩
      (by linarith) (by linarith) (by linarith)

/-- The closed form is nonincreasing in the prime amplitude on each region slice. -/
theorem RStar_anti {δ p p' : ℝ} (h : inRegion δ p) (hpp : p ≤ p') (hp' : p' ≤ 1/2) :
    RStar δ p' ≤ RStar δ p := by
  have h' := inRegion_up h hpp hp'
  have hD := (facts_of_region h).den
  have hD' := (facts_of_region h').den
  have hb := inRegion_bounds h
  have hg := gAnti_nonpos h hpp hp'
  have hcross := tStar_cross_identity δ p p'
  have ht : tStar δ p' ≤ tStar δ p := by
    unfold tStar
    rw [div_le_div_iff₀ hD' hD]
    have : (p'-p)*gAnti δ p p' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hg
    linarith
  unfold RStar
  have hv : 0 ≤ 5/6-δ := by linarith [hb.2.1]
  nlinarith

end
end Cycle61.CountAffine
