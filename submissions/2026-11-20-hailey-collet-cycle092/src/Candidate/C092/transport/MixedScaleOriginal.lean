/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Second moment of the original physical numerator at row-dependent label
scales, with the witness and prime product on their original rows. -/
import Candidate.C092.transport.MixedScaleRetained
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.OriginalFourth

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentRetainedWeightedSource CenteredMomentOriginalReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator
namespace QRH.Cycle092.MixedScale
local notation "O" => HeckeFamily.O

theorem rowwise_scale_second (S : Finset (Ideal O)) (hS : ∀ P∈S, Prime P) (G : 𝓢(ℝ,ℂ))
    (J : ℕ) (ξ ε b q Cslot : ℝ) (hξ : 0<ξ) (hε : 0<ε) (hb : 0<b) (hslot : 0<Cslot) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ U : ℝ in atTop, 1<U ∧ ∀ (rows : Finset FreeRow),
      (∀ u ∈ rows,rowNorm u ≤ U) →
      ∀ (data : ∀ i : rows,PhysicalReflectionData S hS i.val)
        (N : rows → ℝ) (P : rows → ℂ) (Y m E : ℝ),
      0<Y → (∀ i,0 < N i ∧ N i ≤ b*Y) → 0 ≤ m → 0≤E →
      (∀ i,(data i).combinedConductor ≤ (fixedConductorConstant S:ℝ)*U^m*(Y/N i)) →
      (∀ i,‖P i‖ ≤ Cslot*U^q) →
      (∀ v : ℝ,∀ j : Fin 2,∀ x ∈ Set.Icc 0 ((m+ξ)*Real.log U),
        (∑ i : rows,‖polynomial (rowCharacter S hS i.val) false
          (scaleTest (fun z : ℝ => (annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      (∑ i : rows,‖polynomial (rowCharacter S hS i.val) false G (Y/N i) 0 0*P i‖^2)
        ≤ C*(U^ε*(1+2*((m+ξ)*Real.log U))*E+1) := by
  let K : ℝ := fixedConductorConstant S
  have hK : 0<K := by dsimp [K]; exact_mod_cast fixedConductorConstant_pos S hS
  obtain ⟨H,A,hA,hret⟩ := retained_independent_multiplier ε hε 2 J (by norm_num)
  let dg := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  have hdg₀ : 0 ≤ H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hdg : 0 < dg := by dsimp [dg]; linarith
  let C₁ := A*K^ε*dg^2
  have h₁ : 0<C₁ := by dsimp [C₁]; positivity
  obtain ⟨B,hB,htail⟩ := PhysicalTail.discardedSchwartz_fixed_profile (ξ/2) (q+1) b K (by positivity) hb hK G
  let C₂ := 128*(B*Cslot)^2
  have h₂ : 0<C₂ := by dsimp [C₂]; positivity
  refine ⟨2*(C₁+C₂),by positivity,?_⟩
  filter_upwards [eventually_retained_log_interval K ξ hK hξ,eventually_gt_atTop (1:ℝ)] with U hgeom hU
  refine ⟨hU,?_⟩;intro rows hrows data N P Y m E hY hN hm hE hcombined hP hmoment
  have hup := zero_lt_one.trans hU
  let τ := fun i : rows => (data i).presentation
  let ψ := fun i : rows => (data i).primitive
  let X := fun i : rows => Y/N i
  let R := U^(ξ/4)
  let L := (m+ξ)*Real.log U
  have hL : 0≤L := mul_nonneg (by linarith) (Real.log_pos hU).le
  have hc (i : rows) : (data i).combinedConductor ≤ K*U :=
    (data i).combined_le_row.trans (mul_le_mul_of_nonneg_left (hrows i.val i.property) hK.le)
  have hKreal : 1 ≤ K := by dsimp only [K]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (fixedConductorConstant_pos S hS))
  have hret' := hret (fun _ : rows => G) τ ψ P X (fun _ => R) 0 L dg E (K*U)
    (fun i => div_pos hY (hN i).1) hL (fun i j _ hj => by
      simpa only [X,R,L] using hgeom.2 (τ i) (ψ i) (X i) m (div_pos hY (hN i).1) (hcombined i) j _ hj)
    hdg hE (fun _ => by dsimp [dg]; linarith) (one_le_mul_of_one_le_of_one_le hKreal hU.le)
    (fun i => (data i).redundant_le_combined.trans (hc i)) (fun v j x hx => by
      have he (i : rows) : polynomial (τ i) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) =
          polynomial (rowCharacter S hS i.val) false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v) :=
        (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _ (data i).element_eq ..).symm
      simp_rw [he];exact hmoment v j x hx)
  let retained := fun i : rows => retainedSchwartz (τ i) (ψ i) G (X i) R
  let tail := fun i : rows => discardedSchwartz (τ i) (ψ i) G (X i) R
  have hrt : ∑ i : rows,‖retained i*P i‖^2 ≤ C₁*(U^ε*(1+2*L)*E) := by
    apply hret'.trans_eq
    rw [Real.mul_rpow hK.le hup.le]; dsimp [C₁]; ring
  have hpt (i : rows) : ‖tail i*P i‖ ≤ B*Cslot*U^(-(1:ℝ)) := by
    have ht := htail (τ i) (ψ i) Y (N i) U hY (hN i).1 (hN i).2 hU.le (hc i)
    change ‖discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(ξ/4))*P i‖ ≤ _
    rw [show ξ/4=(ξ/2)/2 by ring,norm_mul]
    apply (mul_le_mul ht (hP i) (norm_nonneg _) (by positivity)).trans_eq
    rw [show -(q+1)=(-1:ℝ)-q by ring, Real.rpow_sub hup]
    field_simp
  have htail' : ∑ i : rows,‖tail i*P i‖^2 ≤ C₂ := by
    have hcd : (Fintype.card rows:ℝ) ≤ 128*U := by simpa only [Fintype.card_coe] using freeRow_count rows U hU.le hrows
    calc
      _ ≤ ∑ _i : rows,(B*Cslot*U^(-(1:ℝ)))^2 := Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt i) 2)
      _ = (Fintype.card rows : ℝ)*(B*Cslot*U⁻¹)^2 := by simp [Real.rpow_neg_one]
      _ ≤ (128*U)*(B*Cslot*U⁻¹)^2 := mul_le_mul_of_nonneg_right hcd (sq_nonneg _)
      _ ≤ _ := by
        have hid : (128*U)*(B*Cslot*U⁻¹)^2 = C₂*U⁻¹ := by dsimp [C₂]; field_simp <;> ring
        rw [hid]; exact mul_le_of_le_one_right h₂.le (inv_le_one_of_one_le₀ hU.le)
  have oneRow (i : rows) : ‖polynomial (rowCharacter S hS i.val) false G (Y/N i) 0 0*P i‖^2 ≤
      2*(‖retained i*P i‖^2 + ‖tail i*P i‖^2) := by
    rw [(data i).split G (Y/N i) R (div_pos hY (hN i).1)]
    change ‖(data i).phase*(retained i+tail i)*P i‖^2 ≤ _
    rw [mul_assoc,add_mul,norm_mul,(data i).phase_norm,one_mul]
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (retained i*P i) (tail i*P i)) 2,
      sq_nonneg (‖retained i*P i‖-‖tail i*P i‖)]
  have hX0 : 0 ≤ U^ε*(1+2*L)*E := by positivity
  calc
    _ ≤ ∑ i : rows,2*(‖retained i*P i‖^2 + ‖tail i*P i‖^2) := Finset.sum_le_sum (fun i _ => oneRow i)
    _ = 2*(∑ i : rows,‖retained i*P i‖^2 + ∑ i : rows,‖tail i*P i‖^2) := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ 2*(C₁*(U^ε*(1+2*L)*E)+C₂) := by linarith only [hrt,htail']
    _ ≤ _ := by change _ ≤ 2*(C₁+C₂)*(U^ε*(1+2*L)*E+1); nlinarith only [h₁,h₂,mul_nonneg h₂.le hX0]

#print axioms rowwise_scale_second
end QRH.Cycle092.MixedScale
end
