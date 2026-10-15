/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B111
import Submissions.gao_cycle61_plane_20261013.Bundles.B152
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondOuterPayment; sha256 6878e8fc06b332b5db2ce8c76cb7c8c6f5467d69120c39c71625c2ef9bac7aaf -/
section
                                                        
                                                                    

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentSourceBlockWindows CenteredMomentSecondInputCapacitySource
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- The two witnessed second dyads jointly absorb their square-root
normalizations into the actual input volume. -/
theorem actual_second_outside_volume (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (a V : ℝ)(ha : 0< a)(hV : 0< V)
    (hlower : ∀I : Ideal O,s.beta I≠0 → a*V≤(I.absNorm:ℝ))
    (hne : s.value W≠0) :
    s.outside≤ s.K/(a*V)*normalizer s.C s.D s.inactive := by
  obtain ⟨hc,hd⟩ := physicalBlock_scale_lower s.character s.height s.pool s.beta
    s.C s.D s.hC s.hD s.inactive s.radius s.rows W s.K s.dyad a V ha hlower hne
  have hC := norm_pos s.C s.hC.1
  have hD := norm_pos s.D s.hD.1
  have hX := dyadicScale_pos (s.dyad 2)
  have hY := dyadicScale_pos (s.dyad 3)
  have hcl : a*V≤(s.C.absNorm:ℝ)*dyadicScale (s.dyad 2) := by
    have hh := (div_le_div_iff₀ hC ha).mp hc
    nlinarith
  have hdl : a*V≤(s.D.absNorm:ℝ)*dyadicScale (s.dyad 3) := by
    have hh := (div_le_div_iff₀ hD ha).mp hd
    nlinarith
  have hs : a*V≤ Real.sqrt (s.C.absNorm:ℝ)*Real.sqrt (s.D.absNorm:ℝ)*
      Real.sqrt (dyadicScale (s.dyad 2))*Real.sqrt (dyadicScale (s.dyad 3)) := by
    have hh := mul_le_mul hcl hdl (mul_pos ha hV).le (mul_pos hC hX).le
    have hsq : (a*V)^2≤(Real.sqrt (s.C.absNorm:ℝ)*Real.sqrt (s.D.absNorm:ℝ)*
        Real.sqrt (dyadicScale (s.dyad 2))*Real.sqrt (dyadicScale (s.dyad 3)))^2 := by
      simp only [mul_pow,Real.sq_sqrt hC.le,Real.sq_sqrt hD.le,
        Real.sq_sqrt hX.le,Real.sq_sqrt hY.le]
      nlinarith
    nlinarith [show 0≤ Real.sqrt (s.C.absNorm:ℝ)*Real.sqrt (s.D.absNorm:ℝ)*
      Real.sqrt (dyadicScale (s.dyad 2))*Real.sqrt (dyadicScale (s.dyad 3)) by positivity]
  unfold SecondBlockSource.outside outerScalar
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left s.K_pos.le (mul_pos ha hV) hs)
    (normalizer_pos s.C s.D s.hC s.inactive).le

/-- The lower-support constant is fixed before the actual block data. -/
theorem actual_input_second_outside {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(a ap : ℝ)(ha : 0< a)(hap : 0< ap)
    (d : SecondInputDatum α)(W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤ N)(hlower : a≤ d.input.lower)
    (hW₁ : ∀x,d.input.W₁ x≠0 → ap≤ x)(hW₂ : ∀x,d.input.W₂ x≠0 → ap≤ x)
    (hne : d.block.value W≠0) :
    d.block.outside≤ d.K/(lowerFactor N a ap*volume d.input.toData)*
      normalizer d.C d.D d.inactive := by
  apply actual_second_outside_volume d.block W (lowerFactor N a ap) (volume d.input.toData)
    (lowerFactor_pos N a ap ha hap) (volume_pos _) _ hne
  intro I hi
  have hc : Fintype.card d.slots≤ Fintype.card α := by simpa using Finset.card_le_univ d.slots
  exact actual_lower_support N a ap ha hap d.input
    (hc.trans hcard) hlower hW₁ hW₂ d.R d.seed I hi

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_outside_volume
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_input_second_outside

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondOuterPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondEffectiveScalar; sha256 aee88193876c9e8169751cdfbe17523d6f09c62bcaef2cfbd8e1c38bad0f0865 -/
section
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondInputCapacitySource

/-- Zero physical blocks can be removed before the whole joint Cauchy step.
This supplies actual dyad witnesses wherever the outside weight survives. -/
def secondEffectiveWeight {Label : Type*} (s : Label→ SecondBlockSource)
    (w : Label→ℂ) (W : 𝓢(ℝ,ℂ)) (l : Label) : ℂ :=
  if (s l).value W=0 then 0 else w l

theorem actual_second_effective_sum {Label : Type*}[Fintype Label]
    (s : Label→ SecondBlockSource)(w : Label→ℂ)(W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=∑l,secondEffectiveWeight s w W l*(s l).value W := by
  apply Finset.sum_congr rfl
  intro l hl
  unfold secondEffectiveWeight
  split_ifs with h <;> simp_all

/-- A scalar bound for the actual effective weights, valid even when a
block has vanished. The normalizer is paid once on each squared side. -/
theorem actual_second_effective_scalar_bound {α Label : Type*}
    [Fintype α][DecidableEq α]
    (N : ℕ)(a ap : ℝ)(ha : 0< a)(hap : 0< ap)
    (d : Label→ SecondInputDatum α)(w : Label→ℂ)(W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤ N)
    (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0 → ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0 → ap≤ x)
    (r : SecondRow (fun l=>(d l).block)) :
    let we := secondEffectiveWeight (fun l=>(d l).block) w W
    let balance := secondGeometricBalance (fun l=>(d l).block) we
    let E := ‖w r.1‖*((d r.1).K/lowerFactor N a ap)*
      normalizer (d r.1).C (d r.1).D (d r.1).inactive
    ‖(balance r:ℂ)⁻¹*secondRowLeftScalar d we r‖^2≤ E ∧
    ‖(balance r:ℂ)*secondRowRightScalar d r‖^2≤ E := by
  intro we balance E
  obtain ⟨hl,hr⟩ := actual_second_balanced_scalar_norms d we r
  rw [hl,hr]
  suffices hh : ‖we r.1‖*(d r.1).block.outside*volume (d r.1).input.toData≤ E from ⟨hh,hh⟩
  have hp := lowerFactor_pos N a ap ha hap
  have hv := volume_pos (d r.1).input.toData
  have hn := normalizer_pos (d r.1).C (d r.1).D (d r.1).hC (d r.1).inactive
  by_cases h : (d r.1).block.value W=0
  · simp only [we,secondEffectiveWeight,h,ite_true,norm_zero,zero_mul]
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (div_pos (d r.1).K_pos hp).le) hn.le
  · have hh := actual_input_second_outside N a ap ha hap (d r.1) W hcard
      (hlower r.1) (hW₁ r.1) (hW₂ r.1) h
    simp only [we,secondEffectiveWeight,h,ite_false]
    have hh' := mul_le_mul_of_nonneg_left hh (norm_nonneg (w r.1))
    have hh'' := mul_le_mul_of_nonneg_right hh' hv.le
    apply hh''.trans (le_of_eq ?_)
    dsimp only [E]
    field_simp

/-- The original block sum is contracted after removing its zero terms
and balancing the remaining actual scalars. -/
theorem actual_second_effective_contraction (W : 𝓢(ℝ,ℂ))(A J : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→ SecondBlockSource)(w : Label→ℂ)(r : ℝ),
      0< r → (∀l,(s l).ratio=r) → ∀E : ℝ,0≤ E →
      (∀t : ℝ,secondBalancedEnergyPair s (secondEffectiveWeight s w W)
        (secondGeometricBalance s (secondEffectiveWeight s w W)) t≤ E*(1+‖t‖)^J) →
      (1+r)^A*‖∑l,w l*(s l).value W‖≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := actual_second_balanced_contraction W A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s w r hr heq E hE he
  rw [actual_second_effective_sum s w W]
  exact hbound s (secondEffectiveWeight s w W)
    (secondGeometricBalance s (secondEffectiveWeight s w W))
    (second_geometric_balance_nonzero s (secondEffectiveWeight s w W)) r hr heq E hE he

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_effective_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_effective_scalar_bound
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_effective_contraction

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondEffectiveScalar -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondNormalizedWindows; sha256 f190833d893466b1eb271311569ee51c9c6374c4b5c59757c4e33a970cb59e14 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                         
                                       

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonHeightEnvelope CenteredMomentHeckeColumnWindow
open CenteredMomentCommonLinearNormalization CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn
open CenteredMomentCommonPairedSource
open CenteredMomentAmplificationChildInput
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondInputCapacitySource
open CenteredMomentLogDyadic CenteredMomentSecondPhysicalBlock
local notation "O" => HeckeFamily.O

/-- Positive source weights stay inside the full joint sum through Mellin
inversion. No source-label cardinality is introduced. -/
theorem actual_weighted_normalized_windows {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→ Finset α) (s : (k : κ)→ Input (slots k))
    (C R seed L : κ→ Ideal O) (hC : ∀k,Supported (C k)) (η : κ→ Character)
    (t θ X : κ→ℝ) (hX : ∀k,0< X k) (z : κ→ O) (weight : κ→ℝ)
    (hw : ∀k,0≤ weight k) (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤ E)
    (he : ∀u : ℝ,(∑k∈rows,weight k*‖normalizedColumn
      (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
      (C k) (hC k) (R k) (seed k) (L k) (z k)‖^2)≤ E*(1+‖u‖)^(2*J)) :
    (∑k∈rows,weight k*‖windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
      E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  have hn (k : κ) : ‖(Real.sqrt (weight k):ℂ)‖^2=weight k := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw k)]
  have hh := actual_heterogeneous_joint_window_energy rows slots s C R seed L hC η t θ X hX
    z (fun k=>(Real.sqrt (weight k):ℂ)) V hc hs J E hE ?_
  · simpa only [norm_mul,mul_pow,hn] using hh
  · intro u
    simpa only [norm_mul,mul_pow,hn] using he u

/-- Full second-stage balanced energy from the two literal normalized
column sums. This is the window connector; its analytic inputs are the
joint sums, not individual source estimates. -/
theorem actual_balanced_energy_from_normalized {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t : ℝ) (J : ℕ)
    (Eleft Eright : ℝ) (hEl : 0≤ Eleft) (hEr : 0≤ Eright)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus)
    (hl : ∀u : ℝ,(∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
          ((d r.1).input.t+2*Real.pi*(u-t)))
          (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L r.2.2.2.val‖^2)≤ Eleft*(1+‖u‖)^(2*J))
    (hr : ∀u : ℝ,(∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
          ((d r.1).input.t+2*Real.pi*(u-(-t))))
          (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L (-r.2.2.2.val)‖^2)≤ Eright*(1+‖u‖)^(2*J)) :
    secondBalancedEnergyPair (fun l=>(d l).block) w
      (secondGeometricBalance (fun l=>(d l).block) w) t≤
      Real.sqrt Eleft*Real.sqrt Eright*
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hs u‖| *
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
          (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
          (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hs) u‖| := by
  let rows := secondLiveRows (fun l=>(d l).block)
  let pairs := rows.sigma (secondResidualIdeals (fun l=>(d l).block))
  let weight := fun r : SecondRow (fun l=>(d l).block)=>
    ‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData
  have hw (r) : 0≤ weight r := mul_nonneg
    (mul_nonneg (norm_nonneg _) (second_outside_pos _).le)
      (CenteredMomentExceptionalAmplitudePair.volume_pos _).le
  have hleft := actual_weighted_normalized_windows pairs (fun q=>(d q.1.1).slots)
    (fun q=>(d q.1.1).input) (fun q=>(d q.1.1).C) (fun q=>(d q.1.1).R)
    (fun q=>(d q.1.1).seed) (fun q=>q.2) (fun q=>(d q.1.1).hC)
    (fun q=>(d q.1.1).τ q.1.2.1) (fun q=>(d q.1.1).input.t) (fun _=>t)
    (fun q=>dyadicScale ((d q.1.1).dyad 2)) (fun _=>dyadicScale_pos _)
    (fun q=>q.1.2.2.2.val) (fun q=>weight q.1) (fun q=>hw q.1) logAnnulus hc hs J Eleft hEl
    (fun u=>by simpa only [pairs,rows,weight,Finset.sum_sigma] using hl u)
  have hright := actual_weighted_normalized_windows pairs (fun q=>(d q.1.1).slots)
    (fun q=>(d q.1.1).input) (fun q=>(d q.1.1).D) (fun q=>(d q.1.1).R)
    (fun q=>(d q.1.1).seed) (fun q=>q.2) (fun q=>(d q.1.1).hD)
    (fun q=>(d q.1.1).τ q.1.2.2.1⁻¹) (fun q=>(d q.1.1).input.t) (fun _=>-t)
    (fun q=>dyadicScale ((d q.1.1).dyad 3)) (fun _=>dyadicScale_pos _)
    (fun q=>-q.1.2.2.2.val) (fun q=>weight q.1) (fun q=>hw q.1)
    (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hs) J Eright hEr
    (fun u=>by simpa only [pairs,rows,weight,Finset.sum_sigma] using hr u)
  simp only [pairs,rows,weight,Finset.sum_sigma] at hleft hright
  rw [actual_second_geometric_row_energy]
  have hh := mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_mul hEl,Real.sqrt_mul hEr,Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs] at hh
  exact hh.trans_eq (by ring)

/-- The real weight in the joint window sum has the genuine source-scale
cap, including canceled blocks. This is the weight paid by the low and
extracted-prime scalar lemmas. -/
theorem actual_effective_physical_weight {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (W : SchwartzMap ℝ ℂ)
    (hcard : Fintype.card α≤ N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0 → ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0 → ap≤ x)
    (r : SecondRow (fun l=>(d l).block)) :
    ‖secondEffectiveWeight (fun l=>(d l).block) w W r.1‖*(d r.1).block.outside*
        volume (d r.1).input.toData≤
      ‖w r.1‖*((d r.1).K/lowerFactor N a ap)*
        CenteredMomentSecondCanonicalScalar.normalizer (d r.1).C (d r.1).D (d r.1).inactive := by
  have hh := (actual_second_effective_scalar_bound N a ap ha hap d w W
    hcard hlower hW₁ hW₂ r).1
  rw [(actual_second_balanced_scalar_norms d
    (secondEffectiveWeight (fun l=>(d l).block) w W) r).1] at hh
  exact hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_normalized_windows
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_balanced_energy_from_normalized
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_effective_physical_weight

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondNormalizedWindows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondColumnReindex; sha256 720e539e0cb664d13e5acc053ec0399c5988de7b6feabcb1a1028f55ac4d9226 -/
section
                                                           

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentCommonRadialData
open CenteredMomentCommonLinearNormalization CenteredMomentAmplificationChildInput
open CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

/-- The original row set with precisely the physical live-row conditions.
No canonical partition or reflection closure is required of `s.rows`. -/
def secondLiveColumnRows (s : SecondBlockSource) : Finset s.rows :=
  Finset.univ.filter (fun z=>logAnnulus s.rho≠0 ∧
    logAnnulus (s.x z.val)≠0 ∧ s.rowWeight z.val≠0)

/-- Residual ideals depend on the source label alone, not on either ray
or the physical row. -/
theorem actual_second_residual_ideals_label {Label : Type*}
    (s : Label→ SecondBlockSource) (r : SecondRow s) :
    secondResidualIdeals s r=(s r.1).divisors.filter Squarefree := by
  ext L
  simp only [mem_second_residual_ideals,Finset.mem_filter]

/-- Fix the source label, both rays and residual ideal before summing the
entire physical live-row column. This is an exact finite-sum identity. -/
theorem actual_second_column_reindex {Label β : Type*} [Fintype Label]
    [AddCommMonoid β] (s : Label→ SecondBlockSource)
    (f : SecondRow s→ Ideal O→β) :
    (∑r∈secondLiveRows s,∑D∈secondResidualIdeals s r,f r D)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(s l).divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (s l),f ⟨l,χ,ψ,z⟩ D := by
  have hrows : (∑r∈secondLiveRows s,∑D∈secondResidualIdeals s r,f r D)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑z∈secondLiveColumnRows (s l),
          ∑D∈(s l).divisors.filter Squarefree,f ⟨l,χ,ψ,z⟩ D := by
    simp only [actual_second_residual_ideals_label,secondLiveRows,
      secondLiveColumnRows,Finset.sum_filter,Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [hrows]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  exact Finset.sum_comm

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- The left normalized energy is a sum of complete row columns at a
fixed divisor and pair of rays. Its source weight stays inside the identity. -/
theorem actual_second_left_normalized_column_reindex
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
            ((d r.1).input.t+2*Real.pi*(u-t)))
            (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (d l).block,
            (‖w l‖*(d l).block.outside*volume (d l).input.toData)*
              ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-t)))
                (d l).C (d l).hC (d l).R (d l).seed D z.val‖^2 := by
  exact actual_second_column_reindex (fun l=>(d l).block) _

/-- The right energy uses the original live-row filter and the literal
negated Fourier row. No closure of the input row set under negation is assumed. -/
theorem actual_second_right_normalized_column_reindex
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
            ((d r.1).input.t+2*Real.pi*(u-(-t))))
            (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (d l).block,
            (‖w l‖*(d l).block.outside*volume (d l).input.toData)*
              ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
                ((d l).input.t+2*Real.pi*(u-(-t))))
                (d l).D (d l).hD (d l).R (d l).seed D (-z.val)‖^2 := by
  exact actual_second_column_reindex (fun l=>(d l).block) _

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_residual_ideals_label
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_column_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_left_normalized_column_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_right_normalized_column_reindex

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondColumnReindex -/
