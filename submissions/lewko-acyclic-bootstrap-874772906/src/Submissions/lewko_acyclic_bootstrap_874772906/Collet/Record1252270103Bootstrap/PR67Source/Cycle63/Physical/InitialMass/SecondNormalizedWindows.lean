import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEffectiveScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointWindowFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve Cycle63Moment
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
    (rows : Finset κ) (slots : κ→Finset α) (s : (k : κ)→ Input (slots k))
    (C R seed L : κ→ Ideal O) (hC : ∀k,Supported (C k)) (η : κ→ Character)
    (t θ X : κ→ℝ) (hX : ∀k,0<X k) (z : κ→O) (weight : κ→ℝ)
    (hw : ∀k,0≤weight k) (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤E)
    (he : ∀u : ℝ,(∑k∈rows,weight k*‖normalizedColumn
      (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
      (C k) (hC k) (R k) (seed k) (L k) (z k)‖^2)≤E*(1+‖u‖)^(2*J)) :
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
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t : ℝ) (J : ℕ)
    (Eleft Eright : ℝ) (hEl : 0≤Eleft) (hEr : 0≤Eright)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus)
    (hl : ∀u : ℝ,(∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
          ((d r.1).input.t+2*Real.pi*(u-t)))
          (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L r.2.2.2.val‖^2)≤Eleft*(1+‖u‖)^(2*J))
    (hr : ∀u : ℝ,(∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
          ((d r.1).input.t+2*Real.pi*(u-(-t))))
          (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L (-r.2.2.2.val)‖^2)≤Eright*(1+‖u‖)^(2*J)) :
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
  have hw (r) : 0≤weight r := mul_nonneg
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
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (W : SchwartzMap ℝ ℂ)
    (hcard : Fintype.card α≤N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0 → ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0 → ap≤x)
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
