import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondNormalizedWindows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRatioCap
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter MeasureTheory HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentLogDyadic CenteredMomentOriginalCommonHarmonic CenteredMomentSecondLocalization
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondLiveBlock
open CenteredMomentActiveSource CenteredMomentFirstSectors CenteredMomentSourceRow
open Cycle63Moment RayFourExpansion CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceMass CenteredMomentSecondActivePhysicalDictionary
local instance secondRestrictedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Change only the physical row set. The original input, character family,
Fourier scale and dyadic block coordinates remain literal. -/
def ordinarySecondDatum (d : SecondInputDatum α) (χ : RayCharacter) (Q : Ideal O) (m : O) :
    SecondInputDatum α :=
  {d with
    rows:=partRows false d.input.η χ Q m d.C d.D d.inactive d.radius
    rows_ne:=fun z hz=>sourceRows_nonzero d.C d.D d.inactive d.radius z
      (Finset.mem_filter.mp hz).1}

@[simp] theorem ordinary_second_dyad (d : SecondInputDatum α)
    (χ : RayCharacter)(Q : Ideal O)(m : O)(i : Fin 4) :
    (ordinarySecondDatum d χ Q m).block.dyad i=d.block.dyad i := rfl

@[simp] theorem ordinary_second_ratio (d : SecondInputDatum α)
    (χ : RayCharacter)(Q : Ideal O)(m : O) :
    secondRatioIndex (ordinarySecondDatum d χ Q m).block=secondRatioIndex d.block := rfl

/-- The two full positive normalized sums, on the rows of the supplied
restricted datums. Residual ideals and all source labels stay in the sum. -/
def secondNormalizedSum {Label : Type*}[Fintype Label]
    (reflected : Bool)(d : Label→SecondInputDatum α)(w : Label→ℂ)(t u : ℝ) : ℝ :=
  ∑r∈secondLiveRows (fun l=>(d l).block),
    ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
      (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        (if reflected then
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
            ((d r.1).input.t+2*Real.pi*(u-(-t))))
            (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L (-r.2.2.2.val)‖^2
         else
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
            ((d r.1).input.t+2*Real.pi*(u-t)))
            (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L r.2.2.2.val‖^2)

lemma normalized_balance_sqrt (E H T : ℝ)(hE : 0≤E)(hH : 0<H)(hT : 0≤T) :
    Real.sqrt (E*H*T)*Real.sqrt (E/H*T)=E*T := by
  rw [←Real.sqrt_mul (mul_nonneg (mul_nonneg hE hH.le) hT)]
  have heq : E*H*T*(E/H*T)=(E*T)^2 := by field_simp
  rw [heq,Real.sqrt_sq_eq_abs,abs_of_nonneg (mul_nonneg hE hT)]

/-- Literal full positive normalized sums on every exact ratio fiber. -/
def SecondNormalizedBound {Label : Type*}[Fintype Label]
    (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E H : ℤ→ℝ) : Prop :=
  ∀r∈secondRatioBins (fun l=>(d l).block),∀(reflected : Bool)(t u : ℝ),
        let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val;
        let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block;
        let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val;
        secondNormalizedSum reflected datum (secondEffectiveWeight src weight W) t u≤
          ((if reflected then E r/H r else E r*H r)*(1+‖t‖)^degree)*
            (1+‖u‖)^(2*windowDegree)

/-- Joint restricted physical block contraction from literal positive sums
on each exact ratio fiber. Constants precede the moving datum family. -/
theorem restricted_second_ratio_from_normalized (W : 𝓢(ℝ,ℂ))(A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E H : ℤ→ℝ),
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
      SecondNormalizedBound W degree windowDegree d w E H →
      ‖∑l,w l*(d l).block.value W‖≤
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hcon⟩:=actual_second_ratio_contraction W A degree
  let IL:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hs u‖|
  let IR:=|∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hs) u‖|
  refine ⟨C*IL*IR,by dsimp [IL,IR];positivity,?_⟩
  intro Label _ d w E H hE hH hnorm
  have hh:=hcon (fun l=>(d l).block) w (fun r=>E r*IL*IR)
    (fun r hr=>by have he:=hE r hr; dsimp [IL,IR];positivity) ?_
  · apply hh.trans_eq
    simp_rw [show ∀ r : ℤ, E r*IL*IR/(1+dyadicScale r)^A =
      E r/(1+dyadicScale r)^A*IL*IR by intro r; ring]
    rw [←Finset.sum_mul,←Finset.sum_mul]
    ring
  · intro r hr t
    let datum:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val
    let src:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>(datum l).block
    let weight:=fun l : SecondRatioFiber (fun l=>(d l).block) r=>w l.val
    let ew:=secondEffectiveWeight src weight W
    have hleft:=hnorm r hr false t
    have hright:=hnorm r hr true t
    have hEt : 0≤E r*H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hEr : 0≤E r/H r*(1+‖t‖)^degree := by have he:=hE r hr; have hh:=hH r hr; positivity
    have hb:=actual_balanced_energy_from_normalized datum ew t windowDegree
      (E r*H r*(1+‖t‖)^degree) (E r/H r*(1+‖t‖)^degree) hEt hEr hc hs
      (fun u=>by simpa only [secondNormalizedSum,Bool.false_eq_true,ite_false] using hleft u)
      (fun u=>by simpa only [secondNormalizedSum,ite_true] using hright u)
    rw [normalized_balance_sqrt (E r) (H r) ((1+‖t‖)^degree) (hE r hr) (hH r hr)
      (by positivity)] at hb
    exact hb.trans_eq (by dsimp [IL,IR];ring)

/-- Ordinary restriction leaves the exact ratio image unchanged. -/
@[simp] theorem ordinary_second_ratio_bins {Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α)(χ : Label→RayCharacter)
    (Q : Label→ Ideal O)(m : Label→O) :
    secondRatioBins (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)=
      secondRatioBins (fun l=>(d l).block) := rfl

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
