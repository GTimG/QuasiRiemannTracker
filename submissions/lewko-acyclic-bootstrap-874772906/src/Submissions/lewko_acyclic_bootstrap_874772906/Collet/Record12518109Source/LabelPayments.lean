/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.GeometryCones
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.LowLedger
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission
open OAI OAI.SevenEighths Record12518109Natural
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentSecondCanonical Cycle61Moment Cycle61InitialMass Cycle61HighGeometry
local notation "O" => HeckeFamily.O

/-- The LOW common term uses the original first numerator and cancelled
radical, and retains the complete balanced surplus. -/
theorem actual_label_raw_common (cell : Cell) (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) :
    globalRaw cell (actualFirstVector reflected l.1.1 l.1.2 Z)=
      rawCommon (labelR l Z)
        (max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6)
        (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
        (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
        (labelSurplus reflected l Z) cell.q cell.priorL (labelC reflected l Z)
        cell.priorB (labelD reflected l Z) := by
  rw [globalRaw,actualFirstVector_surplus,globalB_false]
  obtain ⟨hc,hd,hp,hr,hn,hn',ho,ho'⟩ := actualFirstVector_fields reflected l Z
  simp only [hc,hd,hr,hn,ho,rawCommon]

theorem actual_label_natural_common (cell : Cell) (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) :
    globalNatural cell (actualFirstVector reflected l.1.1 l.1.2 Z)=
      -(cell.q/Record12518109Admission.K)*min (labelC reflected l Z) (labelD reflected l Z)-
        max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6-
        labelSurplus reflected l Z := by
  rw [globalNatural,actualFirstVector_surplus,globalB_false]
  obtain ⟨hc,hd,hp,hr,hn,hn',ho,ho'⟩ := actualFirstVector_fields reflected l Z
  simp only [hc,hd,hr]

/-- HIGH's first-label common value is exactly the same normalized common
cost. The projector radical is still paid, not hidden in a density bound. -/
theorem actual_label_high_common (ν : ℝ) (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) :
    globalHigh ν (actualFirstVector reflected l.1.1 l.1.2 Z)=
      labelFirstCommon reflected l Z ν-labelSurplus reflected l Z+labelE l Z := by
  rw [globalHigh,actualFirstVector_surplus,globalB_false]
  obtain ⟨hc,hd,hp,hr,hn,hn',ho,ho'⟩ := actualFirstVector_fields reflected l Z
  simp only [hc,hd,hr,hn,ho]
  have hrho : Record12518109Admission.rho ν=LocalMoment.unmarkedDensity ν := rfl
  rw [hrho]
  simp only [labelFirstCommon,Valuation.firstCommon]
  ring

theorem high_scaled_identity (ν : ℝ) (v : Fin 8→ℝ) (h : d ν≠0) :
    globalHighScaled ν v=d ν*globalHigh ν v+(d ν*ν-etaD ν)*v 0 := by
  have hr : d ν*rho ν=rr ν := by
    unfold rho rr
    field_simp [h]
    <;> ring
  unfold globalHighScaled globalHigh
  linear_combination hr*(max (v 0-v 1) 0+v 3-v 4)

theorem actual_label_paired_payment (k : Fin 15) (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2)
    (Z : ℝ) (hZ : 1<Z) {ν₁ ν₂ : ℝ}
    (hν₁ : ν₁ ∈ Set.Icc (rawCells k).q (3/4)) (hν₂ : ν₂ ∈ Set.Icc (rawCells k).q (3/4)) :
    labelFirstCommon reflected l Z ν₁-labelSurplus reflected l Z+
      (labelFirstCommon (!reflected) l Z ν₂-labelSurplus (!reflected) l Z) ≤
      -gamma (rawCells k)*(labelC reflected l Z+labelD reflected l Z)-2*labelE l Z := by
  have hh := (actual_first_pair_payments k reflected l.1.1 l.1.2 hC hD heq Z hZ).2.2.2.2.1
    ν₁ ν₂ hν₁ hν₂
  rw [actualFirstVector_flip,actual_label_high_common,actual_label_high_common] at hh
  obtain ⟨hc,hd,hp,hr,hn,hn',ho,ho'⟩ := actualFirstVector_fields reflected l Z
  rw [hc,hd] at hh
  linarith only [hh]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.actual_label_raw_common
#print axioms QRH.Record12518109Source.actual_label_high_common
#print axioms QRH.Record12518109Source.high_scaled_identity
#print axioms QRH.Record12518109Source.actual_label_paired_payment
