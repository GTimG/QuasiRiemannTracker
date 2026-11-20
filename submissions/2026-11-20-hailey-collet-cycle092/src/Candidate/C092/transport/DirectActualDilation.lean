/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual Q-source weighted first integral. The source, reflected numerator and
prime amplitudes retain the provenance of DirectActualFourth. -/
import Candidate.C092.transport.DirectActualIntegral
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter MeasureTheory
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator
namespace QRH.Cycle092.DirectEnergy

theorem q_original_dilation_first
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (hAffineError : 0 < affineError) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ (D : Cycle25.Weighted.MomentData)
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
      (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ)
      (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ),
      0 < loss → 0 < xi → 0 < b → 0 < Cslot →
      ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
        (data : Ω → ∀ i : rows, PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : Ω → rows → ℝ) (Y : Ω → ℝ) (m : ℝ),
      (∀ t, 0 < Y t) → (∀ t i, 0 < N t i ∧ N t i ≤ b*Y t) →
      0 ≤ m → m+xi ≤ 2 →
      (∀ t i, (data t i).combinedConductor ≤
        (fixedConductorConstant F.S : ℝ)*U^m*(Y t/N t i)) →
      ∀ (T : Finset (Fin D.N)) (width : T → ℝ) (z : Ω → T → ℂ) (height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ mesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀ t i, (z t i).re=17/50) → 0 ≤ height →
      (∀ t i, |(z t i).im| ≤ height) →
      (((∑ i, width i) ≤ QRH.Cycle090.physicalCap ∧
        2*(m+xi)+(2+10*QRH.Cycle090.sourceCost)*(∑ i,width i) ≤ 1-QRH.Cycle090.sourceCost) ∨
        (2*(m+xi)+6*κ*(∑ i,width i) ≤ 1 ∨ T=∅)) →
      (∀ t (i : rows), ‖primeProduct F U width (z t) i‖ ≤ Cslot*U^q) →
      ∀ (J : Type) [Fintype J] (fullWidth : J → ℝ) (fullZ : Ω → J → ℂ)
        (K : Ω → ℂ) (R y source d qamp ell v xiD ann delta ampLoss Ccount : ℝ),
      0 ≤ source → 0 ≤ qamp → qamp ≤ delta/2 → 0 ≤ v → 0 ≤ xiD → 0 ≤ ann →
      1 ≤ Ccount → (rows.card : ℝ) ≤ Ccount*U^R → Integrable K μ →
      (∀ t (i : rows), U^(qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity
        y source d (2*(v+xiD+ann))-ampLoss) ≤ ‖primeProduct F U width (z t) i‖) →
      (∀ t (i : rows), ‖primeProduct F U fullWidth (fullZ t) i‖ ≤ U^(qamp*ell)) →
      U^(-delta*v/2)*‖∫ t, K t*(∑ i : rows,
        originalRow F G (N t) (Y t) i * primeProduct F U fullWidth (fullZ t) i) ∂μ‖ ≤
        Ccount*(max 1 C*(1+height)^degree)*
          U^(qamp*ell-qamp*QRH.Cycle092.Physical.Selection.zeroCapacity y source d/2+
            (3*R+1+(D.t+affineError+loss))/4+ampLoss/2+delta*(xiD+ann)/2-
            2*(1/1000 : ℝ)*delta*(v+xiD+ann))*(∫ t, ‖K t‖ ∂μ) := by
  obtain ⟨mesh,hm,hfirst⟩ := q_original_amplitude_first hβ affineError hAffineError
  refine ⟨mesh,hm,?_⟩
  intro D F κ hκlo hκhi hκβ G loss xi q b Cslot hloss hxi hb hCslot
  obtain ⟨degree,C,hC,hU⟩ := hfirst D F κ hκlo hκhi hκβ G loss xi q b Cslot
    hloss hxi hb hCslot
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hU] with U hU
  refine ⟨hU.1,?_⟩
  intro rows hrows Ω _ μ data N Y m hY hN hm hmxi hcond T width z height
    hwidth hmesh hcommon hz hheight hzim hgate hslot J _ fullWidth fullZ K R y source d
    qamp ell v xiD ann delta ampLoss Ccount hsource hq hqdelta hv hxiD hann
    hcount hcard hK hselected hfull
  have hUpos : 0 < U := lt_trans zero_lt_one hU.1
  have hh := hU.2 rows hrows Ω μ data N Y m hY hN hm hmxi hcond T width z height
    hwidth hmesh hcommon hz hheight hzim hgate hslot J fullWidth fullZ K R (qamp*ell)
    (qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xiD+ann))-ampLoss)
    Ccount hcount hcard hK hselected hfull
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := QRH.Cycle092.Physical.Selection.capacity_damping
    (y:=y) (d:=d) hsource (by positivity : 0 ≤ 2*(v+xiD+ann)) hq hqdelta hdelta
  have hcoeff : 0 ≤ Ccount*(max 1 C*(1+height)^degree) := by
    have hc : 0 ≤ Ccount := le_trans zero_le_one hcount
    have hm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left 1 C)
    positivity
  have he : -delta*v/2+qamp*ell-
      (qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xiD+ann))-ampLoss)/2+
      (3*R+1+(D.t+affineError+loss))/4 ≤
      qamp*ell-qamp*QRH.Cycle092.Physical.Selection.zeroCapacity y source d/2+
      (3*R+1+(D.t+affineError+loss))/4+ampLoss/2+delta*(xiD+ann)/2-
      2*(1/1000 : ℝ)*delta*(v+xiD+ann) := by linarith
  calc
    _ ≤ U^(-delta*v/2)*(Ccount*(max 1 C*(1+height)^degree)*
      U^(qamp*ell-(qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d
        (2*(v+xiD+ann))-ampLoss)/2+(3*R+1+(D.t+affineError+loss))/4)*
      (∫ t, ‖K t‖ ∂μ)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hUpos.le _)
    _ = Ccount*(max 1 C*(1+height)^degree)*
      U^(-delta*v/2+qamp*ell-(qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity
        y source d (2*(v+xiD+ann))-ampLoss)/2+(3*R+1+(D.t+affineError+loss))/4)*
      (∫ t, ‖K t‖ ∂μ) := by
      rw [show -delta*v/2+qamp*ell-
        (qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d (2*(v+xiD+ann))-ampLoss)/2+
        (3*R+1+(D.t+affineError+loss))/4 = -delta*v/2+
        (qamp*ell-(qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d
          (2*(v+xiD+ann))-ampLoss)/2+(3*R+1+(D.t+affineError+loss))/4) by ring,
        Real.rpow_add hUpos (-delta*v/2)
          (qamp*ell-(qamp*QRH.Cycle092.Physical.Selection.scheduledCapacity y source d
            (2*(v+xiD+ann))-ampLoss)/2+(3*R+1+(D.t+affineError+loss))/4)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.1.le he) hcoeff)
      (integral_nonneg (fun _ => norm_nonneg _))
end QRH.Cycle092.DirectEnergy
#print axioms QRH.Cycle092.DirectEnergy.q_original_dilation_first
