/- Copyright (c) 2026 Sil. Apache-2.0.
Full-source reflected restoration; adapted from PR69 PhysicalDirect/Retained
and Fixed, retaining Gao/OpenAI/Hailey Collet attribution. Generic primitive
restoration, scale geometry and logarithmic absorption are reused unchanged.
No old Geometry.Bounds or PhysicalSchedule is assumed. 
-/
import Candidate.FourthPower.ReturnPhysicalFourier
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.RetainedGeometry
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.RetainedFixed
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
namespace Candidate.FourthPower.ReturnPhysicalRetained
open ReturnCertificate ReturnPhysicalInput ReturnPhysicalSchedule ReturnPhysicalFourier

open OAI OAI.SevenEighths
open Cycle25WeightedNumeratorReflection
open Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowWindow CenteredMomentNaturalPrimitive
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 200000

/-- Certified fourth moment of the actual natural primitive restoration. The
original scale X, presentation τ, primitive ψ and profile may vary independently
with the row. All dependence on that choice is controlled by the combined
conductor/scale bound and the stated profile seminorm. The selected family can
also be empty, in which case the zero-slot endpoint covers lengths up to U². -/
theorem full_actual_retained_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bΦ mesh affineError U di control Ci)
    (epsilon Cscale xi : ℝ) (hepsilon : 0 < epsilon) (hCscale : 0 < Cscale) (hxi : 0 < xi) :
    ∃degree:ℕ, ∃H:Finset (ℕ×ℕ), ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (G:rows→𝓢(ℝ,ℂ)) (X:rows→ℝ) (m B Rcap:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 → 0 < B →
      (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ B) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Rcap) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i,width i≤ mesh) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ((∃d t:ℝ,ds≤ d ∧ d≤ dplus ∧
        0≤ t ∧ t≤ shiftCutoff ∧ m+xi=shiftedPlain d t ∧
        (∑i,width i)≤ shiftedWidth d t) ∨
        (2*(m+xi)+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*
          (1+height)^degree*U^(1+D.t+affineError) := by
  obtain ⟨degree,Jp,Cp,hCp,hpositive⟩:=full_hybrid_fourier F κ hκlo hκhi hbeta hκbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 Jp (by norm_num)
  refine ⟨degree,H,Cr*Cp,by positivity,?_⟩
  filter_upwards [hpositive,eventually_retained_log_interval Cscale xi hCscale hxi]
    with U hp hg
  have hκpos : 0 < κ := by linarith
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m B Rcap he hX hm hmmax hB hG hRcap hR
    hcombined T width z height hw hwmesh hwmax hreal hheight hzim hcapacity
  let n := m+xi
  have hn : 0 ≤ n := by dsimp [n]; linarith
  let P (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let E := Cp*(1+height)^degree*U^(1+D.t+affineError)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinterval : 0 ≤ n*Real.log U := mul_nonneg hn (Real.log_pos hU).le
  have hgeom (i:rows) (a:CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes (τ i) (ψ i)))
      (hY:0 < dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
      (ha:a.2∈CenteredMomentReflectedTruncation.retainedAnnuli (U^(xi/4))
        (dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2) hY) :
      Real.log (dyadicScale a.2*dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
        ∈ Set.Icc 0 (n*Real.log U) := hg.2 (τ i) (ψ i) (X i) m (hX i) (hcombined i) a hY ha
  have hpoly (i:rows) (W:ℝ→ℂ) (x freq:ℝ) :
      polynomial (τ i).inverse false W x 0 freq =
        polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false W x 0 freq :=
    (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _
      (Cycle25.Weighted.RowConductor.inverse_elementCoeff_eq _ _ (he i)) false W x 0 freq).symm
  have hmoment (v w:ℝ) (j k:Fin 2) (x:ℝ) (hx:x∈Set.Icc 0 (n*Real.log U))
      (y:ℝ) (hy:y∈Set.Icc 0 (n*Real.log U)) :
      (∑i:rows, ‖polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (2*Real.pi*v) *
        polynomial (τ i).inverse false (scaleTest (fun z:ℝ=>(annulus z:ℂ)) k)
        (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
        ≤ E*((1+‖v‖)^Jp)^2*((1+‖w‖)^Jp)^2 := by
    have hxlen := reflection_window_length U n x hU hn hx
    have hylen := reflection_window_length U n y hU hn hy
    simp_rw [hpoly]
    have hb:=hp.2 rows hrows T width z height n hw hwmesh hwmax hreal hheight hzim
      hn hmmax hcapacity (Real.exp x) (Real.exp y) (Real.exp_pos _) (Real.exp_pos _)
      hxlen.2 hylen.2 hxlen.1 hylen.1 j k v w
    rw [←Finset.sum_coe_sort rows] at hb
    simpa only [P,E] using hb
  have hresult := hretained G τ ψ P X (fun _=>U^(xi/4)) 0 (n*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hresult using 1 <;> dsimp [E,n] <;> ring


open QuadraticInitialBound

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem full_retained_fixed_profile {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,FullPhysicalAt F bΦ mesh affineError U di control Ci)
    (G:𝓢(ℝ,ℂ)) (loss Cscale Ccond xi:ℝ)
    (hloss:0 < loss) (hCscale:0 < Cscale) (hCcond:0 < Ccond) (hxi:0 < xi) :
    ∃degree:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (X:rows→ℝ) (m:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i,width i≤ mesh) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ((∃d t:ℝ,ds≤ d ∧ d≤ dplus ∧
        0≤ t ∧ t≤ shiftCutoff ∧ m+xi=shiftedPlain d t ∧
        (∑i,width i)≤ shiftedWidth d t) ∨
        (2*(m+xi)+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := full_actual_retained_fourth F κ hκlo hκhi hbeta hκbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput (loss/2) Cscale xi
    (by linarith) hCscale hxi
  let B := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  let K := max 1 Ccond
  have hB : 0 < B := by have := apply_nonneg (H.sup (schwartzSeminormFamily ℝ ℝ ℂ)) G; dsimp [B]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨degree,25*Cr*K^(loss/2)*B^4,by positivity,?_⟩
  filter_upwards [hr,eventually_retained_log_cost loss hloss] with U hr hl
  have hU := hr.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ X m he hX hm hmmax hred hcombined T width z height
    hw hwmesh hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=>G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmesh hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t+affineError) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t+affineError)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring


end Candidate.FourthPower.ReturnPhysicalRetained
