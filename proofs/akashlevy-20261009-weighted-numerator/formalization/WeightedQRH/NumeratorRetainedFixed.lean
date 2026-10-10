import WeightedQRH.NumeratorCertifiedRetained
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.WeightedNumeratorReflection
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 800000

lemma eventually_retained_log_cost (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠU:ℝ in atTop, 1 < U ∧ ∀n:ℝ, 0 ≤ n → n ≤ 2 →
      (1+2*(n*Real.log U))^2 ≤ 25*U^(loss/2) := by
  have hlog := (isLittleO_log_rpow_atTop (by linarith:0 < loss/4)).bound (by norm_num:(0:ℝ)<1)
  filter_upwards [hlog,eventually_gt_atTop (1:ℝ)] with U hlog hU
  have hUpos := zero_lt_one.trans hU
  have hlog0 := (Real.log_pos hU).le
  have hh : Real.log U ≤ U^(loss/4) := by
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hUpos.le _)] using hlog
  refine ⟨hU,?_⟩
  intro n hn hn2
  have hpow : 1 ≤ U^(loss/4) := Real.one_le_rpow hU.le (by linarith)
  have hbase : 1+2*(n*Real.log U) ≤ 5*U^(loss/4) := by
    have hm := mul_le_mul_of_nonneg_right hn2 hlog0
    nlinarith
  have hnonneg : 0 ≤ 1+2*(n*Real.log U) := by positivity
  calc
    _ ≤ (5*U^(loss/4))^2 := pow_le_pow_left₀ hnonneg hbase 2
    _ = _ := by
      rw [mul_pow,←Real.rpow_natCast (U^(loss/4)) 2,←Real.rpow_mul hUpos.le]
      norm_num
      congr 1
      ring

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem certified_retained_fixed_profile {D : WeightedQRH.MomentData}
    (F : ProbeFinalAssembly.WeightedSourceData D) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
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
      (∀i, width i ≤ CenteredMomentEnergyWidthRanges.fineMesh 2 0 1 (3/4) (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      (2*(m+xi)+6*(3/4)*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := certified_actual_retained_fourth F hbeta (loss/2) Cscale xi
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
    hw hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=>G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end SevenEighths.WeightedNumeratorReflection
end
end OAI
