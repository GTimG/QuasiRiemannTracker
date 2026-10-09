import OAI.NumberTheory.DirichletL.Reflection.LowCompletedRows
import QRH.Detector.LowReflectedLength
import QRH.Reflection.LowCompletedFiber

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Exact optimized parent width and retained slot allowance; reflected energy penalty
is carried explicitly. Actual phase, common coefficients and puncture objects unchanged. -/
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_rows_energy_optimized (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤QRH.ell → 0≤ell0 → ell0≤QRH.ell-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(QRH.M-2*d)) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((QRH.M-2*d)+QRH.lowPenalty d+507*η) := by
  have hQRHell : 0 < QRH.ell ∧ QRH.ell < (1/5:ℝ) := by norm_num [QRH.ell, QRH.theta]
  have hQRHM : (49/100:ℝ) + 2*QRH.ell < QRH.M ∧ QRH.M ≤ 1 := by
    norm_num [QRH.M, QRH.ell, QRH.theta]
  obtain ⟨hQRHMlower, hQRHMupper⟩ := hQRHM
  have hQRHsum : QRH.M + QRH.ell = 1 := by simp [QRH.M]

  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_fiber_energy_optimized Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation 2 η (by norm_num) hη
  let mask := Ideal.span {m}*F
  let Z₁ := max Z₀ (max 2 (max Ck (Ideal.absNorm mask:ℝ)))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskZ : (Ideal.absNorm mask:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskn : (Ideal.absNorm mask:ℝ)≤Z^(2:ℝ) := hmaskZ.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hz1 (show (1:ℝ)≤2 by norm_num))
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2:ℝ) := by
    intro I hI
    refine ⟨(hparents I hI).1,(hparents I hI).2.trans ?_⟩
    calc
      _ ≤ Z*Z^(QRH.M-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(QRH.M-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hh := ha Z hZ2 parents mask hparentn
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^((QRH.M-2*d)+QRH.lowPenalty d+506*η))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J (hparents J hJ).1 Z d ell0 shift
      hZZ hd hd1 hell hellcap hshift (hparents J hJ).2
      parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^η*Z^((QRH.M-2*d)+QRH.lowPenalty d+506*η)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
