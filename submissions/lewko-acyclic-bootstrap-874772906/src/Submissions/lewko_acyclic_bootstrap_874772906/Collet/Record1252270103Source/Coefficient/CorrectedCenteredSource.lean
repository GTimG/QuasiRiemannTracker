/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed-inducing centered control for the actual rational whole-pool amplifier
coefficient. All Newton children are discharged by the frozen source theorem. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedCenteredBound
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentAbsoluteEnergy
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => HeckeFamily.O

theorem corrected_centered_source_control_fractional
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀Z : ℝ,1≤Z →∀η χ ψ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^Bχ →Q≤ψ.modulus →InducedBy χ ψ →
      ∀m A z : O,goodLambda∣m →(2:O)∣m →
      (∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) →
      ∀A₁ A₂ D M : Ideal O,A₁≠0 →A₂≠0 →((A₁*A₂).absNorm:ℝ)≤Z^BA →
      ∀P : Finset (Ideal O),0<P.card →(∀p∈P,Prime p) →(∀p∈P,16≤p.absNorm) →
      (∀p∈P,(p.absNorm:ℝ)≤Z^Bpool) →(∀p∈P,¬p∣M) →
      2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      (∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
        frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→ rowWeight η m A z t (n.1*n.2)≠0→
        IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
          (idealDividingPool P (D*(M*n.1*n.2))).card<P.card) →
      ‖correctedCenteredRow P D M A₁ A₂ (rowWeight η m A z t) W₁ W₂ b X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*Real.sqrt T*L^(-α) := by
  obtain ⟨J,S,hS,hsource⟩ := frozen_squarefree_source_control_fractional
    a b ε Bχ (BA+depth*Bpool) α ha hb hε hBχ
      (add_nonneg hBA (mul_nonneg (Nat.cast_nonneg _) hBpool)) hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  have hm : 0≤newtonMassBound depth := by unfold newtonMassBound;positivity
  refine ⟨C*(1+newtonMassBound depth),mul_pos hC (by linarith),?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow A₁ A₂ D M
    hA₁ hA₂ hnormA P hP hp hN hpool havoid hbudget t X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY hsupport
  let base : ℝ:=C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J
  have hb0 : 0≤base := by
    dsimp only [base]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)) (by positivity)
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hbound := newton_centered_norm_bound P D M A₁ A₂ depth (rowWeight η m A z t)
    W₁ W₂ b X₁ X₂ Y₁ Y₂ T L α base hT hL (by linarith) hb0 hP hp hN
      (fun I=>rowWeight_norm_le_one_all η m A z t I) havoid hbudget hsupport ?_
  · apply hbound.trans
    have hscale : 0≤base*Real.sqrt T*L^(-α) := by positivity
    calc
      _≤(base*Real.sqrt T*L^(-α))*(1+newtonMassBound depth) :=
        mul_le_mul_of_nonneg_left (by linarith) hscale
      _=_ := by dsimp only [base];ring
  · intro S' hS' A' hA'
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1
    have hcard := (Finset.mem_filter.mp hS').2
    have hAS := Finset.mem_powerset.mp hA'
    let d:=newtonDivisorPair S' A'
    have hd : GoodPair d := newton_divisor_pair_good P S' A' hsub hAS hp hN
    have hn₁ := ideal_norm_one_le hd.1
    have hn₂ := ideal_norm_one_le hd.2.1
    have hlo₁ := divisor_common_lower L X₁ (d.1.absNorm:ℝ) d.2.absNorm hL.le hX₁ hn₁ hn₂
    have hlo₂ := divisor_common_lower L X₂ (d.2.absNorm:ℝ) d.1.absNorm hL.le hX₂ hn₂ hn₁
    have hly₁ := divisor_common_lower L Y₁ (d.1.absNorm:ℝ) d.2.absNorm hL.le hY₁ hn₁ hn₂
    have hly₂ := divisor_common_lower L Y₂ (d.2.absNorm:ℝ) d.1.absNorm hL.le hY₂ hn₂ hn₁
    rw [mul_comm (d.2.absNorm:ℝ) (d.1.absNorm:ℝ)] at hlo₂ hly₂
    exact hsource W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
      (A₁*d.1) (A₂*d.2) (mul_ne_zero hA₁ hd.1) (mul_ne_zero hA₂ hd.2.1)
      (newton_frozen_norm_bound P S' A' hsub hAS depth hcard A₁ A₂ Z BA Bpool hZ hBpool hnormA hpool)
      t _ _ _ _ _ _ (div_pos hL (pairNorm_pos hd.1 hd.2.1)) hlo₁ hlo₂ hly₁ hly₂
      (by rw [div_mul_div_comm,hpX];rfl) (by rw [div_mul_div_comm,hpY];rfl)

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_centered_source_control_fractional
