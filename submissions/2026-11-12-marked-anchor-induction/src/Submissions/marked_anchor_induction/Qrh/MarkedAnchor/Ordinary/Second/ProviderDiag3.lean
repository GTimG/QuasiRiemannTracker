/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: absorption of the root constants into the `Z^{3ε}` loss.

* `habsf_of_sizes`: the `habs` input of `hrootf_of_margin` from the root sizes (counting,
  multiplicities, conductor powers, `log X`) and a single eventual absorption inequality.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstMixedAllowance
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional
open CenteredMomentCanonicalFirst EisensteinSchwartzPoisson CenteredMomentCompleteCommon
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedPrincipalCentered MixedCommonCoefficient MixedFirstLiveSource MixedOriginalTail
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedFirstExceptionalNormalization
open MixedFirstExceptionalWindow MixedFirstAllocatedRemainders MixedOriginalNormCap
open MixedFirstProfileEnvelope RepairedSourceSideSupply RepairedRawContext
open Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem rpow_freqLoss (Z κ : ℝ) (hZ : 1 < Z) :
    Z^(5*(frequencyLoss Z 1 κ + κ)/6) = (4:ℝ)^(5/6:ℝ)*Z^(5*κ/4) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  unfold frequencyLoss
  rw [show 5*(κ/2 + Real.logb Z (4*1) + κ)/6 = Real.logb Z 4*(5/6) + 5*κ/4 by ring_nf,
    Real.rpow_add hz, Real.rpow_mul hz.le, Real.rpow_logb hz hZ.ne' (by norm_num)]

theorem log_le_of_rpow (X Z BX : ℝ) (hZ : 1 < Z) (hX1 : 1 ≤ X) (hX : X ≤ Z^BX) :
    Real.log X ≤ BX*Real.log Z := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc Real.log X ≤ Real.log (Z^BX) := Real.log_le_log (zero_lt_one.trans_le hX1) hX
    _ = BX*Real.log Z := Real.log_rpow hz _

/-- Eight-factor monotonicity (generic). -/
theorem absorb_chain (c2 y1 A1 B1 R2 A2 A3 B3 A4 B4 sl slb A5 : ℝ) (hc2 : 0 ≤ c2) (h1 : c2 ≤ y1)
    (hA1 : 0 ≤ A1) (h2 : A1 ≤ B1) (hR2 : 0 ≤ R2) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (h3 : A3 ≤ B3)
    (hA4 : 0 ≤ A4) (h4 : A4 ≤ B4) (hsl : 0 ≤ sl) (h5 : sl ≤ slb) (hA5 : 0 ≤ A5) :
    c2*A1*R2*A2*A3*A4*sl*A5 ≤ y1*B1*R2*A2*B3*B4*slb*A5 := by
  have hy1 := hc2.trans h1
  have hB1 := hA1.trans h2
  have hB3 := hA3.trans h3
  have hB4 := hA4.trans h4
  have e1 : c2*A1 ≤ y1*B1 := mul_le_mul h1 h2 hA1 hy1
  have e2 : c2*A1*R2*A2 ≤ y1*B1*R2*A2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e1 hR2) hA2
  have n2 : 0 ≤ y1*B1*R2*A2 := mul_nonneg (mul_nonneg (mul_nonneg hy1 hB1) hR2) hA2
  have e3 : c2*A1*R2*A2*A3 ≤ y1*B1*R2*A2*B3 := mul_le_mul e2 h3 hA3 n2
  have n3 : 0 ≤ y1*B1*R2*A2*B3 := mul_nonneg n2 hB3
  have e4 : c2*A1*R2*A2*A3*A4 ≤ y1*B1*R2*A2*B3*B4 := mul_le_mul e3 h4 hA4 n3
  have n4 : 0 ≤ y1*B1*R2*A2*B3*B4 := mul_nonneg n3 hB4
  have e5 : c2*A1*R2*A2*A3*A4*sl ≤ y1*B1*R2*A2*B3*B4*slb := mul_le_mul e4 h5 hsl n4
  exact mul_le_mul_of_nonneg_right e5 hA5

theorem absorb_eq (Cc z1 pM KN k CM z2 R2 Kc z3 Cs z4 BX lZ fq Pb z5 Ar c16 aa slb c92 c2N c4 z6 : ℝ) :
    (Cc*z1)*(pM*KN*k*(CM*z2))*R2*(Kc*z3*(Cs*z4))*(2304*(BX*lZ))*(fq*(Pb*z5*Ar)*c16*aa)*slb*
      (c92*c2N*(c4*z6)) =
    (Cc*pM*KN*k*CM*R2*Kc*Cs*(2304*BX)*(fq*c16*aa)*Pb*slb*(c92*c2N*c4))*lZ*
      (z1*z2*z3*z4*z5*z6)*Ar := by ring

/-- **The exceptional absorption** (`habs` of `hrootf_of_margin`). -/
theorem habsf_of_sizes (s : Source ι a b) (hd : s.d = (1,1)) (t₀ V : ℝ) (hV : 0 ≤ V)
    (J JL : ℕ) (hJ : 2*JL ≤ J) (cL control : Finset (ℕ×ℕ)) (hc : cL ⊆ control)
    (Z εL Cside θf ε : ℝ) (hZ : 1 < Z) (hCs : 0 < Cside)
    (card Cc eC pM Mc CM eM R2 Kc Bδ Csum εs X BX κ Kslot : ℝ) (Nm : ℕ) (Q : Id)
    (hCc : 0 ≤ Cc) (hCM : 0 ≤ CM) (hBX : 0 ≤ BX)
    (hcard : card^2 ≤ Cc*Z^eC) (hpM : 0 ≤ pM) (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ CM*Z^eM)
    (hR2 : 0 ≤ R2) (hKc : 0 ≤ Kc) (hCsum : 0 ≤ Csum) (hX1 : 1 ≤ X) (hX : X ≤ Z^BX)
    (hcardι : Fintype.card ι ≤ Nm) (hM : ∀ i, s.M i ≤ Kslot) (hK : 1 ≤ Kslot) (ha : 0 < a)
    (habsorb : (Cc*pM*(Kslot^Nm)^2*(1024:ℝ)^Nm*CM*R2*Kc*Csum*(2304*BX)*
        (fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*(((1024:ℝ)^Nm*(Kslot^Nm)^3)^2)*
        ((Kslot^Nm)^2*((2:ℝ)^Nm)^(4/3:ℝ))*((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*(4:ℝ)^(5/6:ℝ)))*
        (Real.log Z + 1)*Z^(eC+eM+Bδ+εs+2*εL+5*κ/4) ≤ θf*Cside*Z^(3*ε)) :
    card^2*(pM*(∏ i, s.M i)^2*(1024:ℝ)^Nm*Mc)*R2*(Kc*Z^Bδ*(Csum*Z^εs))*(2304*Real.log X)*
      (fixedQCost Q*(sourceProfile s JL cL Z εL)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*slotCost s*
      ((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*Z^(5*(frequencyLoss Z 1 κ + κ)/6)) ≤
    θf*amplitude s t₀ V J control Cside*Z^(3*ε) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hlogZ := Real.log_nonneg hZ.le
  have hlogX := Real.log_nonneg hX1
  have hK0 : 0 ≤ Kslot := zero_le_one.trans hK
  have hA0 := amplitude_nonneg s t₀ V hV J control Cside hCs.le
  have hAC : 0 ≤ amplitude s t₀ V J control Cside/Cside := div_nonneg hA0 hCs.le
  have hsP := sourceProfile_sq_le_amplitude s t₀ V hV JL J hJ cL control hc Z εL Cside hz.le hCs
  have hfm := fullMarkedCost_le s Kslot Nm hcardι hM hK
  have hfm0 := fullMarkedCost_nonneg s
  have hsP' : (sourceProfile s JL cL Z εL)^2 ≤
      ((1024:ℝ)^Nm*(Kslot^Nm)^3)^2*Z^(2*εL)*(amplitude s t₀ V J control Cside/Cside) :=
    hsP.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hfm0 hfm 2) (Real.rpow_nonneg hz.le _)) hAC)
  have hslot := slotCost_le_unit s hd Kslot Nm hcardι hM hK
  have hP1 := prodM_ge s
  have hMall := pow_le_pow_left₀ (zero_le_one.trans hP1) (prodM_le s Kslot Nm hcardι hM hK) 2
  have hlog := log_le_of_rpow X Z BX hZ hX1 hX
  have hfq := fixedQCost_nonneg Q
  have hsl0 := slotCost_nonneg s
  have hZB := Real.rpow_nonneg hz.le Bδ
  have hZs := Real.rpow_nonneg hz.le εs
  have h16 : (0:ℝ) ≤ (16:ℝ)^(5/6:ℝ) := Real.rpow_nonneg (by norm_num) _
  have haa : (0:ℝ) ≤ a^(-4/3:ℝ) := Real.rpow_nonneg ha.le _
  have hc92 : (0:ℝ) ≤ (9/2:ℝ)^(2/3:ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : (0:ℝ) ≤ (4:ℝ)^(5/6:ℝ) := Real.rpow_nonneg (by norm_num) _
  have h2N : (0:ℝ) ≤ ((2:ℝ)^Nm)^(4/3:ℝ) := Real.rpow_nonneg (by positivity) _
  have hZk := Real.rpow_nonneg hz.le (5*κ/4)
  rw [rpow_freqLoss Z κ hZ]
  have hchain := absorb_chain (card^2) (Cc*Z^eC) (pM*(∏ i, s.M i)^2*(1024:ℝ)^Nm*Mc)
    (pM*(Kslot^Nm)^2*(1024:ℝ)^Nm*(CM*Z^eM)) R2 (Kc*Z^Bδ*(Csum*Z^εs)) (2304*Real.log X)
    (2304*(BX*Real.log Z))
    (fixedQCost Q*(sourceProfile s JL cL Z εL)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))
    (fixedQCost Q*(((1024:ℝ)^Nm*(Kslot^Nm)^3)^2*Z^(2*εL)*(amplitude s t₀ V J control Cside/Cside))*
      (16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))
    (slotCost s) ((Kslot^Nm)^2*((2:ℝ)^Nm)^(4/3:ℝ))
    ((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*((4:ℝ)^(5/6:ℝ)*Z^(5*κ/4)))
    (sq_nonneg _) hcard (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMall hpM) (by positivity)) hMc0 |>.trans
      (mul_le_mul_of_nonneg_left hMc (by positivity)))
    hR2 (by positivity) (by positivity) (by linarith)
    (by have := sq_nonneg (sourceProfile s JL cL Z εL); positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsP' hfq) h16) haa)
    hsl0 hslot (by positivity)
  refine hchain.trans ?_
  rw [absorb_eq]
  have hzz : Z^eC*Z^eM*Z^Bδ*Z^εs*Z^(2*εL)*Z^(5*κ/4) = Z^(eC+eM+Bδ+εs+2*εL+5*κ/4) := by
    simp only [Real.rpow_add hz]
  rw [hzz]
  set Kf := Cc*pM*(Kslot^Nm)^2*(1024:ℝ)^Nm*CM*R2*Kc*Csum*(2304*BX)*
        (fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*(((1024:ℝ)^Nm*(Kslot^Nm)^3)^2)*
        ((Kslot^Nm)^2*((2:ℝ)^Nm)^(4/3:ℝ))*((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*(4:ℝ)^(5/6:ℝ)) with hKf
  have hKf0 : 0 ≤ Kf := by rw [hKf]; positivity
  set e := eC+eM+Bδ+εs+2*εL+5*κ/4 with he
  have hZe := Real.rpow_nonneg hz.le e
  have hstep2 : Kf*Real.log Z*Z^e ≤ θf*Cside*Z^(3*ε) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hKf0) hZe).trans habsorb
  calc Kf*Real.log Z*Z^e*(amplitude s t₀ V J control Cside/Cside) ≤
        (θf*Cside*Z^(3*ε))*(amplitude s t₀ V J control Cside/Cside) :=
        mul_le_mul_of_nonneg_right hstep2 hAC
    _ = θf*amplitude s t₀ V J control Cside*Z^(3*ε) := by field_simp

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
