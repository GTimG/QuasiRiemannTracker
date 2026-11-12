/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: the root margins of `diag_hbud` from a `RootInput`.

* `refexp_core`: the scalar heart of `hrootf`. With the root reference length
  `L ≥ L_ref = (2/9)·Z^ℓ` (`RootInput.hminimum`), the α-loss `refLoss` at `L_ref`, the selected
  width `W_max = 2^N·Z^{u_max}` and the input width `m ≥ 1`,
  `refLoss · Z^{referenceExponent(W_max)} · W_max^{2/3} ≤ (9/2)^{2/3}·8^N·Z^{5x/6}`
  follows from `RootInput.hmargin` (CF (7.1): `log V + 3u_max − 5/6 − α ℓ ≤ −9ω`).
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag`; `alphaP` is the fixed `D.alpha < 2/3`.
-/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteDiagAssembly3
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSideSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderLabelBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
noncomputable section

/-- **CF (7.1) in the exceptional ledger** (scalar form). -/
theorem refexp_core (Z L ell α uM lV m x ω : ℝ) (Nn : ℕ) (hZ : 1 < Z) (hL0 : 0 < L)
    (hLref : (2/9)*Z^ell ≤ L) (hell : 0 ≤ ell) (hα : α ≤ 2/3) (hm : 1 ≤ m)
    (hmargin : lV + 3*uM - 5/6 - α*ell ≤ -9*ω) (hω : 0 ≤ ω) :
    ((L/((2/9)*Z^ell))^(2/3:ℝ) * (max 1 ((2/9)*Z^ell))^((2/3:ℝ)-α)) *
      Z^(lV - 5*m/6 - 2*(Real.logb Z L - 0)/3 + 7*Real.logb Z ((2:ℝ)^Nn*Z^uM)/3 + 5*x/6) *
      ((2:ℝ)^Nn*Z^uM)^(2/3:ℝ) ≤
    (9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nn)^3*Z^(5*x/6) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hlZ : 0 < Real.log Z := Real.log_pos hZ
  set Lr := (2/9:ℝ)*Z^ell with hLr
  have hLr0 : 0 < Lr := by rw [hLr]; positivity
  set W := (2:ℝ)^Nn*Z^uM with hW
  have hW0 : 0 < W := by rw [hW]; positivity
  have hM0 : 0 < max 1 Lr := lt_max_of_lt_left zero_lt_one
  have hmax : max 1 Lr ≤ Z^ell := max_le (Real.one_le_rpow hZ.le hell)
    (by rw [hLr]; have := Real.rpow_pos_of_pos hz ell; linarith)
  have hlogmax : Real.log (max 1 Lr) ≤ ell*Real.log Z := by
    have := Real.log_le_log hM0 hmax
    rwa [Real.log_rpow hz] at this
  have hlogLr : Real.log Lr = Real.log (2/9) + ell*Real.log Z := by
    rw [hLr, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hz _).ne', Real.log_rpow hz]
  have hlogW : Real.log W = Nn*Real.log 2 + uM*Real.log Z := by
    rw [hW, Real.log_mul (by positivity) (Real.rpow_pos_of_pos hz _).ne', Real.log_pow,
      Real.log_rpow hz]
  have hlogL : Real.logb Z L * Real.log Z = Real.log L := by
    rw [Real.logb, div_mul_cancel₀ _ hlZ.ne']
  have hlogbW : Real.logb Z W * Real.log Z = Real.log W := by
    rw [Real.logb, div_mul_cancel₀ _ hlZ.ne']
  have hlhs0 : 0 < ((L/Lr)^(2/3:ℝ) * (max 1 Lr)^((2/3:ℝ)-α)) *
      Z^(lV - 5*m/6 - 2*(Real.logb Z L - 0)/3 + 7*Real.logb Z W/3 + 5*x/6) * W^(2/3:ℝ) := by
    have := div_pos hL0 hLr0
    positivity
  have hR0 : 0 < (9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nn)^3*Z^(5*x/6) := by positivity
  rw [← Real.log_le_log_iff hlhs0 hR0]
  have hLLr := div_pos hL0 hLr0
  have e1 : Real.log ((L/Lr)^(2/3:ℝ)) = (2/3)*(Real.log L - Real.log Lr) := by
    rw [Real.log_rpow hLLr, Real.log_div hL0.ne' hLr0.ne']
  have e2 : Real.log ((max 1 Lr)^((2/3:ℝ)-α)) = ((2/3:ℝ)-α)*Real.log (max 1 Lr) :=
    Real.log_rpow hM0 _
  have e3 : Real.log (Z^(lV - 5*m/6 - 2*(Real.logb Z L - 0)/3 + 7*Real.logb Z W/3 + 5*x/6)) =
      (lV - 5*m/6 + 5*x/6)*Real.log Z - 2*Real.log L/3 + 7*Real.log W/3 := by
    rw [Real.log_rpow hz, ← hlogL, ← hlogbW]; ring
  have e4 : Real.log (W^(2/3:ℝ)) = (2/3)*Real.log W := Real.log_rpow hW0 _
  have eR : Real.log ((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nn)^3*Z^(5*x/6)) =
      (2/3)*Real.log (9/2) + 3*(Nn*Real.log 2) + (5*x/6)*Real.log Z := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by norm_num), Real.log_pow, Real.log_pow, Real.log_rpow hz]
    push_cast; ring
  have hlhs : Real.log (((L/Lr)^(2/3:ℝ) * (max 1 Lr)^((2/3:ℝ)-α)) *
      Z^(lV - 5*m/6 - 2*(Real.logb Z L - 0)/3 + 7*Real.logb Z W/3 + 5*x/6) * W^(2/3:ℝ)) =
      Real.log ((L/Lr)^(2/3:ℝ)) + Real.log ((max 1 Lr)^((2/3:ℝ)-α)) +
      Real.log (Z^(lV - 5*m/6 - 2*(Real.logb Z L - 0)/3 + 7*Real.logb Z W/3 + 5*x/6)) +
      Real.log (W^(2/3:ℝ)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  rw [hlhs, e1, e2, e3, e4, eR, hlogLr, hlogW]
  have h92 : Real.log (9/2) = -Real.log (2/9) := by
    rw [show (9/2:ℝ) = (2/9)⁻¹ by norm_num, Real.log_inv]
  rw [h92]
  have h23 : 0 ≤ (2/3:ℝ) - α := by linarith
  have hmaxterm := mul_le_mul_of_nonneg_left hlogmax h23
  have hkey : (lV + 3*uM - α*ell - 5*m/6)*Real.log Z ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hlZ.le
    linarith
  nlinarith


open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstMixedAllowance
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional
open CenteredMomentCanonicalFirst EisensteinSchwartzPoisson CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalLedger
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

/-- `sourceControl` is monotone in the seminorm set. -/
theorem sourceControl_mono' {S T : Finset (ℕ×ℕ)} (h : S ⊆ T) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S W ≤ sourceControl T W := by
  unfold sourceControl
  exact (Finset.sup_mono h : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤ T.sup _) W

/-- The source profile squared against the side amplitude. -/
theorem sourceProfile_sq_le_amplitude (s : Source ι a b) (t₀ V : ℝ) (hV : 0 ≤ V)
    (JL J : ℕ) (hJ : 2*JL ≤ J) (cL control : Finset (ℕ×ℕ)) (hc : cL ⊆ control)
    (Z εL Cside : ℝ) (hZ : 0 ≤ Z) (hC : 0 < Cside) :
    (sourceProfile s JL cL Z εL)^2 ≤
      (fullMarkedCost s)^2*Z^(2*εL)*(amplitude s t₀ V J control Cside/Cside) := by
  have h1 := sourceControl_mono' hc s.W₁
  have h2 := sourceControl_mono' hc s.W₂
  have h10 := sourceControl_nonneg cL s.W₁
  have h20 := sourceControl_nonneg cL s.W₂
  have hht : 1 + ‖s.t₁‖ + ‖s.t₂‖ ≤ height t₀ V s.t₁ s.t₂ := by
    unfold height; have := abs_nonneg t₀; linarith
  have hh1 : 1 ≤ height t₀ V s.t₁ s.t₂ := by
    unfold height; have := abs_nonneg t₀; have := norm_nonneg s.t₁; have := norm_nonneg s.t₂; linarith
  have ht0 : 0 ≤ 1 + ‖s.t₁‖ + ‖s.t₂‖ := by positivity
  have hpow : ((1 + ‖s.t₁‖ + ‖s.t₂‖)^JL)^2 ≤ (height t₀ V s.t₁ s.t₂)^J := by
    rw [← pow_mul]
    calc (1 + ‖s.t₁‖ + ‖s.t₂‖)^(JL*2) ≤ (height t₀ V s.t₁ s.t₂)^(JL*2) :=
          pow_le_pow_left₀ ht0 hht _
      _ ≤ _ := pow_le_pow_right₀ hh1 (by omega)
  have hZ2 : (Z^εL)^2 = Z^(2*εL) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]; norm_num; ring_nf
  have hamp : amplitude s t₀ V J control Cside/Cside =
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*(height t₀ V s.t₁ s.t₂)^J := by
    unfold amplitude; field_simp
  rw [hamp]
  unfold sourceProfile
  have hfm := fullMarkedCost_nonneg s
  have hZe : 0 ≤ Z^εL := Real.rpow_nonneg hZ _
  have hc1 : 0 ≤ sourceControl control s.W₁ := sourceControl_nonneg _ _
  calc ((sourceControl cL s.W₁*sourceControl cL s.W₂)*Z^εL*(1+‖s.t₁‖+‖s.t₂‖)^JL*fullMarkedCost s)^2
      = (sourceControl cL s.W₁*sourceControl cL s.W₂)^2*(Z^εL)^2*((1+‖s.t₁‖+‖s.t₂‖)^JL)^2*
          (fullMarkedCost s)^2 := by ring
    _ ≤ (sourceControl control s.W₁*sourceControl control s.W₂)^2*(Z^εL)^2*
          (height t₀ V s.t₁ s.t₂)^J*(fullMarkedCost s)^2 := by
        gcongr
    _ = _ := by rw [hZ2]; ring

/-- **`hrootf` from the root margin.** The exceptional root input of `diag_hbud` follows from the
constant-absorption inequality `habs` (no exponent left: `RootInput.hmargin` and
`refexp_core` remove the whole CF (7.1) excess). -/
theorem hrootf_of_margin {D : StepData} {G : StepGates D} {κ : Type*} [Fintype κ]
    {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {Wsl : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (card pM Mall Mc R2 Kc Bδ Csum εsum Hv Fs slot θA : ℝ) (Nm : ℕ)
    (hpos : 0 ≤ card^2*(pM*Mall^2*(1024:ℝ)^Nm*Mc)*R2*(Kc*Z^Bδ*(Csum*Z^εsum))*Hv*Fs*slot)
    (habs : card^2*(pM*Mall^2*(1024:ℝ)^Nm*Mc)*R2*(Kc*Z^Bδ*(Csum*Z^εsum))*Hv*Fs*slot*
      ((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*
        Z^(5*(frequencyLoss Z 1 (cutoffLoss G N ε)+cutoffLoss G N ε)/6)) ≤ θA) :
    card^2*((pM*Mall^2*(1024:ℝ)^Nm*Mc*((2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)))^(2/3:ℝ))*R2*
        (Kc*refLoss d.root ((2/9)*Z^d.ell) (alphaP G ε)*Z^Bδ*(Csum*Z^εsum))*Hv*Fs*
        (slot*Z^(referenceExponent d.root η d.Kroot Z 1 (cutoffLoss G N ε) (cutoffLoss G N ε)
          ((2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)))))) ≤ θA := by
  have hZ1 := d.one_lt_Z
  have hz : 0 < Z := zero_lt_one.trans hZ1
  have hα := (alphaP_spec G ε).1.le
  have hω := (omega_spec G ε hε).1.le
  have hH1 : Real.logb Z (prefixNormMax d.root.d) = 0 := by
    rw [d.hunit]; simp [prefixNormMax]
  have hm : 1 ≤ Real.logb Z d.Kroot + Real.logb Z (η.modulus.absNorm:ℝ) +
      Real.logb Z fixedPresentationCost := by
    have hK : 1 ≤ Real.logb Z d.Kroot := by
      simpa only [Real.logb_self_eq_one hZ1] using
        Real.logb_le_logb_of_le hZ1 hz d.hKlow
    have h1 := Real.logb_nonneg hZ1 (ideal_norm_one_le η.modulus_ne_bot)
    have h2 := Real.logb_nonneg hZ1 MixedFirstChosenEnergy.fixed_presentation_one_le
    linarith
  have hcore := refexp_core Z d.root.L d.ell (alphaP G ε) (uMax G ε (∑ i, d.w i))
    (Real.logb Z (sourceVolume d.root))
    (Real.logb Z d.Kroot + Real.logb Z (η.modulus.absNorm:ℝ) + Real.logb Z fixedPresentationCost)
    (frequencyLoss Z 1 (cutoffLoss G N ε)+cutoffLoss G N ε) (omegaLoss G ε) Nm hZ1 d.root.hL
    d.hminimum d.hell hα hm d.hmargin hω
  have hrefE : referenceExponent d.root η d.Kroot Z 1 (cutoffLoss G N ε) (cutoffLoss G N ε)
      ((2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i))) =
      Real.logb Z (sourceVolume d.root) -
        5*(Real.logb Z d.Kroot + Real.logb Z (η.modulus.absNorm:ℝ) +
          Real.logb Z fixedPresentationCost)/6 - 2*(Real.logb Z d.root.L - 0)/3 +
        7*Real.logb Z ((2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)))/3 +
        5*(frequencyLoss Z 1 (cutoffLoss G N ε)+cutoffLoss G N ε)/6 := by
    unfold referenceExponent; rw [hH1]
  rw [hrefE]
  have hrl : refLoss d.root ((2/9)*Z^d.ell) (alphaP G ε) =
      (d.root.L/((2/9)*Z^d.ell))^(2/3:ℝ)*(max 1 ((2/9)*Z^d.ell))^((2/3:ℝ)-alphaP G ε) := rfl
  rw [hrl]
  calc _ = (card^2*(pM*Mall^2*(1024:ℝ)^Nm*Mc)*R2*(Kc*Z^Bδ*(Csum*Z^εsum))*Hv*Fs*slot)*
        (((d.root.L/((2/9)*Z^d.ell))^(2/3:ℝ)*(max 1 ((2/9)*Z^d.ell))^((2/3:ℝ)-alphaP G ε))*
          Z^(Real.logb Z (sourceVolume d.root) -
            5*(Real.logb Z d.Kroot + Real.logb Z (η.modulus.absNorm:ℝ) +
              Real.logb Z fixedPresentationCost)/6 - 2*(Real.logb Z d.root.L - 0)/3 +
            7*Real.logb Z ((2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)))/3 +
            5*(frequencyLoss Z 1 (cutoffLoss G N ε)+cutoffLoss G N ε)/6)*
          ((2:ℝ)^Nm*Z^(uMax G ε (∑ i, d.w i)))^(2/3:ℝ)) := by ring
    _ ≤ (card^2*(pM*Mall^2*(1024:ℝ)^Nm*Mc)*R2*(Kc*Z^Bδ*(Csum*Z^εsum))*Hv*Fs*slot)*
        ((9/2:ℝ)^(2/3:ℝ)*((2:ℝ)^Nm)^3*
          Z^(5*(frequencyLoss Z 1 (cutoffLoss G N ε)+cutoffLoss G N ε)/6)) :=
        mul_le_mul_of_nonneg_left hcore hpos
    _ ≤ θA := habs


/-! ### The zero-frequency root input -/

/-- The first child scale against the balanced core `Nτ·V²/(N C·N D)`: the retained first dyad is
below the first nominal scale `N E·N act·V²/(K_root·N C·N D)`, and `N E·N act ≤ Nτ`,
`K_root ≥ Z`. -/
theorem childScale_le_core (C D : Id) (hC : Supported C) (hD : Supported D)
    (hcpC : commonPart C D = C) (hcpD : commonPart D C = D)
    (E : Finset (CommonIndex C D)) (τ η : Character)
    (hmod : τ.modulus = η.modulus * Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} *
      Ideal.span {(72:O)} * Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        activeConductor C D})
    (Kroot V Z κ ξ : ℝ) (hZ : 1 < Z) (hK : Z ≤ Kroot) (hV : 0 < V) (n : ℤ)
    (hn : Retained (frequencyRadius (firstNominalScale C D (∏ P ∈ E, P.val) Kroot V) Z ξ) n) :
    childScale Z κ n ≤ Z^(frequencyLoss Z 1 ξ + κ) *
      ((τ.modulus.absNorm:ℝ)*V^2/((C.absNorm:ℝ)*(D.absNorm:ℝ)))/Z := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hKp : 0 < Kroot := hz.trans_le hK
  have hgen : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) =
      (Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) := by
    rw [← ActualEisensteinCubic.primeSubsetGenerator_norm_sq, eisEmbedding_norm_sq_eq_absNorm_span]
  have hEs := (subsetGenerator_supported C D hC E).1
  have hE0 : (∏ P ∈ E, P.val) ≠ 0 := by
    intro h0
    have : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) = 0 := by rw [h0]; simp
    rw [hgen] at this
    exact (norm_pos _ hEs).ne' this
  have hr := retained_nominal_frequency C D (∏ P ∈ E, P.val) hE0 Z Kroot V
    (firstNominalScale C D (∏ P ∈ E, P.val) Kroot V) 1 ξ hZ hKp hV one_pos (by rw [one_mul]) n hn
  have hF0 := firstNominalScale_pos C D (∏ P ∈ E, P.val) hE0 Kroot V hKp hV
  have hcs : childScale Z κ n ≤ firstNominalScale C D (∏ P ∈ E, P.val) Kroot V *
      Z^(frequencyLoss Z 1 ξ + κ) := by
    unfold childScale
    calc Z^(Real.logb Z (dyadicScale n) + κ) ≤
          Z^(Real.logb Z (firstNominalScale C D (∏ P ∈ E, P.val) Kroot V) +
            (frequencyLoss Z 1 ξ + κ)) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = _ := by rw [Real.rpow_add hz, Real.rpow_logb hz hZ.ne' hF0]
  have hnum := QRH.SilDensitySplit.CubeFree.Second.Provider.modulus_norm_ge τ η _ _ hmod
  have hc := norm_pos C hC.1
  have hd := norm_pos D hD.1
  have hFNS : firstNominalScale C D (∏ P ∈ E, P.val) Kroot V ≤
      ((τ.modulus.absNorm:ℝ)*V^2/((C.absNorm:ℝ)*(D.absNorm:ℝ)))/Z := by
    unfold firstNominalScale
    rw [hcpC, hcpD, hgen]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hV2 : 0 ≤ V^2 := sq_nonneg V
    have h1 : (Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) *
        (Ideal.absNorm (Ideal.span {activeConductor C D}) : ℝ) * V^2 * (Z*((C.absNorm:ℝ)*(D.absNorm:ℝ))) ≤
        (τ.modulus.absNorm:ℝ) * V^2 * (Kroot*((C.absNorm:ℝ)*(D.absNorm:ℝ))) := by
      have hCD : 0 ≤ (C.absNorm:ℝ)*(D.absNorm:ℝ) := by positivity
      have := mul_le_mul hnum (mul_le_mul_of_nonneg_right hK hCD) (by positivity) (by positivity)
      nlinarith
    nlinarith
  have hZx : 0 ≤ Z^(frequencyLoss Z 1 ξ + κ) := Real.rpow_nonneg hz.le _
  calc childScale Z κ n ≤ firstNominalScale C D (∏ P ∈ E, P.val) Kroot V *
      Z^(frequencyLoss Z 1 ξ + κ) := hcs
    _ ≤ ((τ.modulus.absNorm:ℝ)*V^2/((C.absNorm:ℝ)*(D.absNorm:ℝ)))/Z * Z^(frequencyLoss Z 1 ξ + κ) :=
        mul_le_mul_of_nonneg_right hFNS hZx
    _ = _ := by ring

/-- **`hroot0` from the core bound** (CF's `A−1−c+4u`, used as `log V + 4u_max − 1 ≤ 0`, and
`5u_max ≤ 1` for the additive slot width). -/
theorem hroot0_of_core (s : Source ι a b) (τ : Character) (C D : Id) (Abud Z loss : ℝ)
    (card Mall R2 Φ C0 Hv pM Mc prof Yup ε cs Wmax Yr Cy uM x θ0 : ℝ) (Nm : ℕ)
    (hZ : 1 < Z) (hAbud : 0 ≤ Abud) (hθ0 : 0 ≤ θ0) (hcs : cs ≤ Z^x*((τ.modulus.absNorm:ℝ)*(sourceVolume s)^2/
      ((C.absNorm:ℝ)*(D.absNorm:ℝ)))/Z)
    (hWm : Wmax = (2:ℝ)^Nm*Z^uM) (hYr0 : 0 ≤ Yr) (hYr : Yr ≤ Cy*sourceVolume s) (hCy : 0 ≤ Cy)
    (h5 : 5*uM ≤ 1) (h4 : Real.logb Z (sourceVolume s) + 4*uM - 1 ≤ 0)
    (hP : 0 ≤ card^2*Mall^2*R2*(16*Φ*C0)*Hv*(pM*Mall^2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof^2*Yup^ε)))
    (habs0 : card^2*Mall^2*R2*(16*Φ*C0)*Hv*(pM*Mall^2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof^2*Yup^ε))*
      ((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z^x ≤ θ0*Abud*Z^loss) :
    card^2*(Mall^2*R2*(16*cs*Φ*C0)*Hv*
      (pM*Mall^2*(256:ℝ)^Nm*(Wmax + Yr)*((2:ℝ)^Nm*Mc)*(Wmax^4*prof^2*Yup^ε))) ≤
      θ0*balancedBudget s τ C D Abud Z loss := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hV := sourceVolume_pos s
  set Core := (τ.modulus.absNorm:ℝ)*(sourceVolume s)^2/((C.absNorm:ℝ)*(D.absNorm:ℝ)) with hCore
  have hCore0 : 0 ≤ Core := by rw [hCore]; positivity
  have hW0 : 0 ≤ Wmax := by rw [hWm]; positivity
  have hcs0 : 0 ≤ cs ∨ cs < 0 := le_or_gt 0 cs
  -- the slot-width factor
  have hU : Z^uM*Z^uM*Z^uM*Z^uM*Z^uM ≤ Z := by
    rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
    calc Z^(uM+uM+uM+uM+uM) ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z := Real.rpow_one Z
  have hV4 : sourceVolume s*(Z^uM*Z^uM*Z^uM*Z^uM) ≤ Z := by
    have e : sourceVolume s*(Z^uM*Z^uM*Z^uM*Z^uM) =
        Z^(Real.logb Z (sourceVolume s) + 4*uM) := by
      rw [Real.rpow_add hz, Real.rpow_logb hz hZ.ne' hV, show 4*uM = uM+uM+uM+uM by ring,
        Real.rpow_add hz, Real.rpow_add hz, Real.rpow_add hz] <;> ring
    rw [e]
    calc Z^(Real.logb Z (sourceVolume s) + 4*uM) ≤ Z^(1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z := Real.rpow_one Z
  have hslot : (Wmax + Yr)*Wmax^4 ≤ ((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z := by
    rw [hWm]
    have hZu : 0 ≤ Z^uM := Real.rpow_nonneg hz.le _
    have h2 : (0:ℝ) ≤ 2^Nm := by positivity
    have e32 : ((2:ℝ)^Nm)^5 = 32^Nm := by rw [show (32:ℝ) = 2^5 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    have e16 : ((2:ℝ)^Nm)^4 = 16^Nm := by rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    calc ((2:ℝ)^Nm*Z^uM + Yr)*((2:ℝ)^Nm*Z^uM)^4
        = ((2:ℝ)^Nm)^5*(Z^uM*Z^uM*Z^uM*Z^uM*Z^uM) + ((2:ℝ)^Nm)^4*(Yr*(Z^uM*Z^uM*Z^uM*Z^uM)) := by ring
      _ ≤ ((2:ℝ)^Nm)^5*Z + ((2:ℝ)^Nm)^4*(Cy*(sourceVolume s*(Z^uM*Z^uM*Z^uM*Z^uM))) := by
          have hX0 : 0 ≤ Z^uM*Z^uM*Z^uM*Z^uM := by positivity
          apply add_le_add (mul_le_mul_of_nonneg_left hU (by positivity))
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc Yr*(Z^uM*Z^uM*Z^uM*Z^uM) ≤ (Cy*sourceVolume s)*(Z^uM*Z^uM*Z^uM*Z^uM) :=
                mul_le_mul_of_nonneg_right hYr hX0
            _ = _ := by ring
      _ ≤ ((2:ℝ)^Nm)^5*Z + ((2:ℝ)^Nm)^4*(Cy*Z) := by
          apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV4 hCy) (by positivity)
      _ = _ := by rw [e32, e16]; ring
  have hmain : cs*((Wmax + Yr)*Wmax^4) ≤ ((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z^x*Core := by
    have hWY0 : 0 ≤ (Wmax + Yr)*Wmax^4 := by positivity
    rcases hcs0 with hcs0 | hcs0
    · calc cs*((Wmax + Yr)*Wmax^4) ≤ (Z^x*Core/Z)*(((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z) :=
            mul_le_mul hcs hslot hWY0 (by have := Real.rpow_nonneg hz.le x; positivity)
        _ = _ := by field_simp
    · have : cs*((Wmax + Yr)*Wmax^4) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcs0.le hWY0
      have : 0 ≤ ((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z^x*Core := by
        have := Real.rpow_nonneg hz.le x; positivity
      linarith
  have hbud : Abud*Core*Z^loss ≤ balancedBudget s τ C D Abud Z loss := by
    unfold balancedBudget
    have hall : 1 ≤ Z^(allowance C D Z) := Real.one_le_rpow hZ.le (by unfold allowance; positivity)
    have hZl := Real.rpow_nonneg hz.le loss
    rw [← hCore]
    calc Abud*Core*Z^loss = Abud*(Core*1)*Z^loss := by ring
      _ ≤ Abud*(Core*Z^(allowance C D Z))*Z^loss :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hall hCore0) hAbud) hZl
  calc card^2*(Mall^2*R2*(16*cs*Φ*C0)*Hv*
        (pM*Mall^2*(256:ℝ)^Nm*(Wmax + Yr)*((2:ℝ)^Nm*Mc)*(Wmax^4*prof^2*Yup^ε)))
      = (card^2*Mall^2*R2*(16*Φ*C0)*Hv*(pM*Mall^2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof^2*Yup^ε)))*
          (cs*((Wmax + Yr)*Wmax^4)) := by ring
    _ ≤ (card^2*Mall^2*R2*(16*Φ*C0)*Hv*(pM*Mall^2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof^2*Yup^ε)))*
          (((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z^x*Core) := mul_le_mul_of_nonneg_left hmain hP
    _ = (card^2*Mall^2*R2*(16*Φ*C0)*Hv*(pM*Mall^2*(256:ℝ)^Nm*((2:ℝ)^Nm*Mc)*(prof^2*Yup^ε))*
          ((32:ℝ)^Nm + (16:ℝ)^Nm*Cy)*Z^x)*Core := by ring
    _ ≤ (θ0*Abud*Z^loss)*Core := mul_le_mul_of_nonneg_right habs0 hCore0
    _ = θ0*(Abud*Core*Z^loss) := by ring
    _ ≤ θ0*balancedBudget s τ C D Abud Z loss := mul_le_mul_of_nonneg_left hbud hθ0

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
