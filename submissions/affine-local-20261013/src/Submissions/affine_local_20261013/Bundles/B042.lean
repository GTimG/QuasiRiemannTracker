/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B030
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B036
import Submissions.affine_local_20261013.Bundles.B037
import Submissions.affine_local_20261013.Bundles.B038
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralClassArithmetic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowExponent

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowSourceScales ; sha256 546054da82a7d4c36f2bb1d020b167a47e0be767ccc765eb38f9f3bed6450e91 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowSourceScales.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
namespace LowProbe
open ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0< Z) :
    Z^(Submission20261012.Global.ly:ℝ)/Z^(Submission20261012.Global.lx:ℝ)=Z^(Submission20261012.Global.b:ℝ) := by
  rw [←Real.rpow_sub hZ]
  rw [Submission20261012.Global.length_difference]

lemma source_scale_square (Z : ℝ) (hZ : 0< Z) :
    Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)*Z^(Submission20261012.Global.ly:ℝ)=(Z^(Submission20261012.Global.lx:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  rw [Submission20261012.Global.LowGeometry.scale_square]
  congr 1
  norm_num
  ring

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(Submission20261012.Global.b:ℝ)) (hLl : L≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)) :
    1≤ Z^(Submission20261012.Global.ly:ℝ)/L ∧
    q*Z^(Submission20261012.Global.lx:ℝ)≤ Z^(Submission20261012.Global.ly:ℝ) ∧
    L*Z^(Submission20261012.Global.ly:ℝ)≤ q^2*(Z^(Submission20261012.Global.lx:ℝ))^2 := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)≤ Submission20261012.Global.ly from Submission20261012.Global.LowGeometry.dilation_le_y))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (Submission20261012.Global.lx))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)*Z^(Submission20261012.Global.ly:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(Submission20261012.Global.lx:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(Submission20261012.Global.b:ℝ)) (hLl : L≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)) (hδ : 0≤δ) :
    (q*(Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.ly:ℝ)/L)/(Z^(Submission20261012.Global.ly:ℝ)/L))*
      (1+((Z^(Submission20261012.Global.ly:ℝ)/L)^2/(q*(Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.ly:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Submission20261012.Global.ly:ℝ)/L)^2/(q*(Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.ly:ℝ)/L)))^2/(Z^(Submission20261012.Global.ly:ℝ)/L))*
      (Z^(Submission20261012.Global.ly:ℝ)/L)^δ ≤
        (3*q/L)*Z^((2*Submission20261012.Global.signal Submission20261012.Global.theta)+(Submission20261012.Global.ly)*δ:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0< q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0< L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(Submission20261012.Global.ly:ℝ)/(q*Z^(Submission20261012.Global.lx:ℝ))≤ Z^(Submission20261012.Global.b:ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤ Z^(Submission20261012.Global.ly:ℝ)/(q*Z^(Submission20261012.Global.lx:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.b:ℝ))^(1/6:ℝ)*(Z^(Submission20261012.Global.ly:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(Submission20261012.Global.lx:ℝ)*(Z^(Submission20261012.Global.b:ℝ))^(1/6:ℝ)*(Z^(Submission20261012.Global.ly:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(Submission20261012.Global.b:ℝ)) (hLl : L≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.ly:ℝ)/L)/(Z^(Submission20261012.Global.ly:ℝ)/L))*
      (1+((Z^(Submission20261012.Global.ly:ℝ)/L)^2/(q*(Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.ly:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(Submission20261012.Global.ly:ℝ)/L)^2/(q*(Z^(Submission20261012.Global.lx:ℝ)/L)*(Z^(Submission20261012.Global.ly:ℝ)/L)))^2/(Z^(Submission20261012.Global.ly:ℝ)/L))*
      (Z^(Submission20261012.Global.ly:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : elementNorm C.generator≤ Z^(Submission20261012.Global.b:ℝ))
    (hLl : L≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧ elementNorm C.generator≤ Z^(Submission20261012.Global.b:ℝ) ∧
      ∀L : ℝ,1≤ L→L≤ B*Z^(Submission20261012.Global.ell:ℝ)→
        1≤ Z^(Submission20261012.Global.ly:ℝ)/L ∧
        1≤(Z^(Submission20261012.Global.ly:ℝ)/L)^2/lowPhysicalScale C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(Submission20261012.Global.lx:ℝ)/L) (Z^(Submission20261012.Global.ly:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+((Submission20261012.Global.ly/2))*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<(Submission20261012.Global.b:ℝ) from Submission20261012.Global.b_pos)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((2*Submission20261012.Global.lx-Submission20261012.Global.ly-Submission20261012.Global.ell):ℝ) from Submission20261012.Global.LowGeometry.dilation_gap)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ) := calc
    L≤ B*Z^(Submission20261012.Global.ell:ℝ) := hLB
    _≤ Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly-Submission20261012.Global.ell):ℝ)*Z^(Submission20261012.Global.ell:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((2*Submission20261012.Global.lx-Submission20261012.Global.ly):ℝ) := by rw [←Real.rpow_add hz]; congr 1; ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=> lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowSourceScales -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowExponent ; sha256 d06fad3517bd263653027fbe9fcba11bea61b0d5996c8b44705638671031d406 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowExponent.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_low_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0< kK) (hkP : 0< kP) (hη : 0<η) :
    ∃ Z₀ : ℝ,1< Z₀ ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀)) (e : A→Fin 3) (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤ Z^Lrow → (kP*QP)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+ε*(H+v+ell+za)+η/2+O₀/2≤
      ((1-Submission20261012.Global.ell)-d)+200*η+π := by
  obtain ⟨Z₀,hZ₀,hgates⟩ := actual_surviving_retained_gates s hc₀ kK kP η hkK hkP hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hK hP hIn hPow hRow hlog hPowUpper hQwidth hd hd1 hell0 hO hza hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscale hret hsurv
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨hv,hell,hel,hwidth⟩ := hgates G hpair j column e Z X QK QP δ i hZ hX hK hP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  have hH := physical_residual_width I Q hI Z ((1-Submission20261012.Global.ell)-2*d) O₀ H Ck CO CH hz hCk hCO hCH hIn hPow hRow
  have hA := original_optional_powerful_width J I Q Q₀ hJ hI hQ hpower hmask A Z hz
  have hN0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 1)
  have hS0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 0)
  have hB0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 2)
  have hNA := frozenExtracted_width_le G j e 1 Z hz
  have ht := LowReflected.compensated_reflected_exponent_with_length d ell0 O₀ H
    (normWidth Z (∏ b,G.ideal b)) (normWidth Z (frozenExtracted G j e 1))
    (normWidth Z (frozenExtracted G j e 0)) (normWidth Z (frozenExtracted G j e 2)) za
    (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
    (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
    (ramifiedWidth Z i.1) shift (5*η)
    hd hd1 (by positivity) (by linarith) (by linarith) (by linarith)
    hN0 hNA hS0 hB0 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (hshift.trans (by linarith)) ?_
  · have hb := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
      (kK*QK) (kP*QP) (familyRawScale_pos G s hc₀ X QK QP hX hK hP) hz
      (mul_pos hkK hK) (mul_pos hkP hP) hscale hconst hrowcap hslotcap i hret
      (frozenExtracted G j e 1) (frozenExtracted G j e 2)
      (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
    rw [←heH,←heza] at hb
    have hb' := mul_le_mul_of_nonneg_left hb hε
    have hTd : terminalDualWidth Z H za Nstar G.ideal j e=
        2*H+2*normWidth Z (∏ b,G.ideal b)+2*za-1-ell0-shift-
          normWidth Z (frozenExtracted G j e 1)-3*normWidth Z (frozenExtracted G j e 2) := by
      unfold terminalDualWidth
      rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal]
      ring
    change InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
      (normWidth Z (frozenExtracted G j e 2)) za _ _ _ _+_+_+_≤_
    rw [hTd]
    unfold InverseTerminalWidths.reflectedExponent at ht ⊢
    linarith
  · dsimp only [terminalDualWidth] at hwidth
    rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal] at hwidth
    linarith
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowExponent -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SourcePrimeBins ; sha256 8aba17437065e1b10a6363129447edc09e1f6ca6c4dd89aa3725d94c327d1b03 -/
section




/-! The original canonical prime-amplitude estimates, specialized to the new
source slots and the two external heights of the full-w representation. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical
open HeckeInverseAmplification ProbeMellinBoundary HeckePrimeAmplitudeBins

 theorem weighted_source_prime_bins {Δ : ℝ}
    (D : HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (τ : ℝ) (n : ℕ) (hτ : 0 < τ) (hheight : 4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 →
      ∀(η : Character) (u : FreeRow),Z^(1/100:ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 → rowNorm u ≤ Z^(d-D.t) →
      ∀(a : ℝ) (i : ℕ),i ≤ n → (51/100:ℝ) ≤ a → a ≤ 1 →
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ) < a+2*D.e →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ → ∀j : Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
      let g := amplitude (Z^(D.ell j)) (a-1/2) D.t Q
      0 ≤ g ∧ g ≤ a-1/2 ∧ g∈labels (a-1/2) D.t ∧
      ‖Q‖ ≤ (Z^(D.ell j))^(g+D.t) ∧
      (0 < g → (Z^d)^(2*(D.ell j/d)*g) ≤ ‖Q‖^2) := by
  have hp := actual_phase_bins_on_cube F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad F.maximal F.W 1 2 (by norm_num) (by norm_num)
    (Cycle25.Numerator.source_complex_support_open F) (F.W.smooth ⊤)
    D.t (1/200) (7/8) D.rmin τ D.ε D.e D.κ D.cost D.t (1/100) D.t n
    D.t_pos.le (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.e_pos D.e_small
    D.kappa_pos D.cost_pos.le D.t_pos (by norm_num) D.phase_budget D.epsilon_gap
    D.t_pos (by linarith)
  filter_upwards [hp,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) 2 (by norm_num),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hp hscale hT hZ
  intro d hd hd' η u hulo hcal huhi a i hi ha ha' hbin z hz hzim j
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  have hrlo : D.rmin ≤ D.ell j/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := (D.slots_bounds j).2.1
    nlinarith only [hh,hd',D.rmin_pos]
  have hrhi : D.ell j/d ≤ D.t := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (D.slots_bounds j).2.2
    nlinarith only [hh,hd,D.t_pos]
  have hH : 0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ := by positivity
  have hhh : ((|((0,z.im),0).1.1| ≤ (3*i+1:ℕ)*Z^τ ∧
      |((0,z.im),0).2| ≤ (3*i+1:ℕ)*Z^τ) ∧
      |((0,z.im),0).1.2| ≤ (3*i+1:ℕ)*Z^τ) := by
    simpa only [abs_zero] using And.intro (And.intro hH hH) hzim
  have hh := hp d hd hd' (hscale d hd) hT η u hulo hcal huhi a i hi ha ha' hbin
    (D.ell j/d) ((0,z.im),0) hrlo hrhi hhh
  have he : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hz' : (17/50:ℂ)+z.im*Complex.I=z := by
    apply Complex.ext <;> simp [hz]
  dsimp only at hh ⊢
  rw [he,hz'] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Global.Numerator.SourcePrimeBins -/

/- BEGIN ORIGINAL MODULE Global.Transport.CentralClassArithmetic ; sha256 6ace7d068f4f43877fe723a0da3567dbb4efb7e4e32185ba79c35c017580af3d -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/




/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem classPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_class_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a q D Rcount : ℝ),0≤ v → 51/100≤ a → a≤1 → 0≤ D → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      (rows.card:ℝ)≤ D*(Z^d)^Rcount →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      (∀u∈rows,weightedMean Finset.univ (fun j=> ell j/d)
        (fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) ((17/50:ℂ)+t.1.2*Complex.I)))=q) →
      ‖cubeArithmeticSum S hS hmax η rows T (classPoolOutside M H S N c b Y) W Y a e t‖≤
        C*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-Submission20261012.Global.ell*(4/25)+q*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2:ℝ)^(4/25+12*e+eps*(N+8)))
  have hAA : 0< AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*AA,mul_pos hC hAA,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let α : ℝ := a-1/2+12*e+eps*(N+8)
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=> classPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let E : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-Submission20261012.Global.ell*(4/25)+q*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell)
  have hE : 0≤ E := by dsimp [E];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤ E*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=Z^(-Submission20261012.Global.ell*(4/25)+q*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(Submission20261012.Global.ell*(4/25):ℝ)+weightedMean Finset.univ (fun j=> ell j/d) g*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j=> ell j/d) g=q from hq u hu]
      congr 1 ; ring
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 ; dsimp [F,E,α,Y,z,g] ; ring
  have hh := dyadic_weighted_rows_card α (17/50) E (Z^v) (D*(Z^d)^Rcount) hE
    (Real.rpow_pos_of_pos hZp _) rows hcard hnorm F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (classPoolOutside M H S N c b Y) W Y a e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)≤ AA :=
    annular_power_uniform _ _ (by dsimp [α];linarith)
  apply (hsum.trans hh).trans
  have hpow : (Z^d)^Rcount*Z^loss*Z^(-Submission20261012.Global.ell*(4/25)+q*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell)*(Z^v)^(α-17/50)=
      Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-Submission20261012.Global.ell*(4/25)+q*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D*(Z^d)^Rcount)*E*AA*(Z^v)^(α-17/50) := by gcongr
    _ = _ := by
      dsimp [E]
      calc
        _ = (C*AA)*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          ((Z^d)^Rcount*Z^loss*Z^(-Submission20261012.Global.ell*(4/25)+q*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell)*(Z^v)^(α-17/50)) := by ring
        _ = _ := by rw [hpow]
end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CentralClassArithmetic -/

/- BEGIN ORIGINAL MODULE Global.Transport.CentralExponent ; sha256 5e931dcdc2f6e64fc04cc6d0c2a9fa2a8bddf095a5ce5b5685e7f6cc2d5bebde -/
section


noncomputable section
namespace Submission20261012.Global.Transport
lemma adaptive_count_identity {delta q epsilon em R nu : ℝ} (hd : 0< delta) (hd1 : delta≤3/4) (_hq : 0≤ q) (_hq1 : q≤ delta/2) :
    OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent delta q 0 epsilon em R nu =
    oldCount delta (q/delta)+(159*epsilon+em+R+7*nu) := by
  simp only [OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent,ite_eq_left (show delta≤5/6 by linarith),zero_div,add_zero]
  unfold oldCount
  ring
theorem central_exponent_identity (d v a q countLoss rowLoss outerLoss : ℝ) :
    centralScale a 0 + d * (oldCount (2 * a - 1) (q / (2 * a - 1)) + countLoss) +
      v * (a - 1 / 2 - 17 / 50 + rowLoss) + outerLoss - 4*ell/25 + q * ell =
    genericOldExponent d (2 * a - 1) q (oldCount (2 * a - 1) (q / (2 * a - 1))) + signal theta +
      d * countLoss + v * rowLoss + outerLoss + (d - v) * (17 / 50 - (a - 1 / 2)) := by
  unfold centralScale genericOldExponent Submission20261012.Global.signal Submission20261012.Global.b
  rw [Submission20261012.Global.y_endpoint,Submission20261012.Global.row_endpoint]
  ring

theorem central_class_saving {d v a q countLoss rowLoss outerLoss μ : ℝ}
    (hd0 : 0 ≤ d) (_hv0 : 0 ≤ v) (hvd : v ≤ d) (hdv : d - v ≤ μ)
    (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a) (hc : 0 ≤ countLoss) (hr : 0 ≤ rowLoss)
    (hbudget : countLoss + rowLoss + outerLoss + μ ≤ 1 / 4000) :
    centralScale a 0 + d * (oldCount (2 * a - 1) (q / (2 * a - 1)) + countLoss) +
      v * (a - 1 / 2 - 17 / 50 + rowLoss) + outerLoss - 4*ell/25 + q * ell ≤
      signal theta - 1 / 4000 := by
  have he := original_branch_exponent hd0 ha0 ha1 hq0 hq1 hbranch
  have hd1 : d ≤ 1 := hbranch.1.trans extended_h_lt_one.le
  have hv1 : v ≤ 1 := hvd.trans hd1
  have hc' := mul_le_mul_of_nonneg_right hd1 hc
  have hr' := mul_le_mul_of_nonneg_right hv1 hr
  have hp := mul_nonneg (sub_nonneg.mpr hvd) (show 0 ≤ a - 1 / 2 by linarith)
  have hμ : (d - v) * (17 / 50 - (a - 1 / 2)) ≤ μ := by nlinarith
  rw [central_exponent_identity]
  nlinarith

/-- Actual count and physical-loss bookkeeping used by the original central cube. -/
theorem actual_central_class_saving (N : ℕ) {d v a q ε εm R ν e eps loss mesh
    logCost heightCost momentCost μ : ℝ}
    (hd0 : 0 ≤ d) (_hv0 : 0 ≤ v) (hvd : v ≤ d) (hdv : d - v ≤ μ)
    (ha0 : 51 / 100 < a) (ha1 : a ≤ 7 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ (2 * a - 1) / 2)
    (hbranch : OriginalBranch d a)
    (hε : 0 ≤ ε) (hεm : 0 ≤ εm) (hR : 0 ≤ R) (hν : 0 ≤ ν)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : (159 * ε + εm + R + 7 * ν) + (12 * e + eps * (N + 8)) +
      (logCost + heightCost + momentCost + loss + mesh * ell + (16-6*ly) * e) + μ ≤ 1 / 4000) :
    logCost + heightCost + momentCost +
      d * OAI.SevenEighths.ProbeHighRowFamily.adaptiveRowExponent (2*a-1) q 0 ε εm R ν +
      v * (a-1/2+12*e+eps*(N+8)-17/50) + loss - 4*ell/25 + q*ell + mesh*ell ≤
      signal theta - 1 / 4000 - centralScale a e := by
  rw [adaptive_count_identity (by linarith) (by linarith) hq0 hq1]
  have hh := central_class_saving hd0 _hv0 hvd hdv ha0 ha1 hq0 hq1 hbranch
    (show 0 ≤ 159 * ε + εm + R + 7 * ν by positivity)
    (show 0 ≤ 12 * e + eps * (N + 8) by positivity) hbudget
  unfold centralScale at *
  nlinarith


end Submission20261012.Global.Transport
end
/- END ORIGINAL MODULE Global.Transport.CentralExponent -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeFiniteError ; sha256 4e2d7712fd03b3774474e2201d611a82ceaa23d651a05dbbb348178cfab44b9e -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]


theorem finite_cube_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0 < b) (hζ : ζ≤1/48) (hA : 0≤ A)
    (e : ℝ) (he : 0 < e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((Submission20261012.Global.h:ℝ)+ζ)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(Submission20261012.Global.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2 < B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u) < a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=> Z^(length j)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=> Z^(length j)) W0 W1
          (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_cube_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((Submission20261012.Global.h:ℝ)+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (Submission20261012.Global.h:ℝ)+ζ≤1 by linarith [Submission20261012.Global.h_interval])
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (Submission20261012.Global.ell:ℝ)≤1 by linarith [Submission20261012.Global.ell_interval])) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z (a u) e (H u)‖≤ E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=> hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=> hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤ A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) (fun j _=> hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CubeFiniteError -/
