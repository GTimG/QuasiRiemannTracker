import Submissions.hailey_collet_1252270103.Record1252270103Return.Low.Detector.LowReflectedLength
import Submissions.hailey_collet_1252270103.Record1252270103Return.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowBranchSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowExponent

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Reflection/LowExponent, Reflection/LowBranchSum, Reflection/LowCaps.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle61. -/
namespace OAI
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
namespace SevenEighths.Record1252270103LowReflection
section

open InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}
theorem original_surviving_low_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ,1<Z₀ ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀)) (e : A→Fin 3) (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤QRH.Record1252270103Return.Geometry.ell → ell0≤QRH.Record1252270103Return.Geometry.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+ε*(H+v+ell+za)+η/2+O₀/2≤
      ((1-QRH.Record1252270103Return.Geometry.ell)-d)+200*η+π := by
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
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨hv,hell,hel,hwidth⟩ := hgates G hpair j column e Z X QK QP δ i hZ hX hK hP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  have hH := physical_residual_width I Q hI Z ((1-QRH.Record1252270103Return.Geometry.ell)-2*d) O₀ H Ck CO CH hz hCk hCO hCH hIn hPow hRow
  have hA := original_optional_powerful_width J I Q Q₀ hJ hI hQ hpower hmask A Z hz
  have hN0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 1)
  have hS0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 0)
  have hB0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 2)
  have hNA := frozenExtracted_width_le G j e 1 Z hz
  have ht := Record1252270103LowReflected.compensated_reflected_exponent_with_length d ell0 O₀ H
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
end
section

open InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}
theorem original_surviving_low_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤QRH.Record1252270103Return.Geometry.ell → ell0≤QRH.Record1252270103Return.Geometry.ell-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(((1-QRH.Record1252270103Return.Geometry.ell)-d)+200*η+π-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_low_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^(((1-QRH.Record1252270103Return.Geometry.ell)-d)+200*η+π-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*Z^(((1-QRH.Record1252270103Return.Geometry.ell)-d)+200*η+π-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end
section

open InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
local notation "Eis" => ActualEisensteinCubic.O
lemma low_actual_scale_caps (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀))
    (Z Ck d ell0 shift η QK QP : ℝ) (hZ : 2≤Z) (hCkp : 0<Ck) (hCk : Ck≤Z)
    (hQn : (Ideal.absNorm Q:ℝ)≤Z) (hd : 0≤d) (hell : 0≤ell0)
    (hellcap : ell0≤QRH.Record1252270103Return.Geometry.ell-d+η) (hshift : |shift|≤η) (hη : η≤1)
    (hIn : (Ideal.absNorm I:ℝ)≤Ck*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d))
    (hK : QK≤2*Ck*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d)) (hP : QP/2≤Z^ell0) :
    (Ideal.absNorm I:ℝ)≤Z^2 ∧
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤Z^(8:ℝ) ∧
      QK≤Z^(8:ℝ) ∧ QP≤Z^(8:ℝ) ∧ (Z^(1+ell0+shift))⁻¹≤Z^(8:ℝ) := by
  have hgeom := (And.intro QRH.Record1252270103Return.Geometry.sixth_lt_ell QRH.Record1252270103Return.Geometry.ell_lt_fifth)
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hcp : Ck*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d)≤Z^2 := by
    calc
      _ ≤ Z*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d) := mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hz.le _)
      _ = Z^(1+((1-QRH.Record1252270103Return.Geometry.ell)-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := by
        rw [←Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num; linarith [QRH.Record1252270103Return.Geometry.ell_pos,QRH.Record1252270103Return.Geometry.ell_lt_fifth])
  have hi := hIn.trans hcp
  refine ⟨hi,?_,?_,?_,?_⟩
  · calc
      _ ≤ (Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := original_pool_restricted_norm J I Q Q₀ hJ hI hQ hpower hmask A
      _ ≤ Z^2*Z := mul_le_mul hi hQn (Nat.cast_nonneg _) (sq_nonneg _)
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QK ≤ 2*(Ck*Z^((1-QRH.Record1252270103Return.Geometry.ell)-2*d)) := by linarith
      _ ≤ Z*Z^2 := mul_le_mul hZ hcp (by positivity) hz.le
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QP ≤ 2*Z^ell0 := by linarith
      _ ≤ Z*Z^ell0 := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+ell0) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num; linarith [QRH.Record1252270103Return.Geometry.ell_pos,QRH.Record1252270103Return.Geometry.ell_lt_fifth])
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (by have hs := (abs_le.mp hshift).1;linarith)
lemma low_reflection_parameters (η : ℝ) (hη : 0<η) :
    0<η/(200*(1+η)) ∧
    η/(200*(1+η))*(8+8+2*(η/2+57+η))+η/2≤2*η := by
  have hp : 0<200*(1+η) := by positivity
  constructor
  · positivity
  · apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [sq_nonneg η]
end
end
end SevenEighths.Record1252270103LowReflection
end
end OAI
