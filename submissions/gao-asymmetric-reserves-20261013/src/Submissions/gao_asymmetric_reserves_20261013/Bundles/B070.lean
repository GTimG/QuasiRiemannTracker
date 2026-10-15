/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B005
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B021
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B036
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B037
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B056
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B063
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B064
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B068
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B069
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralClassPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFixedMember

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.FiniteCollect ; sha256 edab780d862b0b807ad07b69889475887d2c3790e26570b30ba7e56465054485 -/
section




/-! The literal finite row/error-subset collection after numerator bounds. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem finite_array_weight_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι→ℂ) (F : ι→κ→ℂ) (A : ℝ) (B : κ→ℝ) (hA : 0≤ A)
    (ha : ∀i∈s,‖a i‖≤ A) (hB : ∀j∈t,(∑i∈s,‖F i j‖)≤ B j) :
    ‖∑i∈s,a i*(∑j∈t,F i j)‖≤ A*(∑j∈t,B j) := by
  calc
    _ ≤ ∑i∈s,‖a i*(∑j∈t,F i j)‖ := norm_sum_le _ _
    _ ≤ ∑i∈s,A*(∑j∈t,‖F i j‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (ha i hi) (norm_sum_le _ _) (norm_nonneg _) hA
    _ = A*(∑j∈t,∑i∈s,‖F i j‖) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) hA

theorem reconstructedDyadValue_norm_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (A : ℝ) (B : Finset (Fin K)→ℝ) (hA : 0≤ A)
    (ha : ∀u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar S hS hmax η u x z‖≤ A)
    (hb : ∀J∈Finset.univ.powerset,
      (∑u∈R,‖errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
        (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
          (-star (idealRowHom u.val P.val.val)))‖)≤ B J) :
    ‖reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y‖≤ A*(∑J∈Finset.univ.powerset,B J) :=
  finite_array_weight_bound R Finset.univ.powerset _ _ A B hA ha hb


open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem reconstructedDyadValue_amplitude_partition {K : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (slots : Finset Slot) (U cap mesh : ℝ) (hm : 0 < mesh)
    (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y =
      ∑bin : BinLabel slots cap mesh,reconstructedDyadValue S hS hmax η
        (amplitudeRows R slots U cap mesh hm widths Q bin) T hT W Yp x z W1 Y := by
  unfold reconstructedDyadValue
  exact sum_amplitudeRows R slots U cap mesh hm widths Q _

theorem reconstructedDyadValue_class_uniform {K : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (slots : Finset Slot) (U cap mesh : ℝ) (hm : 0 < mesh) (hcap : cap≤1/2)
    (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) (A : ℝ) (hA : 0≤ A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows R slots U cap mesh hm widths Q bin).Nonempty →
      ‖reconstructedDyadValue S hS hmax η
        (amplitudeRows R slots U cap mesh hm widths Q bin) T hT W Yp x z W1 Y‖≤ A) :
    ‖reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [reconstructedDyadValue_amplitude_partition S hS hmax η R T hT W Yp x z W1 Y
    slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows R slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,reconstructedDyadValue,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm


/-- Empty physical prime pools already make the original integrated numerator
zero; no arbitrary coefficient choice is made in this case. -/
theorem integratedDyadValue_zero_of_no_labels {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : SchwartzMap ℝ ℂ) (Y : ℝ)
    (hempty : ¬Nonempty (∀i,T i)) :
    FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z = 0 := by
  letI : IsEmpty (∀i,T i) := not_nonempty_iff.mp hempty
  simp only [FullWContour.integratedDyadValue,Finset.univ_eq_empty,Finset.sum_empty,Finset.sum_const_zero]

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.FiniteCollect -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowFixedMember ; sha256 bb47b0cf65cf0f886a523e599be3befbc779ac93de0ff5cebaa2864944b4adbb -/
section




/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowFixedMember.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_fixed_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ QK QP : ℝ),
      Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart I) →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      QK/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      1≤ QK → QK≤2*Ck*Z^((1-Submission20261012.Global.ell)-2*d) → 2≤ QP → QP/2≤ Z^ell0 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(1+ell0+shift)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+504*η-O₀/2) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  let ε := η/(200*(1+η))
  have hε : 0<ε := (low_reflection_parameters η hη).1
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := original_low_member_geometry_uniform a c₀ mode
    ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac (η/8) (by positivity) η hη
    η (η/2) 57 8 hη (by positivity) (by norm_num) 8 2 (by positivity)
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hlogQ⟩ := constant_log_error (Ideal.absNorm Q:ℝ) η (actual_ideal_norm_pos Q hQ) hη
  obtain ⟨Z₄,hZ₄,hlogC⟩ := constant_log_error (2*Ck) η (by positivity) hη
  obtain ⟨Z₅,hZ₅,hlog16⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max Z₅ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))))))
  have hz1 : Z₁≤ Z₀ := le_max_left _ _
  have hz2 : Z₂≤ Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤ Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤ Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : Z₅≤ Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hzcap : max 2 (max Ck (Ideal.absNorm Q:ℝ))≤ Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨degree,C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q₀ hJ hI hF hpower hmask A Z d ell0 shift O₀ QK QP
    hZ hd hd1 hell hellcap hshift hOeq hIn hKr hK1 hKcap hP2 hPcap
  have hz : 1< Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hzpos : 0< Z := lt_trans zero_lt_one hz
  have hZ2 : 2≤ Z := (le_max_left _ _).trans (hzcap.trans hZ)
  have hCkZ : Ck≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  have hQZ : (Ideal.absNorm Q:ℝ)≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  obtain ⟨hIcap,hFcap,hK8,hP8,hX8⟩ := low_actual_scale_caps J I Q Q₀ hJ hI hQ hpower hmask A
    Z Ck d ell0 shift η QK QP hZ2 hCk hCkZ hQZ hd hell hellcap hshift hη1 hIn hKcap hPcap
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hXp : 0< Z^(1+ell0+shift) := Real.rpow_pos_of_pos hzpos _
  have hQK : 0< QK := by linarith
  have hQP : 0< QP := by linarith
  have hsc := hscale i G Z (Z^(1+ell0+shift)) QK QP 8 (hz2.trans hZ) hXp hQK.le hQP.le
    hFcap hK8 hP8 hX8
  norm_num only at hsc
  have hO : 0≤ O₀ := hOeq ▸ normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero I)
  have hOp : 0<(Ideal.absNorm (rowPowerfulPart I):ℝ) := actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
  have hOn : Z^O₀=(Ideal.absNorm (rowPowerfulPart I):ℝ) := by
    rw [hOeq]
    exact Real.rpow_logb hzpos (ne_of_gt hz) hOp
  have hO2 : O₀≤2 := by
    have hh := Real.logb_le_logb_of_le hz hOp ((original_powerful_norm_le I hI).trans hIcap)
    rw [←Real.rpow_natCast,Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    norm_num at hh
    exact hOeq.symm ▸ hh
  have hza : Real.logb Z (QP/2)≤ ell0+η := by
    have hh := Real.logb_le_logb_of_le hz (by positivity : 0< QP/2) hPcap
    rw [Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    linarith
  have hrowlower : Z^(Real.logb Z QK)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [Real.rpow_logb hzpos (ne_of_gt hz) hQK]
    exact hKr
  have hslot8 : QP/2≤ Z^(8:ℝ) := by linarith
  have hbudget : ε*(8+8+2*(η/2+57+η))+η/2≤2*η := (low_reflection_parameters η hη).2
  have hh := he i (σ:=σ) J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ (Real.logb Z QK) (Real.logb Z (QP/2)) (1+ell0+shift) d ell0 shift (2*η)
    Ck 1 2 (Z^(1+ell0+shift)) QK QP 8 8
    (hz1.trans hZ) hCk (by norm_num) (by norm_num) hXp hQK hQP hIn
    (by simpa only [div_one,hOn] using le_refl (Ideal.absNorm (rowPowerfulPart I):ℝ)) hrowlower
    (by simpa only [mul_one] using hlogC Z (hz4.trans hZ))
    (by rw [hOeq];linarith) (hlogQ Z (hz3.trans hZ)) hd hd1 hellcap hO hza hshift rfl rfl rfl
    (by rw [Real.logb_rpow hzpos (ne_of_gt hz)]) (by positivity) (by linarith)
    hK8 hslot8 (hlog16 Z (hz5.trans hZ)) hbudget hX8 hK8 hP8 (by linarith)
    hFcap hsc hFcap
  dsimp only at hh ⊢
  intro rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := hh rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKn hPn hr haw
  apply (hD θ r aw hqk hqp hKn hPn hr haw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowFixedMember -/

/- BEGIN ORIGINAL MODULE Global.Transport.MixedFullWCollected ; sha256 a1051ca397db3604edd312f25555cffaa72ca05fab8781eefbb294e0bf60ab02 -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/





open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

private lemma norm_le_of_fullW_transfer {A B : ℂ} {C P : ℝ}
    (hAB : ‖A-B‖ ≤ 1) (hB : ‖B‖ ≤ C*P) (hP : 1 ≤ P) :
    ‖A‖ ≤ (C+1)*P := by
  calc
    _ = ‖(A-B)+B‖ := by rw [sub_add_cancel]
    _ ≤ ‖A-B‖+‖B‖ := norm_add_le _ _
    _ ≤ 1+C*P := add_le_add hAB hB
    _ ≤ (C+1)*P := by linarith only [hP]

theorem actual_mixed_fullW_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y ≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (μ top : ℝ) (htop : top ≤ 1)
    (hfinal : (159*ε+εm+R+7*ν)+(12*e+eps*(N+8))+
      (logCost+heightCost+momentCost+loss+mesh*Submission20261012.Global.ell+(16-6*Submission20261012.Global.ly)*e)+μ≤1/4000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (target nu : ℝ) (htarget : Submission20261012.Global.signal Submission20261012.Global.theta≤ target) (hnu : 0 < nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0 < dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : top+2*margin ≤ dmax)
    (hweightedTop : top+2*margin ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension)
    (hmuMargin : 2*margin≤μ) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,1 ≤ C0 → ∀weightedC : ℝ,0 ≤ weightedC → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(top)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u ≤ n ∧ grid u ≤ m ∧ grid u≠0 ∧ 51/100+e*grid u≤7/8) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      -- This is the only new analytic input: actual normalized full-w cells outside the old branch.
      -- It is a premise, not a theorem asserting that the weighted estimate has been proved.
      (∀k∈smallDyadicIndices (Z^top),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        let Y : Fin N→ℝ := fun j=> Z^(ell j)
        let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
        let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
          (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
            (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
        rows'.Nonempty →
        (1/2:ℝ) < sourceDyadConductor Z margin k →
        (1/3:ℝ) < 2*(51/100+e*j)-1 →
        sourceDyadConductor Z margin k ≤ top+2*margin →
        ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y)
          (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e
          (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤
          weightedC*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(target+nu)) →
      (∀k∈smallDyadicIndices (Z^(top)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) 0
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(target+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm ν logCost heightCost momentCost hεm hν hlog hMomentHeight
      μ hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu counts
  have hellpos (j : Fin N) : 0 < ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := Submission20261012.Global.LowNormalizer.actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Ct,hCt,htransfer⟩ := actual_normalized_cube_fullW_arbitrary_saving M H hH N τ 1 c b A
    Submission20261012.Global.rowExtension nu hτ hc hcb hA
      (by norm_num [Submission20261012.Global.rowExtension, Submission20261012.Endpoint.zeta]) hnu
    e he he1 S hS hmax hfirst ell hellpos hell hellsum W hW hcompact hWs hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*(C+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (top) hdmin hdmin1 hmargin hconductor,
    htransfer, source_cube_height_eventually τ hτ,
    eventually_ge_atTop ((Ct+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg ht hheightZ hlargeZ hZ
  intro C0 hC0 weightedC hweightedC rows hrows idx grid hlabels hnext hcurrent hweighted hmom
  have hC0zero : 0 ≤ C0 := zero_le_one.trans hC0
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0 < Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := (C+1)*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(target+nu)
  have hD : 0 ≤ D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(top)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤ D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51/100<51/100+e*j := by
        have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith only [he, hjp]
      have ha' : 51/100+e*j≤7/8 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j ≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      by_cases hbranch : Submission20261012.Global.Transport.OriginalBranch (sourceDyadConductor Z margin k) (51/100+e*j)
      · have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
          (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 (by unfold sourceDyadConductor;linarith)
          (by unfold sourceDyadConductor;linarith) ha ha' hbranch hC0zero Rij
          (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
            (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
          (fun u hu=> hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          hnext' hcurrent' (fun t ht=> hmom k hk i hi j hj ⟨u,hu⟩ t ht)
        apply hbounded.2.trans
        dsimp [D]
        gcongr
        · nlinarith only [hC,hweightedC,mul_nonneg hC.le hweightedC]
        · exact hZ.le
        · linarith only [htarget]
      · have hdtop' : sourceDyadConductor Z margin k ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension := by
          unfold sourceDyadConductor
          linarith only [hgeo.2.1,hweightedTop]
        have hregime : (1/2:ℝ) < sourceDyadConductor Z margin k ∧
            (1/3:ℝ) < 2*(51/100+e*j)-1 := by
          unfold Submission20261012.Global.Transport.OriginalBranch at hbranch
          constructor
          · by_contra hbad
            exact hbranch ⟨hdtop',Or.inr (le_of_not_gt hbad)⟩
          · by_contra hbad
            exact hbranch ⟨hdtop',Or.inl (le_of_not_gt hbad)⟩
        have hdynamic : sourceDyadConductor Z margin k≤ top+2*margin := by unfold sourceDyadConductor;linarith only [hgeo.2.1]
        have hw := hweighted k hk i hi j hj ⟨u,hu⟩ hregime.1 hregime.2 hdynamic
        have htop' : top ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension := by
          change top+2*margin ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension at hweightedTop
          linarith only [hweightedTop,hmargin]
        have hRtop : ∀u∈Rij,u.val≠1 ∧
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ≤ Z^(Submission20261012.Global.h+Submission20261012.Global.rowExtension) := by
          intro u hu
          refine ⟨(hrows u (hsub hu)).1,?_⟩
          exact (hrows u (hsub hu)).2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le htop')
        have hcellData : ∀u∈Rij,(51/100:ℝ) ≤ 51/100+e*j ∧ 51/100+e*j ≤ 1 ∧
            2 < Z^τ ∧ Z^τ ≤ (3*i+1:ℕ)*Z^τ ∧ (3*i+1:ℕ)*Z^τ ≤ (3*i+2:ℕ)*Z^τ ∧
            detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
              (3*(i+1:ℕ)*Z^τ) < 51/100+e*j+2*e := by
          intro u hu
          refine ⟨ha.le,ha'.trans (by norm_num),hheightZ.2,?_,?_,hnext' u hu⟩
          · have hc : (1:ℝ) ≤ (3*i+1:ℕ) := by exact_mod_cast (by omega : 1 ≤ 3*i+1)
            simpa using mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZp.le τ)
          · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 3*i+1 ≤ 3*i+2)) (Real.rpow_nonneg hZp.le τ)
        have herr := (ht η Rij hRtop (fun _=>51/100+e*j) (fun _=> Z^τ)
          (fun _=>(3*i+1:ℕ)*Z^τ) (fun _=> i) hcellData).2
        have hsaving : Ct*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) ≤ 1 := by
          calc
            _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
              (by nlinarith only [hlargeZ,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
            _ = 1 := by rw [Real.rpow_neg_one]; exact mul_inv_cancel₀ hZp.ne'
        have hηone : (1:ℝ) ≤ (η.modulus.absNorm:ℝ)^(2*eps) :=
          Real.one_le_rpow (HeckeLogarithmicInput.modulus_norm_ge_one η) (by positivity)
        have hpone : (1:ℝ) ≤ Z^(target+nu) := by
          apply Real.one_le_rpow hZ.le
          have hp : 0< Submission20261012.Global.signal Submission20261012.Global.theta := by
            rw [Submission20261012.Global.signal_low]
            have hxp : 0< Submission20261012.Global.lx := by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.x_rescaled_pos]
            linarith [Submission20261012.Global.b_pos]
          linarith only [hnu,htarget,hp]
        have hone : (1:ℝ) ≤ C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(target+nu) :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC0 hηone) hpone
        have htriangle := norm_le_of_fullW_transfer (C:=weightedC)
          (P:=C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(target+nu))
          (herr.trans hsaving) (by simpa only [mul_assoc] using hw) hone
        simp only [←mul_assoc] at htriangle
        apply htriangle.trans
        dsimp [D]
        gcongr
        nlinarith only [hC,hweightedC,mul_nonneg hC.le hweightedC]
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(top)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(top)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=> hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(top))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (top) hZ.le htop) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (target+nu) dyadCost];ring

end Submission20261012.Global.HighRowFamily

end

end
/- END ORIGINAL MODULE Global.Transport.MixedFullWCollected -/

/- BEGIN ORIGINAL MODULE Global.Transport.NormalizedTransportSaving ; sha256 7be44ccc068e16348654128079d5a208c602688c0e503bd589c6d16a65b7eb59 -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/


open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem transportSavingPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_probe_transport_saving (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Submission20261012.Global.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (_hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Submission20261012.Global.theta*ellMin) (hlarge : sigma+nu ≤ saving+Submission20261012.Global.signal Submission20261012.Global.theta) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := transportSavingPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ) ≤ a ∧ a≤7/8 ∧
        a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a ≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+Submission20261012.Global.b)/6) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,hbound⟩ := actual_normalized_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨C,hC,hb⟩ := hbound η
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  dsimp only at hb ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := hb
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,herror.trans ?_⟩
  have hβlower := hβlo
  have h1 : Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e+nu) ≤ Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Submission20261012.Global.Transport.small_saving, Submission20261012.Global.Transport.theta_lower])
  have h2 : Z^(-saving+nu) ≤ Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by dsimp [Submission20261012.Global.signal] at hlarge; linarith)
  have h3 : Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-1/4000+nu) ≤ Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h4 : Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6+e-Submission20261012.Global.theta*ellMin) ≤ Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ C*(4*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = _ := by ring

end Submission20261012.Global.HighRowFamily

end



#print axioms Submission20261012.Global.HighRowFamily.actual_normalized_probe_transport_saving
end
/- END ORIGINAL MODULE Global.Transport.NormalizedTransportSaving -/

/- BEGIN ORIGINAL MODULE Physical.ActualPacketUniform ; sha256 350210c0a14484caa34e9fa243af850b587b6ac723444051fd40182ecace5d5d -/
section



/-! The actual label-packet constant is uniform over the bare transport
window. The fourth-moment premise remains explicit at this packet layer. -/
noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Classical ContDiff
namespace Local44.Physical
open Cycle25.Numerator Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem actual_label_half_packet_bin_bound_uniform {ι : Type} [Fintype ι] [DecidableEq ι]
    (massEps cp dp Bp : ℝ) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < dp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀ (bare : ℝ), BareWindow bare → ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤ Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp dp) →
      (∀i y,‖W i y‖≤ Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤ alpha → alpha≤1 → 0< eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0< a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0< Y →
      ∀(U xi pad : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L delta loss momentEps Ccount Cmoment : ℝ),
      1≤ U → 0≤ xi → 0≤ pad → 1≤ Ccount → 1≤ Cmoment → 0≤ q → q≤ delta/2 →
      0≤ delta/2 → delta/2≤1 →
      1-alpha-6*eps≤1/2-delta/2 → -(1/100:ℝ)≤1/2-delta/2 →
      1+firsteps≤ x.re+(1/2-delta/2) → 0< Ccond →
      (∀i,0≤ Cu i) → (∀i,Cu i≤ Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤ U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤ U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤ Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*transportCapacity bare ((j:ℝ)*xi+xi+pad)-loss)≤‖Q j i‖) →
      (∀i,‖P i‖≤ U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ))
      (∀j∈Finset.range (n+1),∀e:∀i,LabelPacketIndex S (u i) T,
        (∑i,‖if (labelPacketScale S (u i) T (e i):ℝ)≤ b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i):ℝ)))=j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i):ℝ)) 0 0 else 0‖^4 * ‖Q j i‖^2)
          ≤ Cmoment*U^(1+momentEps)) →
      (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*baseCapacity bare/2+(3*R+1+momentEps)/4+loss/2+delta*(xi+pad)/2) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro bare hn S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY U xi pad n Cu Ccond Q P
    R q L delta loss momentEps Ccount Cmoment hU hxi hpad hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀i,T i→ℂ := fun i P=> physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0
  let M : ℝ := Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ))
  have hU0 : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0< N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0< M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _=> Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hYp i)) _))
  have hLM (i : κ) : Lc i ≤ 1 := by
    letI : Finite (O ⧸ (Ideal.span {(u i).val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1)
    have hNupos : (0:ℝ)<(Ideal.span {(u i).val}:Ideal O).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1))
    apply (div_le_one (mul_pos hCcond hNupos)).mpr
    exact (hCu i).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast FiniteConductor.absNorm_le_of_le (Ideal.le_radical (I := (Ideal.span {(u i).val}:Ideal O)))) hCcond.le)
  have hms (i : κ) := hmass S hS firsteps hfirst η (u i) T hT hdis hη W Yp hYp hWS hWB x z
    alpha eps (delta/2) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2))≤ M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps≤ x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) :=
    actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T) (he : ¬N i e≤ b*Y) : Sp i e=0 :=
    MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
      (N i e) hsupp hY (hNp i e) (lt_of_not_ge he)
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e≤ b*Y) :
      max 1 (Lc i*N i e)≤ U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU hxi (hLM i) (hNp i e).le he hcut
  have hb := packet_half_mass_bins (fun i=> labelPacketBase S (u i) T Pbase) A Sp N hNp Lc bare U xi pad n
    (fun i e=> N i e≤ b*Y) Q P R q L delta loss momentEps Ccount Cmoment M hn hM hU hxi hpad hc hm
    hq hqdelta hcard hzoff hupp hseries (fun i=>(hms i).1) hmassU hselected hfull hselection
  have heq : (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) =
      Y^(-(1/2:ℝ))*(∑i,‖(∑'e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e)*P i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold labelPolynomialPacket
    rw [mul_assoc,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
    rw [show (-(1/2:ℂ)).re=-(1/2:ℝ) by norm_num]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)).trans_eq (by dsimp only [M]; ring)


end Local44.Physical

#print axioms Local44.Physical.actual_label_half_packet_bin_bound_uniform
end
/- END ORIGINAL MODULE Physical.ActualPacketUniform -/

/- BEGIN ORIGINAL MODULE Analytic.ActualIncumbent ; sha256 b0ab6c89b28afddecbaf72b5cc419185557edaf9d14e7959188a455313fa6941 -/
section



/-! Both incumbent endpoints come from the completed source proof.
No marked or zero-slot moment is introduced as an additional premise. -/

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_incumbent_pair
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character,
      ∀ Q : Ideal O, Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Czero Cpositive : ℝ, 0 < Czero ∧ 0 < Cpositive ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε (3/4)
          Z η₀ Q degree S Cpositive := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap (3/4) ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap
    (by norm_num) hε hbeta (by linarith)
  exact certified_terminal (α := α) M H hH W bslot a b radial Bmask L lo hi
    Mcap (3/4) ε hmask hMcap.le (by norm_num) hε hcert

#print axioms actual_incumbent_pair
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualIncumbent -/
