/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B030
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B046
import Submissions.affine_local_20261013.Bundles.B055
import Submissions.affine_local_20261013.Bundles.B056
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowInverseNormalize
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowRemoteMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorCollected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFull

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowInverseNormalize ; sha256 9feb8275f55eeb52f75f9f0c368aa0a67a92bee4ff58ef32e362273f9b8def1d -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowInverseNormalize.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
namespace LowProbe
open ProbePhysical

lemma low_inverse_power_cancel (Z d α : ℝ) (hZ : 0< Z) :
    Z^((1-Submission20261012.Global.ell)-2*d+α)*(Z^d)^2/Z^((1-Submission20261012.Global.ell):ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0< q) (hC : 0≤ C) (_hB : 0≤ B) (hZ : 0< Z) (hL : 0< L) (hH : 1≤ H)
    (hE : 0≤ E) (hEL : E≤ C*H^n*Z^((1-Submission20261012.Global.ell)-2*d+α)) (hLB : L≤ B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^((1-Submission20261012.Global.ell):ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^((1-Submission20261012.Global.ell):ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^((1-Submission20261012.Global.ell)-2*d+α))/(q*Z^((1-Submission20261012.Global.ell):ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^((1-Submission20261012.Global.ell)-2*d+α))*L^2/(q*Z^((1-Submission20261012.Global.ell):ℝ)) := by field_simp
      _≤(C*H^n*Z^((1-Submission20261012.Global.ell)-2*d+α))*(B*Z^d)^2/(q*Z^((1-Submission20261012.Global.ell):ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^((1-Submission20261012.Global.ell)-2*d+α)*(Z^d)^2/Z^((1-Submission20261012.Global.ell):ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowInverseNormalize -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowRemoteMass ; sha256 46ff8dfd6e46ea863e3d0d5c3b1a0f27fa8ee7473d1b15c914ab5906c1b79994 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowRemoteMass.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalSlot_count (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (H : ℝ) (hH : 1≤ H) (hnorm : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤ H) :
    ((canonicalSlotSupport T).card:ℝ)≤128*H := by
  have hh := DescentFiberCost.finite_ideal_count_real (lowPrimeIdealList T) H hH
    (fun I hI=>(lowPrimeIdealList_prime T I hI).ne_zero) (lowPrimeIdealList_norm T H hnorm)
  have he := Fintype.card_congr (canonicalSlotEquiv T hT)
  simp only [Fintype.card_coe] at he
  rw [lowPrimeIdealList,Finset.card_image_of_injective _ Subtype.val_injective,he] at hh
  exact hh

lemma canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ Submission20261012.Global.ell) (b Z : ℝ) (hZ : 1≤ Z)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(Submission20261012.Global.ell:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod₀ (fun i _=> Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma slotProduct_norm_ge_one {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    1≤ elementNorm (slotProduct p J) := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr (slotProduct_nonzero p hp J)))

lemma compensationSubsetWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (Y : Fin K→ℝ)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    ‖compensationSubsetWeight η W Y p J‖≤1 := by
  rw [compensationSubsetWeight,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans _
  · rw [compensationSubsetCoefficient,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (slotProduct_norm_pos p hp J).le _),norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (slotProduct_norm_ge_one p hp J) (by norm_num))).trans (ProbeRow.targetMonoid_norm_le_one η _)
  · rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _=> norm_nonneg _) (fun i _=> hW i _)

lemma compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (b Z : ℝ) (hZ : 1≤ Z) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=> Z^(Submission20261012.Global.lx:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Z^(Submission20261012.Global.ly:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(Submission20261012.Global.lx:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(Submission20261012.Global.ly:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^((1-Submission20261012.Global.ell):ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=> norm_nonneg _) (fun (i : SelectedSlot J) _=> hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=> hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤ elementNorm C.generator*Z^((1-Submission20261012.Global.ell):ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(Submission20261012.Global.ell:ℝ)*Z^((1-Submission20261012.Global.ell):ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowRemoteMass -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowFull ; sha256 d8e2f29ddcd2e639ab42ce4059c004a63f548e2162b60b864ac0802a2d415430 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowFull.
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
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_full_energy
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤ Lpool) :
    ∃ (degree degreeTail : ℕ) (C Ctail Z₀ : ℝ), 0< C ∧ 0< Ctail ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤ Z^Lrow → (QP/2)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,Cm,Z₀,hCm,hZ₀,henergy⟩ := original_low_sector_retained_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail
    (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) lo hi hlo Adecay W hWs hW
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤ Cshape := by dsimp [Cshape];positivity
  have hCtail : 0< Ctail := by dsimp [Ctail];positivity
  refine ⟨degree,degreeTail,2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0< Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤ Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤ Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hNlevel hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    gcongr
    linarith only
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
      nlinarith only [hp]
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowFull -/

/- BEGIN ORIGINAL MODULE Global.Transport.CanonicalReduction ; sha256 8fcdee98e97cee80f97bd7342880b8e4e5e606d6b26d1aed2ceeb90f2ee3bf72 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/



open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O


theorem canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) T W (fun i=> Z^(length i))
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)) := by
  obtain ⟨Cs,hCs,hs⟩ := canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := canonical_large_original_tail K δ a b B ζ saving hδ (by linarith [Submission20261012.Global.h_interval]) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=> outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=> Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Submission20261012.Global.h_interval]))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=> Z^(length i)) W0 W1
      (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=> primaryGenerator (P i).val.val) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=> by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CanonicalReduction -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeFloorCollected ; sha256 a0444944ef58dd161058added6fe463d5d9844d57cdd5c4571db619244033219 -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/





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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem collectedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hδ : 0<δ)
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
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu)
    (saving : ℝ) (hsaving : 0 < saving)
    (htotal : 26*e+(N+8)*eps+loss+mesh*Submission20261012.Global.ell+nu+saving≤1/100) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin ≤ d → d ≤ dmax → ∀(v : ℝ),0 ≤ v → v ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u ≤ Z^v) →
      ∀idx : FreeRow→ℕ,(∀u∈rows,idx u ≤ n) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (collectedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(Submission20261012.Global.signal Submission20261012.Global.theta-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := actual_floor_cube_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu saving hsaving htotal
  refine ⟨(n+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η] with Z hb
  intro d hd hd' v hv hvhi rows hrows hnorm idx hidx hbin
  dsimp only
  let Yp : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
  let hT := collectedFloorPoolOutside M H S N c b Yp
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
  let Ri : ℕ→Finset FreeRow := fun i=> rows.filter (fun u=> idx u=i)
  have hnormer := (hb d hd hd' v hv hvhi ∅ (by simp) (by simp) 0 (Nat.zero_le n) (by simp)).1
  refine ⟨hnormer,?_⟩
  have hpart := finiteCentralCubeRows_bin_partition S hS hmax η rows T hT WC Yp W0 W1
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (Z^τ) idx (fun _=>0) n 0 (fun u hu=>⟨hidx u hu,le_rfl⟩)
  have heq : finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
      (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑i∈Finset.range (n+1),finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ) := by
    simpa [cubeBinRows,Ri] using hpart
  change ‖finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [heq,Finset.sum_div]
  apply (norm_sum_le _ _).trans
  have hboundi (i : ℕ) (hi : i∈Finset.range (n+1)) :
      ‖finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(Submission20261012.Global.signal Submission20261012.Global.theta-saving) := by
    have hsub : Ri i⊆rows := Finset.filter_subset _ _
    have hbi : ∀u∈Ri i,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e := by
      intro u hu
      have hh := hbin u (hsub hu)
      rwa [(Finset.mem_filter.mp hu).2] at hh
    exact (hb d hd hd' v hv hvhi (Ri i) (fun u hu=> hrows u (hsub hu))
      (fun u hu=> hnorm u (hsub hu)) i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hbi).2
  calc
    _ ≤ ∑i∈Finset.range (n+1),C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(Submission20261012.Global.signal Submission20261012.Global.theta-saving) := Finset.sum_le_sum hboundi
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring

end Submission20261012.Global.HighRowFamily

end



#print axioms Submission20261012.Global.HighRowFamily.actual_floor_rows_saving
end
/- END ORIGINAL MODULE Global.Transport.CubeFloorCollected -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderBounds ; sha256 889646ccd3e9f15ef6b266db41637d78569b479a775e88faacb29b53b10919ec -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Submission20261012.Global.Transport.PrincipalRemainderBounds
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
open Submission20261012.Global.Transport.PrincipalFiniteProduct Submission20261012.Global.Transport.PrincipalFiniteProductX Submission20261012.Global.Transport.PrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma active_prime_sum_bound (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B) (hP : 0< P)
    (hthreshold : 480 ≤ c*P) (hξ : ξ ≤ 1)
    (hW : ∀x,0 ≤ W x ∧ W x ≤ B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
       ≤ (128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=> W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A) :
      c*P ≤ (Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ) ≤ d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ) ≤ 128*(d*P) := by
    have h := DescentFiberCost.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1) ≤ c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith [Submission20261012.Global.Transport.theta_bounds])
  rw [he]
  calc
    _ ≤ ∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _ ≤ (128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

def slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(theta :ℝ)))*(128*d*B*c^(ξ-1))

lemma slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B) : 0 ≤ slotConstant J c d B ξ := by
  have hd0 : 0 ≤ d := hc.le.trans hd
  unfold slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=> by positivity)

theorem window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0< P j)
    (hthreshold : ∀j∈J,480 ≤ c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j)
    (T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s w z : ℂ)
    (hs : theta  ≤ s.re) (hw : 19/20 ≤ w.re) (hz : z.re=ξ) (hzlo : 33/200 ≤ ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖ ≤ 
      slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=> W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A j) : c*P j ≤ (Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := Submission20261012.Global.Transport.PrincipalFiniteProduct.combined_slot_bound_sharp η S hS J A
    (fun j p=> W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=> PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _ ≤ (3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(theta :ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=> by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstant,←mul_assoc,Finset.prod_mul_distrib]

def scalePower (X Y Z a ξ υ : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)

lemma scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    0 ≤ scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0< P j) (hthreshold : ∀j∈J,480 ≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) (T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
  (ha : theta  ≤ a) (hυ : 19/20 ≤ υ) (hzlo : 33/200 ≤ ξ) (hC : 0 ≤ C)
  (hR : ∀s : ℂ,a ≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖  ≤ 
    scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖ ≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := Submission20261012.Global.Transport.PrincipalContours.height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX];congr 1;simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ];congr 1;simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];congr 1;simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile;ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma full_sharp_pointwise (hυhi : υ ≤ 2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖  ≤ 
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := Submission20261012.Global.Transport.PrincipalContours.fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := Submission20261012.Global.Transport.PrincipalContours.fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (Submission20261012.Global.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _ ≤ (scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact Submission20261012.Global.Transport.PrincipalContours.height_le_joint_z _ _ _ | exact Submission20261012.Global.Transport.PrincipalContours.height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖  ≤ 
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := Submission20261012.Global.Transport.PrincipalContours.fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (Submission20261012.Global.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _ ≤ (scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _ ≤ (scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact Submission20261012.Global.Transport.PrincipalContours.height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=> F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ (fun w=> F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=> F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    Integrable F heightMeasure ∧
      (∫p,‖F p‖ ∂heightMeasure) ≤ K/(|6*ξ-1| *|υ-1|)*
        (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (theta ) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := Submission20261012.Global.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := Submission20261012.Global.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := Submission20261012.Global.Transport.PrincipalContours.continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=> LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hE : 0 ≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _ ≤ ∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _ ≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _ ≤ (K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith [Submission20261012.Global.Transport.theta_bounds]

theorem residue_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume) ≤ K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (theta ) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := Submission20261012.Global.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := Submission20261012.Global.Transport.PrincipalContours.continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I)) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    rw [Submission20261012.Global.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hE : 0 ≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _ ≤ ∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _ ≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _ ≤ (K+1)/|6*ξ-1| *E := by gcongr;linarith [Submission20261012.Global.Transport.theta_bounds]

theorem full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤ 
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0< k := pow_pos normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _ ≤ k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _ ≤ k*(K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem residue_vertical_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral ξ
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖ ≤ 
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0< k := pow_pos normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ (1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _ ≤ (1+‖R‖)*(k*(K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
      gcongr;exact hh.2
    _=_ := by ring
end Uniform

theorem ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e ≤ 5/6) :
    ∃C : ℝ,0< C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤ 
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖ ≤ 
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith [Submission20261012.Global.Transport.theta_bounds],by linarith [Submission20261012.Global.Transport.theta_bounds]⟩ (by linarith [Submission20261012.Global.Transport.theta_bounds])
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith [Submission20261012.Global.Transport.theta_bounds])];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith [Submission20261012.Global.Transport.theta_bounds]

lemma source_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a ξ υ : ℝ) (hZ : 0< Z) :
    scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(slotEll j))^ξ) =
    Z^(a-(4+b)/6+(h)*(ξ-1/6)+(ly)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(slotEll j))^ξ)=Z^((ell)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  rw [Submission20261012.Global.row_endpoint, Submission20261012.Global.b]; nlinarith [Submission20261012.Global.length_sum]

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a e : ℝ) (hZ : 0< Z) :
    scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(slotEll j))^(1/6+e)) = Z^(a-(4+b)/6+(h)*e-ly/20) := by
  rw [source_scale_identity J slotEll hell Z a (1/6+e) (19/20) hZ]
  congr 1;rw [Submission20261012.Global.row_endpoint, Submission20261012.Global.b]; nlinarith [Submission20261012.Global.length_sum]

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a : ℝ) (hZ : 0< Z) :
    scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(slotEll j))^(33/200:ℝ)) = Z^(a-(4+b)/6-h/600) := by
  rw [source_scale_identity J slotEll hell Z a (33/200) 1 hZ]
  congr 1;rw [Submission20261012.Global.row_endpoint, Submission20261012.Global.b]; nlinarith [Submission20261012.Global.length_sum]

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e ≤ 5/6) :
    ∃C : ℝ,0< C ∧ ∀(slotEll : ι→ℝ),(∑j∈J,slotEll j=ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0< Z→
    (∀j∈J,480 ≤ c*Z^(slotEll j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(slotEll j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(slotEll j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤ 
      C/e*Z^(a-(4+b)/6+(h)*e-ly/20)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖ ≤ C*Z^(a-(4+b)/6-h/600)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro slotEll hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=> Z^(slotEll j)) (fun _ _=> Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J slotEll hell Z a e hZ,source_z_scale_identity J slotEll hell Z a hZ] at hh
  exact hh

lemma source_w_strict_exponent (β e : ℝ) (he : e ≤ 1/1000) :
    (β+e)-(4+b)/6+(h)*e-ly/20 ≤ β-(4+b)/6-1/4000 := by nlinarith [Submission20261012.Global.h_interval, Submission20261012.Global.ly_coarse, Submission20261012.Global.Transport.theta_bounds]

lemma source_z_strict_exponent (β e : ℝ) (he : e ≤ 1/1000) :
    (β+e)-(4+b)/6-h/600 ≤ β-(4+b)/6-1/4000 := by nlinarith [Submission20261012.Global.h_interval, Submission20261012.Global.ly_coarse, Submission20261012.Global.Transport.theta_bounds]

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e ≤ 1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (theta :ℝ) 2) :
    ∃C : ℝ,0< C ∧ ∀(slotEll : ι→ℝ),(∑j∈J,slotEll j=ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1 ≤ Z→
    (∀j∈J,480 ≤ c*Z^(slotEll j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(slotEll j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(slotEll j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> verticalIntegral (1/6+e)
      (fun z=> verticalIntegral (19/20) (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤ 
      C/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=> verticalIntegral (33/200) (fun z=> K0 s 1 z*LFunction π (6*z)))‖ ≤ 
      C*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by nlinarith [Submission20261012.Global.h_interval, Submission20261012.Global.ly_coarse, Submission20261012.Global.Transport.theta_bounds]) he (by nlinarith [Submission20261012.Global.h_interval, Submission20261012.Global.ly_coarse, Submission20261012.Global.Transport.theta_bounds])
  refine ⟨C,hC,?_⟩
  intro slotEll hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound slotEll hell W hW hsupp T hT Z (by nlinarith [Submission20261012.Global.h_interval, Submission20261012.Global.ly_coarse, Submission20261012.Global.Transport.theta_bounds]) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end Submission20261012.Global.Transport.PrincipalRemainderBounds

end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderBounds -/
