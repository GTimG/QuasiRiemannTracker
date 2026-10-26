/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B003
import Submissions.certb_local_20261013.Bundles.B030
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.certb_local_20261013.Bundles.B037
import Submissions.certb_local_20261013.Bundles.B038
import Submissions.certb_local_20261013.Bundles.B043
import Submissions.certb_local_20261013.Bundles.B045
import Submissions.certb_local_20261013.Bundles.B051
import Submissions.certb_local_20261013.Bundles.B052
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalTails
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowRetainedBudget

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowCentralGeometry ; sha256 0bbf0a4fafc6adea1d540dd4362d3479f0849f30ff181f515284d071a6f0f5b7 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowCentralGeometry.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical
namespace LowProbe
open ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0< Z) (slots : Fin K→Finset ActualEisensteinCubic.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) := by
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,max 1 b*Z^(ell i.val) := Finset.prod_le_prod₀
      (fun _ _=> by unfold elementNorm;positivity)
      (fun i _=>(hslots i.val _ (p i).property).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    _=(max 1 b)^J.card*Z^(lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤_ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

theorem eventually_low_selected_caps {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤ Z^(lowSelectedLength ell J+ε/2) := by
  have hp : 0<ε/2 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro J
  apply (lowSelectedCaps_product ell hell J Z b hZ.le).trans
  calc
    _≤ Z^(ε/2)*Z^(lowSelectedLength ell J) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring

def lowCentralShift (Z T ell0 : ℝ) : ℝ := Real.logb Z T-1-ell0

lemma lowCentralShift_scale (Z T ell0 : ℝ) (hZ : 1< Z) (hT : 0< T) :
    Z^(1+ell0+lowCentralShift Z T ell0)=T := by
  rw [lowCentralShift,show 1+ell0+(Real.logb Z T-1-ell0)=Real.logb Z T by ring]
  exact Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hT

lemma lowCentralShift_bound (Z T ell ε : ℝ) (hZ : 1< Z) (hT : 0< T) (hε : 0≤ε)
    (hlo : Z^(1+ell-ε/2)≤ T) (hhi : T≤ Z^(1+ell+ε/2)) :
    |lowCentralShift Z T (ell+ε/2)|≤ε := by
  have he := lowCentralShift_scale Z T (ell+ε/2) hZ hT
  rw [←he,Real.rpow_le_rpow_left_iff hZ] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma lowCentral_ratio_bounds (Z T ell ε : ℝ) (hZ : 0< Z)
    (hlo : Z^(-ε/2)≤ T/Z^(1+ell)) (hhi : T/Z^(1+ell)≤ Z^(ε/2)) :
    Z^(1+ell-ε/2)≤ T ∧ T≤ Z^(1+ell+ε/2) := by
  constructor
  · have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hlo
    convert hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hhi
    convert hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowCentralGeometry -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowUnselectedMass ; sha256 e565bcd3c0ad1857fedc2d77f5d5dc6dc07037eb5050e2160db15d3d2c794d68 -/
section




/-! Adapted from OpenAI/math family003, pinned original module Detector.LowUnselectedMass.
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
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0< C ∧
    ∀(T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤ C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2:ℝ)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=> I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2:ℝ)) := by
    rw [Finset.sum_image (fun P _ Q _ h=> hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=> elementNorm a.val^(-(3/2:ℝ)))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

lemma lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖ =
      ∏i : J,elementNorm (a i).val^(-(3/2:ℝ))*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
    (fun i : J=> elementNorm (a i).val) (fun i _=> by unfold elementNorm;positivity)]

theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤ M) :
    ∃C : ℝ,0< C ∧ ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤ M)→
      (∑a : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P a‖)≤ C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_three_halves
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=> canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-(3/2:ℝ))*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=> Finset.sum_nonneg (fun a _=> mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ))*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ)))*M := (Finset.sum_mul ..).symm
        _≤ C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=> by positivity) (fun _ _=> le_max_right _ _)
    _≤_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

/-- The unselected prime norm supplies the exact power needed by the relaxed energy. -/
theorem lowUnselectedMass_decay (K : ℕ) (M a : ℝ) (hM : 0≤ M) (ha : 0< a) :
    ∃C : ℝ,0< C ∧ ∀(ell : Fin K→ℝ)(Z : ℝ),0< Z→
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
    (∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤ elementNorm n)→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
    (∀i x,‖W i x‖≤ M)→
    (∑p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P p‖*
        elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤ C*Z^(-lowUnselectedLength ell J/2) := by
  obtain ⟨C,hC,hbound⟩ := lowUnselectedMass_bound K M hM
  let c := (min 1 a)^K
  have hc : 0< c := by dsimp [c];positivity
  refine ⟨C*c^(-(1/2:ℝ)),by positivity,?_⟩
  intro ell Z hZ T hT hlower J W P hW
  have hp (p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J) :
      elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ))≤ c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
    have hh := lowUnselectedProduct_norm_lower ell a Z ha hZ _ hlower J p
    have hb := Real.rpow_le_rpow_of_nonpos (show 0< c*Z^(lowUnselectedLength ell J) by positivity) hh (show -(1/2:ℝ)≤0 by norm_num)
    have hid : (c*Z^(lowUnselectedLength ell J))^(-(1/2:ℝ))=c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le]
      congr 2
      ring
    exact hb.trans_eq hid
  calc
    _≤∑p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P p‖*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
        Finset.sum_le_sum (fun p _=> mul_le_mul_of_nonneg_left (hp p) (norm_nonneg _))
    _=(∑p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P p‖)*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) := (Finset.sum_mul ..).symm
    _≤ C*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
      mul_le_mul_of_nonneg_right (hbound T hT J W P hW) (by positivity)
    _=_ := by ring

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowUnselectedMass -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowRetainedBudget ; sha256 59eff93807509b4392ed2b072fa4891238ccd8ebf0935517c4a6dd1212721efe -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowRetainedBudget.
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

theorem original_low_sector_retained_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤ Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
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
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_retained_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0< Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤ Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith)) (by positivity)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowRetainedBudget -/

/- BEGIN ORIGINAL MODULE Global.Numerator.BoxGeometry ; sha256 432cc00aaa22947d7422fbc9862033170100518c2cc6da68ba72046415e078d9 -/
section




/-! Exact scale and capacity bookkeeping for finite coefficient-dilation boxes. -/
noncomputable section
open scoped BigOperators Classical
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator

lemma physical_y_range (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension) :
    (1/2:ℝ) < Submission20261012.Global.ly/d ∧ Submission20261012.Global.ly/d < 1 := by
  have hdp : 0 < d := by linarith
  constructor
  · apply (lt_div_iff₀ hdp).mpr
    have hh := Submission20261012.Global.extended_numerator_short
    linarith
  · apply (div_lt_one hdp).mpr
    exact Submission20261012.Global.ly_lt_half.trans_le hd

/-- The coarse finite box range suffices: the maximum reflected length remains
below the fixed L=2 empty-slot endpoint, uniformly in all actual high dyads. -/
theorem reflected_box_geometry (d v boxWidth annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension)
    (hv:0 ≤ v) (hvmax:v ≤ 1+boxWidth) (hbox:0 ≤ boxWidth)
    (hann:0 ≤ annulusSlack) (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    0 ≤ 1-Submission20261012.Global.ly/d+v+boxWidth ∧
      (1-Submission20261012.Global.ly/d+v+boxWidth)+annulusSlack ≤ 2 := by
  obtain ⟨hylo,hyhi⟩ := physical_y_range d hd hdmax
  constructor <;> linarith

/-- A dilation-box upper edge bounds the combined primitive-plus-redundant
conductor relative to the actual original scale Y/N. -/
theorem combined_scale_of_dilation_box (U C Cu rowSize N y v boxWidth:ℝ)
    (hU:0 < U) (hC:0 < C) (hrow:0 < rowSize) (hrowU:rowSize ≤ U) (hN:0 < N)
    (hbox:max 1 (Cu*N/(C*rowSize)) ≤ U^(v+boxWidth)) :
    Cu ≤ C*U^(1-y+v+boxWidth)*(U^y/N) := by
  have hb : Cu*N ≤ U^(v+boxWidth)*(C*rowSize) :=
    (div_le_iff₀ (mul_pos hC hrow)).mp ((le_max_right _ _).trans hbox)
  have hprod : Cu*N ≤ C*(U^(v+boxWidth)*U) := by
    calc
      _ ≤ U^(v+boxWidth)*(C*rowSize) := hb
      _ ≤ U^(v+boxWidth)*(C*U) := by gcongr
      _ = _ := by ring
  have hpow : U^(1-y+v+boxWidth)*U^y = U^(v+boxWidth)*U := by
    rw [←Real.rpow_add hU]
    calc
      _ = U^(v+boxWidth+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one]
  have he : C*U^(1-y+v+boxWidth)*(U^y/N) =
      (C*(U^(v+boxWidth)*U))/N := by
    calc
      _ = (C*(U^(1-y+v+boxWidth)*U^y))/N := by ring
      _ = _ := by rw [hpow]
  rw [he]
  exact (le_div_iff₀ hN).mpr hprod

lemma capacity_shift_exact (kap y v boxWidth annulusSlack:ℝ) :
    selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) =
      selectedCapacity kap ((2*y-1)/(6*kap)) (v+boxWidth+annulusSlack) := by
  unfold selectedCapacity
  congr 1
  ring

/-- A positive selected family fits the reflected two-plain capacity. If the
capacity has saturated to zero, positivity forces the selected family empty. -/
theorem physical_reflected_capacity_or_empty {ι:Type*} (T:Finset ι)
    (width:ι→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0< kap)
    (hw:∀i∈T,0 < width i)
    (hselected:(∑i∈T,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i∈T,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw :=
      max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 :=
      max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun j hj=>(hw j hj).le) hi
    linarith [hw i hi]

/-- The annular tolerance changes the selected-slot exponent by exactly its
linear capacity cost; it can be included in the final small loss budget. -/
lemma annular_capacity_saving_loss (kap q y annulusSlack:ℝ) :
    -q*((2*y-1)/(6*kap)-annulusSlack/(3*kap))/2 =
      -q*((2*y-1)/(6*kap))/2+q*annulusSlack/(6*kap) := by ring


/-- A convenient uniform positive margin for the selected base capacity. -/
lemma physical_y_strong_lower (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension) :
    (11/20:ℝ) < Submission20261012.Global.ly/d := by
  have hdp : 0 < d := by linarith
  apply (lt_div_iff₀ hdp).mpr
  have hh := Submission20261012.Global.h_interval
  have hy := Submission20261012.Global.ly_coarse
  norm_num [Submission20261012.Global.rowExtension, Endpoint.zeta] at *
  linarith

lemma shifted_base_capacity_pos (kap d annulusSlack:ℝ)
    (hkap:0< kap) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension)
    (hann:annulusSlack ≤ 1/100) :
    0 < (2*(Submission20261012.Global.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) := by
  have hh := physical_y_strong_lower d hd hdmax
  have hid : (2*(Submission20261012.Global.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) =
      (2*(Submission20261012.Global.ly/d)-1-2*annulusSlack)/(6*kap) := by ring
  rw [hid]
  exact div_pos (by linarith) (by positivity)

def coefficientBoxCount (xi:ℝ) : ℕ := ⌈1/xi⌉₊

lemma coefficientBoxCount_extent (xi:ℝ) (hxi:0 < xi) :
    1 ≤ (coefficientBoxCount xi:ℝ)*xi ∧
      (coefficientBoxCount xi:ℝ)*xi < 1+xi := by
  have hlo := Nat.le_ceil (1/xi)
  have hhi := Nat.ceil_lt_add_one (by positivity:(0:ℝ) ≤ 1/xi)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlo hxi.le
    simpa only [coefficientBoxCount,div_mul_cancel₀ _ hxi.ne'] using hh
  · have hh := mul_lt_mul_of_pos_right hhi hxi
    dsimp [coefficientBoxCount]
    simpa only [add_mul,div_mul_cancel₀ _ hxi.ne',one_mul] using hh

lemma coefficient_box_index_range (xi:ℝ) (hxi:0 < xi) (j:ℕ)
    (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ (j:ℝ)*xi ∧ (j:ℝ)*xi ≤ 1+xi := by
  have hjn : j ≤ coefficientBoxCount xi := by have := Finset.mem_range.mp hj; omega
  have hjr : (j:ℝ) ≤ (coefficientBoxCount xi:ℝ) := by exact_mod_cast hjn
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hxi.le,
    (mul_le_mul_of_nonneg_right hjr hxi.le).trans (coefficientBoxCount_extent xi hxi).2.le⟩

/-- A fixed source cutoff fits below U uniformly in every weighted high dyad. -/
theorem eventually_physical_cutoff_le_base (b:ℝ) (hb:0 ≤ b) :
    ∀ᶠU:ℝ in Filter.atTop, 1 < U ∧ ∀d:ℝ,(1/2:ℝ) ≤ d →
      b*U^(Submission20261012.Global.ly/d) ≤ U := by
  have he : ∀ᶠU:ℝ in Filter.atTop, b ≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).eventually (Filter.eventually_ge_atTop _)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0 < d := by linarith
  have hy : Submission20261012.Global.ly/d ≤ 19/20 := by
    apply (div_le_iff₀ hdp).mpr
    linarith [Submission20261012.Global.ly_coarse.2]
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := by
      exact mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hU.le hy)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by
      rw [←Real.rpow_add (zero_lt_one.trans hU)]
      norm_num

/-- The finite box range and the reflected scale range use the same actual
parameters; no unbounded coefficient tail remains after the source cutoff. -/
theorem physical_coefficient_box_geometry (d xi annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension)
    (hxi:0 < xi) (hann:0 ≤ annulusSlack) (hsmall:2*xi+annulusSlack ≤ 1/2)
    (j:ℕ) (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ 1-Submission20261012.Global.ly/d+(j:ℝ)*xi+xi ∧
      (1-Submission20261012.Global.ly/d+(j:ℝ)*xi+xi)+annulusSlack ≤ 2 := by
  obtain ⟨hv,hvmax⟩ := coefficient_box_index_range xi hxi j hj
  exact reflected_box_geometry d ((j:ℝ)*xi) xi annulusSlack hd hdmax hv hvmax hxi.le hann hsmall


lemma physical_reflected_capacity_or_empty_subtype {ι:Type*} (T:Finset ι)
    (width:T→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0< kap)
    (hw:∀i,0 < width i)
    (hselected:(∑i,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw := max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 := max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

end Submission20261012.Global.Numerator

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.BoxGeometry -/

/- BEGIN ORIGINAL MODULE Global.Transport.CanonicalTails ; sha256 32f18a4597bc1e53154602522bdc3d23013e79dd8cb01cbd55ac819c45116012 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/





open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
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
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=> mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=> Z^(length i)) W0 W1
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=> Z^(length i)) W0 W1
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=> Z^(length i)) W0 W1
      (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> finitePhysicalRows S hmax η (dyadicRows (Z^((Submission20261012.Global.h:ℝ)+ζ)) n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((Submission20261012.Global.h:ℝ)+ζ)) n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨C,hC,hmain⟩ := large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((Submission20261012.Global.h:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CanonicalTails -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeFloorSaving ; sha256 be06840c66fedf65f851a7ac4f186c22c7568836dc8c858d6f670cb2815a2b10 -/
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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem savingFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_cube_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0 < dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu)
    (saving : ℝ) (_hsaving : 0 < saving)
    (htotal : 26*e+(N+8)*eps+loss+mesh*Submission20261012.Global.ell+nu+saving≤1/100) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → v≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (savingFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(Submission20261012.Global.signal Submission20261012.Global.theta-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := actual_normalized_floor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv hvhi rows hrows hnorm i hi hbin
  dsimp only
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := Submission20261012.Global.Transport.floor_source_margin hvhi
  have hl := Submission20261012.Global.Transport.floor_loss_bound N (loss:=loss) (mesh:=mesh) (hvhi.trans Submission20261012.Global.extended_h_lt_one.le) he.le heps.le
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
  linarith

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CubeFloorSaving -/
