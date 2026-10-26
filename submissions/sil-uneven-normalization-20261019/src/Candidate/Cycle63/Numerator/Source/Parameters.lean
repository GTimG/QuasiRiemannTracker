import Candidate.Cycle63.Numerator.Fourth.Active
import Candidate.Cycle63.Assembly.Count.BaselineMoments
import Candidate.Cycle63.Numerator.Source.ActualBin
import Candidate.Cycle25.Numerator.PhysicalFront

/- Original module: Candidate.Cycle63.Numerator.Fourth.Public. -/
section

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Cycle63.Numerator.Fourth
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open Cycle63DetectorCount
open Cycle63.Arithmetic
open ProbeRowRadicalConductor CenteredMomentDetectorPlainFiberSource
open Cycle25.Numerator Cycle25.Weighted.Numerator

/-- The affine carrier on the actual new slot dictionary and original physical
source. The projection contains no old high-row length or total. -/
abbrev BaselineAffineAt (D : BaselineData) (F : BaselineSourceData D)
    (bΦ mesh ε U : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  AffineAt F bΦ mesh ε U degree control C

/-- Direct public specialization to the baseline source on the new geometry. -/
theorem baseline_active_box_fourth (D : BaselineData) (F : BaselineSourceData D)
    (hb : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤ D.momentKappa)
    (bΦ mesh affineError : ℝ) (hAffineError : 0<affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh affineError U di control Ci)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hbcut:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,dMinus ≤ d → d ≤ dPlus →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ mesh) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ Capacity.scheduledCapacity d (2*((j:ℝ)*boxWidth+boxWidth+annulusSlack)) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(y/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  exact affine_active_box_fourth F D.momentKappa D.momentKappa_lo D.momentKappa_hi hκβ hb
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput G loss boxWidth annulusSlack b
    hloss hbox hann hbcut hsmall

lemma rescaled_slot_mesh (D : BaselineData) (mesh d : ℝ)
    (hd : (1/200:ℝ)≤ d) (hfine : ∀j,D.length j≤ mesh/200) :
    ∀j,D.length j/d≤ mesh := by
  have hp:0<d:=by linarith
  have hmesh:0≤ mesh:=by
    by_cases hn:D.N=0
    · have ht:=D.slots_sum
      have he:=Cycle63.Arithmetic.ell_pos
      simp [hn] at ht
      linarith
    · have hN:0<D.N:=Nat.pos_of_ne_zero hn
      have hlength:=D.slots_pos ⟨0,hN⟩
      have hh:=hfine ⟨0,hN⟩
      linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hmul:=mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

lemma source_slot_power (Z d width : ℝ) (hZ : 0<Z) (hd : d≠0) :
    (Z^d)^(width/d)=Z^width := by
  rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ width hd]

end Cycle63.Numerator.Fourth
end

/- Original module: Candidate.Cycle63.Numerator.Source.Parameters. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic
open OAI OAI.SevenEighths Cycle63DetectorCount HeckeFamily

lemma source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤a) (hatop : a≤7/8) :
    0≤(2*a-1)/2 ∧ (2*a-1)/2≤1 ∧
    1-a-6*D.e≤1/2-(2*a-1)/2 ∧
    -(1/100:ℝ)≤1/2-(2*a-1)/2 ∧
    1+4*D.e≤(a+16*D.e)+(1/2-(2*a-1)/2) := by
  have he:=D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

lemma source_complex_profile_norm (D : BaselineData) (F : BaselineSourceData D) (r : ℝ) :
    ‖F.W r‖≤1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded r).1]
  exact (F.bounded r).2

lemma source_cutoff_le_base (b : ℝ) (hb : 0≤b) :
    ∀ᶠU:ℝ in atTop,1<U ∧ ∀d:ℝ,(1/2:ℝ)≤d → b*U^(y/d)≤U := by
  have he : ∀ᶠU:ℝ in atTop,b≤U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0<d:=by linarith
  have hy : y/d≤19/20 := by
    apply (div_le_iff₀ hdp).mpr
    have hy : y≤19/40:=by norm_num [y]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end Cycle63.Numerator.Source
end
