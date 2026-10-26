/- Adapted from the pinned Hailey Collet/OpenAI transport.
Apache-2.0 attribution is retained in each source block.
Only guard class/namespace references are generalized; analytic proof bodies
and original physical objects are preserved.  -/
import Candidate.FourthPower.TransportGeometry
import Candidate.FourthPower.TransportErrors
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.GeometricTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalLargeTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.SmallTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.SmallSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalSmallTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalTails
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalPartition

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LargeDyad -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+(SilFourthPowerTransport.Arithmetic.h:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(SilFourthPowerTransport.Arithmetic.x:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(SilFourthPowerTransport.Arithmetic.y:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [large_source_scale Z hZ0 length hl r];ring

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LargeDyad -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.GeometricTail -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped BigOperators
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily

lemma large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0 < Z) (n : ℕ) :
    Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+(SilFourthPowerTransport.Arithmetic.h:ℝ)*r)*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0 < Z) (hr : 8/5+δ < r) :
    Summable (fun n : ℕ=>Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+(SilFourthPowerTransport.Arithmetic.h:ℝ)*r)*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0 < Z) (hr : 8/5+δ < r) :
    (∑'n : ℕ,Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+(SilFourthPowerTransport.Arithmetic.h:ℝ)*r)*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤r ∧ 8/5+δ < r ∧
      (1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.GeometricTail -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LargeTail -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma absolutePhysicalDyadIntegral_nonneg {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) :
    0≤absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (norm_nonneg _) (physicalDyadNorm_nonneg S hS hmax η R T hT W Yp _ _ _)

theorem large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r) (hr' : 8/5+δ < r) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r) := by
  obtain ⟨C,hC,hmain⟩ := large_physical_dyad_bound K δ a b B r hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [SilFourthPowerTransport.Transport.h_pos])
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r
  let g : ℕ→ℝ := fun n=>Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+(SilFourthPowerTransport.Arithmetic.h:ℝ)*r)*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤f n := absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤A*g n := by
    have hUn : 1≤Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith [SilFourthPowerTransport.Transport.h_pos])) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    simpa only [A,g,mul_assoc] using hh
  have hg : Summable g := large_geometric_summable Z ζ δ r hZ0 hr'
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^((1+SilFourthPowerTransport.Arithmetic.x/2+SilFourthPowerTransport.Arithmetic.y)+((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      rw [show (∑'n,g n)=_ from large_geometric_sum Z ζ δ r hZ0 hr']
    _ = _ := by dsimp [A];ring

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LargeTail -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LargeSaving -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤r ∧ 0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,hr,hr',hpower⟩ := exists_large_tail_line ζ δ saving hζ
  obtain ⟨C,hC,hmain⟩ := large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LargeSaving -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PhysicalLargeTail -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_original_physical_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,C,hr,hC,hmain⟩ := large_physical_tail_arbitrary_saving K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hgs,hgb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℂ := fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z 2 2 r
  have hbnd (n : ℕ) : ‖f n‖≤N*g n := norm_finitePhysicalRows_le_absolute
    (1/2000) 2 2 r (by norm_num) (by norm_num) (by norm_num)
    (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num) (by norm_num) hr
    S hS hmax hfirst η (R n) (fun u hu=>(hR n u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  have hns : Summable (fun n=>‖f n‖) := Summable.of_nonneg_of_le (fun n=>norm_nonneg _) hbnd (hgs.mul_left N)
  refine ⟨hns.of_norm,?_⟩
  calc
    (∑'n,‖f n‖) ≤ ∑'n,N*g n := hns.tsum_le_tsum hbnd (hgs.mul_left N)
    _ = N*(∑'n,g n) := tsum_mul_left
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) := mul_le_mul_of_nonneg_left hgb hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PhysicalLargeTail -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.SmallTail -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z ((7/8:ℝ)+8*e) (1/2) (17/50))
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6)-1/50)+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    ((7/8:ℝ)+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) (by linarith) le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hsmall⟩ := small_dyadic_square_sum
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6))+8*e)
  have hA : 0≤A := by dsimp [A];positivity
  have hbnd (n : ℕ) (hn : n∈F) :
      absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z ((7/8:ℝ)+8*e) (1/2) (17/50)
      ≤A*((2:ℝ)^n)^(2:ℝ) := by
    have hUn : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2:ℝ)^n) hUn (R n) (hR n hn) T hT hdis (fun i=>Z^(length i)) hYp
      W hWS hWB (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))≤((2:ℝ)^n)^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by linarith)
    have hscale := small_source_scale Z hZ0 length hl (7/8) e
    calc
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))*
          Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6))+8*e) := by
        apply hh.trans_eq
        rw [←hscale]
        ring
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(2:ℝ)*
          Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6))+8*e) := by gcongr
      _ = _ := by dsimp [A];ring
  calc
    _ ≤ ∑n∈F,A*((2:ℝ)^n)^(2:ℝ) := Finset.sum_le_sum hbnd
    _ = A*∑n∈F,((2:ℝ)^n)^(2:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(D*(Z^(1/100:ℝ))^(2:ℝ)) := mul_le_mul_of_nonneg_left
      (hsmall (Z^(1/100:ℝ)) (Real.rpow_pos_of_pos hZ0 _) F hF) hA
    _ = _ := by
      dsimp [A]
      rw [←Real.rpow_mul hZ0.le]
      have he : Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6))+8*e)*Z^((1/100:ℝ)*2)=
          Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6)-1/50)+8*e) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = (C*D)*(η.modulus.absNorm:ℝ)^δ*
            (Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6))+8*e)*Z^((1/100:ℝ)*2)) := by ring
        _ = _ := by rw [he]

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.SmallTail -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PhysicalSmallTail -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6)-1/50)+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z ((7/8:ℝ)+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z‖≤N*g n := norm_finitePhysicalRows_le_absolute
    e ((7/8:ℝ)+8*e) (1/2) (17/50) he he' (by linarith) (by linarith)
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6)-1/50)+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6)-1/50)+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end SevenEighths.SilFourthPowerTransportHighRowFamily
end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.PhysicalSmallTail -/

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.CanonicalTails -/
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.SilFourthPowerTransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+SilFourthPowerTransport.Transport.b)/6-(SilFourthPowerTransport.Arithmetic.y/2-SilFourthPowerTransport.Arithmetic.h*(17/50-1/6)-1/50)+8*e) := by
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
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(SilFourthPowerTransport.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(SilFourthPowerTransport.Arithmetic.x:ℝ)) (Z^(SilFourthPowerTransport.Arithmetic.y:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨C,hC,hmain⟩ := large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((SilFourthPowerTransport.Arithmetic.h:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

end SevenEighths.SilFourthPowerTransportHighRowFamily

end

end OAI
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.CanonicalTails -/
