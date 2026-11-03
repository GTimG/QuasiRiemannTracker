/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalTail/PhysicalSmallTail.lean
Original SHA-256: 1134f75543575c2173b9b144951a6b34b86fb2f7b31e545183dcd3686384d371
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalSmallTail
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalTail.TailScales
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalTail.SmallTail

/-! Transport of the matching OpenAI PrimeRows source, pinned commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; license: upstream-config/LICENSE.
The original physical objects are retained, with tuned geometric scales. -/

namespace LW56e2.Transport.PhysicalTail

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem transport_small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : TunedCandidate.B≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=TunedCandidate.ell →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(TunedCandidate.signal HeckeZeroSupremum.beta-1/20+8*e) := by
  obtain ⟨C,hC,hmain⟩ := transport_small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z (max HeckeZeroSupremum.beta (7/8)+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z‖≤N*g n := norm_finitePhysicalRows_le_absolute
    e (max HeckeZeroSupremum.beta (7/8)+8*e) (1/2) (17/50) he he' (by linarith [le_max_right HeckeZeroSupremum.beta (7/8:ℝ)])
    (by linarith [le_max_left HeckeZeroSupremum.beta (7/8:ℝ)])
    (by have hm : max HeckeZeroSupremum.beta (7/8:ℝ)≤1 := max_le HeckeZeroSupremum.beta_le_one (by norm_num);linarith) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(TunedCandidate.signal HeckeZeroSupremum.beta-1/20+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(TunedCandidate.signal HeckeZeroSupremum.beta-1/20+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end

end LW56e2.Transport.PhysicalTail
