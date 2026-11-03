/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighLargeTail.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighLargeDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeTail

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open AsymmetricGeometry
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

set_option maxHeartbeats 600000

theorem large_physical_dyads_summable_with_perturbed_lengths (K : ℕ) (δ a b B r ζ t : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r) (hr' : 8/5+δ<r) (hζ : 0<ζ)
    (ht : 0 ≤ t)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^(rowBase+3*t/2+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^(rowBase+3*t/2+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ)+t →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(xBase-t/2:ℝ)) (Z^(yBase-t/2:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(xBase-t/2:ℝ)) (Z^(yBase-t/2:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*
        Z^(((53/32:ℝ)-skew/2)+(rowBase+3*t/2+ζ)*(8/5+δ)-ζ*r-3*t/4) := by
  obtain ⟨C,hC,hmain⟩ := large_physical_dyad_bound_with_perturbed_lengths K δ a b B r t hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrowBase : 0 < rowBase := by norm_num [rowBase, skew]
  let f : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(xBase-t/2:ℝ)) (Z^(yBase-t/2:ℝ)) Z 2 2 r
  let g0 : ℕ→ℝ := fun n=>Z^(((53/32:ℝ)-skew/2)+rowBase*r)*
    (Z^(rowBase+(3*t/2+ζ))*(2:ℝ)^n)^(8/5+δ-r)
  let g : ℕ→ℝ := fun n=>Z^((3*r/2-3/4)*t)*g0 n
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤f n := absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤A*g n := by
    have hUn : 1≤Z^(rowBase+3*t/2+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^(rowBase+3*t/2+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    have hpow : Z^(((53/32:ℝ)-skew/2)+rowBase*r+(3*r/2-3/4)*t)=
        Z^((3*r/2-3/4)*t)*Z^(((53/32:ℝ)-skew/2)+rowBase*r) := by
      rw [←Real.rpow_add hZ0]
      congr 1
      ring
    calc
      f n ≤ A*(Z^(((53/32:ℝ)-skew/2)+rowBase*r+(3*r/2-3/4)*t)*
          (Z^(rowBase+3*t/2+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
        simpa only [f,A,mul_assoc] using hh
      _ = A*g n := by rw [hpow]; dsimp [g,g0]; ring
  have hg0 : Summable g0 := show_large_geometric_summable Z ((53/32:ℝ)-skew/2) rowBase (3*t/2+ζ) δ r hZ0 hr'
  have hg : Summable g := hg0.mul_left _
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^(((53/32:ℝ)-skew/2)+(rowBase+3*t/2+ζ)*(8/5+δ)-ζ*r-3*t/4)*
        (1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      have hgsum : (∑'n,g n) = Z^((3*r/2-3/4)*t) *
          (Z^(((53/32:ℝ)-skew/2)+(rowBase+(3*t/2+ζ))*(8/5+δ)-(3*t/2+ζ)*r) *
            (1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
        dsimp only [g]
        rw [tsum_mul_left]
        rw [show (∑'n,g0 n)=_ from sum_large_geometric_scale Z ((53/32:ℝ)-skew/2) rowBase (3*t/2+ζ) δ r hZ0 hr']
      rw [hgsum]
      have hpow : Z^((3*r/2-3/4)*t)*
          Z^(((53/32:ℝ)-skew/2)+(rowBase+(3*t/2+ζ))*(8/5+δ)-(3*t/2+ζ)*r)=
          Z^(((53/32:ℝ)-skew/2)+(rowBase+3*t/2+ζ)*(8/5+δ)-ζ*r-3*t/4) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring_nf
      calc
        _ = A*((Z^((3*r/2-3/4)*t)*
            Z^(((53/32:ℝ)-skew/2)+(rowBase+(3*t/2+ζ))*(8/5+δ)-(3*t/2+ζ)*r))*
            (1-(2:ℝ)^(8/5+δ-r))⁻¹) := by ring
        _ = _ := by rw [hpow]
    _ = _ := by dsimp [A];ring


end SevenEighths.ProbeHighRowFamily
end

end OAI
