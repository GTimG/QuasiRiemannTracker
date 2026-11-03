/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalLow/LowWindowBound.lean
Original SHA-256: 4794add614e5acde52c9a5c680829cbc80c3fbbb76aeeae180529ab75de69607
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowWindowBound
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalLow.LowCommonBound

/-!
Transport of OpenAI Detector/LowWindowBound.lean, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; license: upstream-config/LICENSE.
The physical objects and the generic analytic inputs are unchanged.
-/

namespace OAI
noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem transport_original_ray_compensatedPhysicalProbe_low_loss
    (totalWidth x y : ℝ) (hE0 : 0≤totalWidth) (hE1 : totalWidth≤1/5)
    (hsumXY : x+y=1-totalWidth) (hxy : x<y) (hgrow : totalWidth<2*x-y)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤totalWidth) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^x) (Z^y) Z‖≤C*Z^((x/2+(y-x)/12)+loss) := by
  let D := max 1 B
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=>W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := transport_original_ray_compensatedPhysicalProbe_low totalWidth x y hE0 hE1 hsumXY hxy hgrow η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=>Z^(ell i))
    (Z^x) (Z^y) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤D^K*(C*Z^((x/2+(y-x)/12)+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤D^K*(C*Z^((x/2+(y-x)/12)+loss)) := by gcongr
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
