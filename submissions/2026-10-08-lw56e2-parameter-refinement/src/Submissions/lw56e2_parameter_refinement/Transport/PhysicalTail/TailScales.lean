/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalTail/TailScales.lean
Original SHA-256: e306456e6acccd8d5875d890470e633ab94f021ca51fe9f969c532d82e4516ca
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.lw56e2_parameter_refinement.Transport.TunedCandidate

/-! Actual source-scale identities for the tuned geometry. The small contour
stays at max(beta,7/8)+8e, within the official analytic domain. The geometric
slack pays for this displacement; no extension of that dyad theorem is used.
Source: OpenAI003 commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
License: upstream-config/LICENSE. -/

namespace LW56e2.Transport.PhysicalTail
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths ProbeHighRowFamily

def largeBase : ℝ := 1+TunedCandidate.lx/2+TunedCandidate.ly

theorem tuned_h_lower : (1/100:ℝ)<TunedCandidate.h := by
  rw [TunedCandidate.geometry_values.2.2.2]
  norm_num

theorem tuned_h_upper : TunedCandidate.h+1/48≤1 := by
  rw [TunedCandidate.geometry_values.2.2.2]
  norm_num

theorem tuned_total_le_one : TunedCandidate.ell≤1 := by
  rw [TunedCandidate.geometry_values.1]
  norm_num

lemma transport_small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z)
    (length : Fin K→ℝ) (hlength : ∑i,length i=TunedCandidate.ell) (beta e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^TunedCandidate.lx)^(1/2-(17/50:ℝ))*
        Z^(max beta (7/8)+8*e+(17/50:ℝ)-1)*
        (Z^TunedCandidate.ly)^((1/2:ℝ)-1))=
      Z^(max beta (7/8)+8*e-1+TunedCandidate.lx/2-TunedCandidate.ly/2+
        TunedCandidate.h*(17/50)) := by
  rw [physical_scale_power Z hZ,hlength,←TunedCandidate.h_eq]
  congr 1
  ring

lemma transport_small_source_scale_bound {K : ℕ} (Z : ℝ) (hZ : 1≤Z)
    (length : Fin K→ℝ) (hlength : ∑i,length i=TunedCandidate.ell)
    (beta e : ℝ) (hbeta : TunedCandidate.B≤beta) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^TunedCandidate.lx)^(1/2-(17/50:ℝ))*
        Z^(max beta (7/8)+8*e+(17/50:ℝ)-1)*
        (Z^TunedCandidate.ly)^((1/2:ℝ)-1))≤
      Z^(TunedCandidate.signal beta-7/100+8*e) := by
  rw [transport_small_source_scale Z (lt_of_lt_of_le zero_lt_one hZ) length hlength]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hmax : max beta (7/8)≤beta+(7/8-TunedCandidate.B) := by
    apply max_le
    · linarith [TunedCandidate.boundary_improvement]
    · linarith
  rw [TunedCandidate.signal_eq]
  rcases TunedCandidate.geometry_values with ⟨he,hx,hy,hh⟩
  rw [hx,hy,hh]
  rw [TunedCandidate.boundary_value] at hmax
  norm_num [TunedCandidate.b]
  linarith

lemma transport_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z)
    (length : Fin K→ℝ) (hlength : ∑i,length i=TunedCandidate.ell) (r : ℝ) :
    (∏i,(Z^(length i))^r)*
      ((Z^TunedCandidate.lx)^(1/2-r)*Z^(2+r-1)*(Z^TunedCandidate.ly)^((2:ℝ)-1))=
      Z^(largeBase+TunedCandidate.h*r) := by
  rw [physical_scale_power Z hZ,hlength,←TunedCandidate.h_eq]
  congr 1
  dsimp [largeBase]
  ring

end
end LW56e2.Transport.PhysicalTail
