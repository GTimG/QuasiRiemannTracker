/- One global native dyad box for all actual rebased LOW sources. Apache-2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainAbsoluteBox
import Candidate.Research.RecursiveAffine.SourceContextHeight

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63InitialMass Cycle153SourceSchedule CenteredMomentDyadicCount
open Filter

private theorem actual_indices_mono {a b c d : ℝ}
    (ha : 0<a)(hb : 0<b)(hc : 0<c)(hd : 0<d)(hca : c ≤ a)(hbd : b ≤ d) :
    indices a b ⊆ indices c d := by
  intro n hn
  rw [mem_indices_iff_scale c d hc hd]
  have h:=(mem_indices_iff_scale a b ha hb n).mp hn
  exact ⟨hca.trans h.1,h.2.trans (by linarith only [hbd])⟩

/-- Enlarging the local actual base and the ambient cardinality embeds
all four literal native dyad coordinates in one fixed global source box.
The box includes every actual first-height/configuration choice. -/
theorem geometryMainAbsoluteBox_global
    (Z U B loss b : ℝ)(n N : ℕ)(hZ : 1<Z)(hU : 0<U)(hU1 : U ≤ 1)
    (hB : 0 ≤ B)(hloss : 0 ≤ loss)(hb : 1 ≤ b)(hn : n ≤ N) :
    geometryMainAbsoluteBox (Z^U) n B loss b ⊆ geometryMainAbsoluteBox Z N B loss b := by
  have hz:=zero_lt_one.trans hZ
  have hlocal:=Real.rpow_pos_of_pos hz U
  have hp (a : ℝ)(ha : 0 ≤ a) : (Z^U)^a ≤ Z^a := by
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    exact mul_le_of_le_one_left ha hU1
  have hm (a : ℝ)(ha : 0 ≤ a) : Z^(-a) ≤ (Z^U)^(-a) := by
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith only [hU1,ha]
  have hbpow : b^(2*n) ≤ b^(2*N) := pow_le_pow_right₀ hb (Nat.mul_le_mul_left 2 hn)
  have hcoeff : max 1 (4*b^(2*n)) ≤ max 1 (4*b^(2*N)) :=
    max_le_max_left _ (mul_le_mul_of_nonneg_left hbpow (by norm_num))
  intro x hx
  have hi:=Fintype.mem_piFinset.mp hx
  apply Fintype.mem_piFinset.mpr
  intro i
  fin_cases i
  · apply actual_indices_mono (Real.rpow_pos_of_pos hlocal _) (Real.rpow_pos_of_pos hlocal _)
      (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _) (hm _ (by positivity))
      (hp _ (by positivity))
    exact hi 0
  · apply actual_indices_mono (by norm_num) (mul_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
        (Real.rpow_pos_of_pos hlocal _)) (by norm_num)
      (mul_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) (Real.rpow_pos_of_pos hz _))
      le_rfl (mul_le_mul hcoeff (hp _ (by positivity))
        (Real.rpow_nonneg hlocal.le _) (by positivity))
    exact hi 1
  · apply actual_indices_mono (by norm_num) (Real.rpow_pos_of_pos hlocal _) (by norm_num)
      (Real.rpow_pos_of_pos hz _) le_rfl (hp _ (by positivity))
    exact hi 2
  · apply actual_indices_mono (by norm_num) (Real.rpow_pos_of_pos hlocal _) (by norm_num)
      (Real.rpow_pos_of_pos hz _) le_rfl (hp _ (by positivity))
    exact hi 3

/-- The one original-base box used for every historical step. -/
def rootNativeDyadBox (Z : ℝ)(N : ℕ) : Finset (Fin 4→ℤ):=
  geometryMainAbsoluteBox Z N 4 (nativeMu/8) (9/4)

theorem local_native_dyad_subset_root (Z U : ℝ)(n N : ℕ)
    (hZ : 1<Z)(hU : 0<U)(hU1 : U ≤ 1)(hn : n ≤ N) :
    geometryMainAbsoluteBox (Z^U) n 4 (nativeMu/8) (9/4) ⊆ rootNativeDyadBox Z N :=
  geometryMainAbsoluteBox_global Z U 4 (nativeMu/8) (9/4) n N hZ hU hU1 (by norm_num)
    (div_nonneg nativeMu_pos.le (by norm_num)) (by norm_num) hn

/-- The cardinal of the actual uniform native box is subpower. This is
native absolute-source geometry, not an assumed bound on a history set. -/
theorem root_native_dyad_subpower (N : ℕ)(eps : ℝ)(heps : 0<eps) :
    ∃Cb : ℝ,0<Cb ∧∀ᶠZ : ℝ in atTop,1<Z ∧
      ((rootNativeDyadBox Z N).card:ℝ) ≤ Cb*Z^eps := by
  obtain ⟨Cb,hCb,hreceipt⟩:=eventual_actual_geometry_main_absolute_box N 4 (nativeMu/8)
    (9/4) (9/4) (nativeMu/64) eps (by norm_num)
    (div_pos nativeMu_pos (by norm_num)) (by norm_num) (by norm_num)
    (div_nonneg nativeMu_pos.le (by norm_num)) (by nlinarith only [nativeMu_pos]) heps
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hreceipt] with Z hZ
  exact ⟨hZ.1,hZ.2.1⟩

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.local_native_dyad_subset_root
#print axioms OAI.SevenEighths.Cycle153Reachable.root_native_dyad_subpower
