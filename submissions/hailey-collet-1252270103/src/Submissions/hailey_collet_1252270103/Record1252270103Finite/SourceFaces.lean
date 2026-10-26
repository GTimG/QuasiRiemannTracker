/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
set_option autoImplicit false
namespace Record1252270103Finite

theorem source_face_before_crossing (n low:Source) (hL:n.L<low.L)
 {s:ℝ} (hs:s≤(crossing n low:ℝ)) :
 (n.B:ℝ)-(n.L:ℝ)*s ≤ (low.B:ℝ)-(low.L:ℝ)*s := by
 have hd : (0:ℝ)<(low.L:ℝ)-(n.L:ℝ) := by exact_mod_cast sub_pos.mpr hL
 have hx : (crossing n low:ℝ)=((low.B:ℝ)-(n.B:ℝ))/((low.L:ℝ)-(n.L:ℝ)) := by
  unfold crossing
  push_cast
  rfl
 rw [hx] at hs
 have hmul := (le_div_iff₀ hd).mp hs
 nlinarith

theorem source_parent_domain_before_crossing (n low:Source) (hL:n.L<low.L)
 (hcap:crossing n low≤low.cap) {m₁ m₂ s:ℝ}
 (hs:s≤(crossing n low:ℝ))
 (hm:m₁+m₂+(n.L:ℝ)*s≤(n.B:ℝ)) :
 m₁+m₂+(low.L:ℝ)*s≤(low.B:ℝ) ∧ s≤(low.cap:ℝ) := by
 have hf := source_face_before_crossing n low hL hs
 have hc : (crossing n low:ℝ)≤(low.cap:ℝ) := by exact_mod_cast hcap
 constructor
 · nlinarith
 · exact le_trans hs hc
#print axioms source_parent_domain_before_crossing
end Record1252270103Finite
