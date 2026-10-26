import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineFinalWeight
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryUniformControls
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 40000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open QuadraticInitialBound CenteredMomentFiniteProfileExceptional Cycle63Physical

private theorem paid_profile_weight_mono
    (p : Profiles (1/4) (9/4)) (S S' : Finset (ℕ×ℕ))
    (C H x y Z e e' : ℝ) (j j' k k' : ℕ)
    (hS : S⊆S') (hC : 0≤C) (hH : 0≤H) (hx : 1≤x) (hy : 1≤y)
    (hZ : 1<Z) (he : e≤e') (hj : j≤j') (hk : k≤k') :
    C*H*(p.control S)^2*x^j*y^k*Z^e ≤
      C*H*(p.control S')^2*x^j'*y^k'*Z^e' := by
  have hp := profile_control_mono p hS
  have hp0 := p.control_nonneg S
  have hx0 := zero_le_one.trans hx
  have hy0 := zero_le_one.trans hy
  have hxp := pow_le_pow_right₀ hx hj
  have hyp := pow_le_pow_right₀ hy hk
  have hzp := Real.rpow_le_rpow_of_exponent_le hZ.le he
  have hsquare := pow_le_pow_left₀ hp0 hp 2
  gcongr

/-- Join the two already-paid branches with the zero/tail remainder. The
prime average and amplifier coefficient occur only in the supplied paid
branch inequalities; this join introduces no additional prime payment. -/
theorem geometry_affine_paid_branch_budget
    (p : Profiles (1/4) (9/4)) (Sm Se : Finset (ℕ×ℕ))
    (budget main error average coefficient Cr Cm Ce H x y Z em ee e : ℝ)
    (jm je km ke : ℕ)
    (hCr : 0≤Cr) (hCm : 0≤Cm) (hCe : 0≤Ce) (hH : 0≤H)
    (hx : 1≤x) (hy : 1≤y) (hZ : 1<Z)
    (hem : em≤e) (hee : ee≤e) (he : 0≤e)
    (hbudget : budget ≤ Cr*H*(p.control {(0,0)})^2*Z^(-(1/20:ℝ)) +
      average*(coefficient*main+error))
    (hmain : average*coefficient*main ≤ Cm*H*(p.control Sm)^2*x^jm*y^km*Z^em)
    (herror : average*error ≤ Ce*H*(p.control Se)^2*x^je*y^ke*Z^ee) :
    let S := ({(0,0)}∪Sm)∪Se
    budget ≤ (Cr+Cm+Ce)*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e := by
  intro S
  have hSm : Sm⊆S := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hSe : Se⊆S := Finset.subset_union_right
  have hS0 : {(0,0)}⊆S := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hm := paid_profile_weight_mono p Sm S Cm H x y Z em e jm (max jm je) km (max km ke)
    hSm hCm hH hx hy hZ hem (le_max_left _ _) (le_max_left _ _)
  have herr := paid_profile_weight_mono p Se S Ce H x y Z ee e je (max jm je) ke (max km ke)
    hSe hCe hH hx hy hZ hee (le_max_right _ _) (le_max_right _ _)
  have hr := paid_profile_weight_mono p {(0,0)} S Cr H x y Z (-(1/20:ℝ)) e
    0 (max jm je) 0 (max km ke) hS0 hCr hH hx hy hZ (by linarith)
    (Nat.zero_le _) (Nat.zero_le _)
  simp only [pow_zero, mul_one] at hr
  calc
    budget ≤ Cr*H*(p.control {(0,0)})^2*Z^(-(1/20:ℝ)) +
        average*coefficient*main + average*error := by nlinarith only [hbudget]
    _ ≤ Cr*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e +
        Cm*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e +
        Ce*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e :=
      add_le_add (add_le_add hr (hmain.trans hm)) (herror.trans herr)
    _ = _ := by ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
