import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineAssembly
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped BigOperators
open QuadraticInitialBound CenteredMomentFiniteProfileExceptional Cycle63Physical

/-- Collect a finite family of profile controls and three independent height
degrees before the profile and heights move. The index can include the slot
subset and the analytic branch. -/
theorem geometry_uniform_profile_controls {ι : Type*} [Fintype ι]
    (C : ι→ℝ) (S : ι→Finset (ℕ×ℕ)) (j k l : ι→ℕ)
    (hC : ∀i,0≤C i) :
    ∃C₀ : ℝ,0<C₀ ∧ ∃S₀ : Finset (ℕ×ℕ),∃j₀ k₀ l₀ : ℕ,
      ∀i (p : Profiles (1/4) (9/4)) (x y z : ℝ),
        1≤x → 1≤y → 1≤z →
        C i*(p.control (S i))^2*x^(j i)*y^(k i)*z^(2*l i)≤
          C₀*(p.control S₀)^2*x^j₀*y^k₀*z^(2*l₀) := by
  classical
  let C₀:=1+∑i,C i
  let S₀:=Finset.univ.biUnion S
  let j₀:=Finset.univ.sup j
  let k₀:=Finset.univ.sup k
  let l₀:=Finset.univ.sup l
  have hC₀ : 0<C₀ := by
    have hs:=Finset.sum_nonneg (fun i (_ : i∈(Finset.univ:Finset ι))=>hC i)
    dsimp [C₀];linarith
  refine ⟨C₀,hC₀,S₀,j₀,k₀,l₀,?_⟩
  intro i p x y z hx hy hz
  have hCi : C i≤C₀ := by
    have hh:=Finset.single_le_sum (fun i (_ : i∈(Finset.univ:Finset ι))=>hC i)
      (Finset.mem_univ i)
    dsimp [C₀];linarith
  have hSi : S i⊆S₀ := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,ha⟩
  have hp:=profile_control_mono p hSi
  have hp0:=p.control_nonneg (S i)
  have hj : j i≤j₀:=Finset.le_sup (f:=j) (Finset.mem_univ i)
  have hk : k i≤k₀:=Finset.le_sup (f:=k) (Finset.mem_univ i)
  have hl : 2*l i≤2*l₀:=Nat.mul_le_mul_left 2
    (Finset.le_sup (f:=l) (Finset.mem_univ i))
  have hxp:=pow_le_pow_right₀ hx hj
  have hyp:=pow_le_pow_right₀ hy hk
  have hzp:=pow_le_pow_right₀ hz hl
  have hx0 : 0≤x:=zero_le_one.trans hx
  have hy0 : 0≤y:=zero_le_one.trans hy
  have hz0 : 0≤z:=zero_le_one.trans hz
  have hsquare : (p.control (S i))^2≤(p.control S₀)^2:=pow_le_pow_left₀ hp0 hp 2
  exact mul_le_mul
    (mul_le_mul (mul_le_mul (mul_le_mul hCi hsquare (sq_nonneg _) hC₀.le)
      hxp (pow_nonneg hx0 _) (mul_nonneg hC₀.le (sq_nonneg _)))
      hyp (pow_nonneg hy0 _) (by positivity))
    hzp (pow_nonneg hz0 _) (by positivity)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
