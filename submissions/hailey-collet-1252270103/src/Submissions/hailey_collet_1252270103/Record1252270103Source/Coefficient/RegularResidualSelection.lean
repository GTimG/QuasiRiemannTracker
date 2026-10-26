/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Selection from the full residual ideal pool keeps its inverse-norm weight.
No residual ideal is asserted to divide an encoded physical row. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.JointForcedFamily
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.Divisor

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularResidualSelection
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open Record1252270103Source Record1252270103Second
open QRH.Record1252270103Source.Admission.JointForced
local notation "O"=>ActualEisensteinCubic.O
universe u

theorem full_squarefree_seed_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃H : ℝ,0<H ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀ε : ℝ,0≤ε→∀Ls : Finset (Ideal O),
      (∀L∈Ls,Squarefree L)→(∀L∈Ls,(L.absNorm:ℝ)≤Z^B)→
      (∑L∈Ls,(L.absNorm:ℝ)^ε/(L.absNorm:ℝ))≤H*Z^(δ+B*ε) := by
  obtain ⟨H,hH,h⟩:=ExceptionalWindow.full_seed_mass_subpower B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε hε Ls hsf hnorm
  have he : (∑L∈Ls,(L.absNorm:ℝ)^ε/(L.absNorm:ℝ))=
      ∑L∈Ls,‖(moebius L:ℂ)‖*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ)) := by
    apply Finset.sum_congr rfl
    intro L hL
    rw [(hsf L hL).moebius_eq]
    simp
  rw [he]
  exact hZ.2 ε hε Ls hnorm

/-- One actual residual ideal and actual complete forced child dominate the
entire finite residual sum. The harmonic constant and threshold precede
every moving source, character, pool and row. -/
theorem uniform_selected_residual (N : ℕ) (ε δ B : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hB : 0≤B) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type u}[Fintype ι],Fintype.card ι≤N→
      ∀(s : Input ι)(A₁ A₂ D K R : Ideal O)(F : Ideal O→ℂ)
        (Ls : Finset (Ideal O)),
      (∀L∈Ls,Squarefree L)→(∀L∈Ls,(L.absNorm:ℝ)≤Z^B)→
      ∀(τ : Character)(t : ℝ)(z : O),
      let modifier:=Collision.markedSourceModifier (ι:=ι) A₁ A₂ D K F
      (∑L∈Ls,‖normalizedRow s modifier R L τ t z‖^2)≠0→
      ∃L : Ideal O,L∈Ls ∧
        ∃p : ChildIndex s modifier R L,
          normalizedRow s modifier R L τ t z≠0 ∧
          frozenCoefficient p.2 p.1 R s.ν s.W s.P≠0 ∧
          0<childValue s modifier R L τ t z p ∧
          L∣(p.1:Ideal O) ∧ (p.1:Ideal O)∣L^2 ∧
          (∑L'∈Ls,‖normalizedRow s modifier R L' τ t z‖^2)≤
            K₀*Z^(δ+B*ε)*forcedProfileCost s*childValue s modifier R L τ t z p := by
  classical
  obtain ⟨Kf,hKf,hselect⟩:=uniform_selected_child.{u} N ε hε
  obtain ⟨H,hH,hmass⟩:=full_squarefree_seed_mass B δ hB hδ
  refine ⟨Kf*H,mul_pos hKf hH,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst hcard s A₁ A₂ D K R F Ls hsf hnorm τ t z modifier hsum
  let live:=Ls.filter (fun L=>normalizedRow s modifier R L τ t z≠0)
  have hlive : live.Nonempty := by
    obtain ⟨L,hL,hv⟩:=Finset.exists_ne_zero_of_sum_ne_zero hsum
    refine ⟨L,Finset.mem_filter.mpr ⟨hL,?_⟩⟩
    intro hn
    exact hv (by simp [hn])
  have hex (L : live):=hselect hcard s A₁ A₂ D K R L F
    (hsf L (Finset.mem_filter.mp L.property).1) τ t z (Finset.mem_filter.mp L.property).2
  choose pick hp using hex
  let value:=fun L:live=>childValue s modifier R L τ t z (pick L)
  obtain ⟨L₀,hL₀⟩:=hlive
  obtain ⟨Lstar,_,hmax⟩:=Finset.exists_max_image (Finset.univ:Finset live) value
    ⟨⟨L₀,hL₀⟩,Finset.mem_univ _⟩
  have hvpos : 0<value Lstar:=(hp Lstar).2.1
  refine ⟨Lstar,(Finset.mem_filter.mp Lstar.property).1,pick Lstar,
    (Finset.mem_filter.mp Lstar.property).2,(hp Lstar).1,hvpos,
    (hp Lstar).2.2.1,(hp Lstar).2.2.2.1,?_⟩
  have hterm (L : Ideal O)(hL : L∈Ls) :
      ‖normalizedRow s modifier R L τ t z‖^2≤
        (Kf*forcedProfileCost s*value Lstar)*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ)) := by
    by_cases hn : normalizedRow s modifier R L τ t z=0
    · simp only [hn,norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (mul_nonneg (mul_nonneg hKf.le (forcedProfileCost_nonneg s)) hvpos.le)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
    let l:live:=⟨L,Finset.mem_filter.mpr ⟨hL,hn⟩⟩
    have hm:=hmax l (Finset.mem_univ l)
    have hc : 0≤Kf*(L.absNorm:ℝ)^ε*forcedProfileCost s/(L.absNorm:ℝ):=
      div_nonneg (mul_nonneg (mul_nonneg hKf.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (forcedProfileCost_nonneg s)) (Nat.cast_nonneg _)
    have hh:=(hp l).2.2.2.2
    apply hh.trans
    convert mul_le_mul_of_nonneg_left hm hc using 1 <;> dsimp only [value,l] <;> ring
  calc
    _≤∑L∈Ls,(Kf*forcedProfileCost s*value Lstar)*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ)) :=
      Finset.sum_le_sum hterm
    _=(Kf*forcedProfileCost s*value Lstar)*(∑L∈Ls,(L.absNorm:ℝ)^ε/(L.absNorm:ℝ)) :=
      (Finset.mul_sum ..).symm
    _≤(Kf*forcedProfileCost s*value Lstar)*(H*Z^(δ+B*ε)) :=
      mul_le_mul_of_nonneg_left (hZ.2 ε hε.le Ls hsf hnorm)
        (mul_nonneg (mul_nonneg hKf.le (forcedProfileCost_nonneg s)) hvpos.le)
    _=_ := by dsimp only [value];ring

end
end QRH.Record1252270103Source.RegularResidualSelection
#print axioms QRH.Record1252270103Source.RegularResidualSelection.full_squarefree_seed_mass
#print axioms QRH.Record1252270103Source.RegularResidualSelection.uniform_selected_residual
