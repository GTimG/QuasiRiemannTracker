/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Monotonicity of our fixed finite return envelope. The general derivative
argument follows PR69 CountMonotonicity, with our own branch data and
checked upward admission windows. No analytic count theorem is assumed.
-/
import Candidate.SilPrior.FourthPower.ReturnFinite
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnMonotone
noncomputable section
open ReturnCertificate ReturnCountData ReturnFinite Filter
open scoped Topology

theorem C0_hasDerivAt (b : ImprovedBranch) (p : ℝ) :
    HasDerivAt (C0 b) (CPrime b) p := by
  have hp := hasDerivAt_id p
  by_cases hc : b.capped=true
  · convert (hasDerivAt_const p (1:ℝ)).sub ((hp.const_mul 2).mul_const (capWidth b)) using 1
    · funext z;simp [C0,Z,hc]
    · simp [CPrime,hc] <;> ring
  · convert (hasDerivAt_const p (1:ℝ)).sub
      (((hp.const_mul 2).mul_const b.face.intercept).div_const b.face.slope) using 1
    · funext z;simp [C0,Z,hc]
    · simp [CPrime,hc] <;> ring

theorem A_hasDerivAt (b : ImprovedBranch) (p : ℝ) :
    HasDerivAt (A b) (APrime b) p := by
  have hp := hasDerivAt_id p
  by_cases hc : b.capped=true
  · convert hasDerivAt_const p (2:ℝ) using 1
    · funext z;simp [A,hc]
    · simp [APrime,hc]
  · convert (hasDerivAt_const p (2:ℝ)).sub ((hp.const_mul 4).div_const b.face.slope) using 1
    · funext z;simp [A,hc]
    · simp [APrime,hc] <;> ring

theorem D_hasDerivAt (b : ImprovedBranch) (p : ℝ) :
    HasDerivAt (D b) (DPrime b) p := by
  have hp := hasDerivAt_id p
  by_cases hc : b.capped=true
  · convert (hasDerivAt_const p (3:ℝ)).sub hp using 1
    · funext z;simp [D,hc]
    · simp [DPrime,hc]
  · convert ((hasDerivAt_const p (3:ℝ)).sub hp).sub
      ((hp.const_mul 4).div_const b.face.slope) using 1
    · funext z;simp [D,hc]
    · simp [DPrime,hc] <;> ring

theorem U_hasDerivAt (b : ImprovedBranch) (p : ℝ) :
    HasDerivAt (U b) (UPrime b p) p := by
  convert ((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)).mul (C0_hasDerivAt b p) using 1
  · funext z;rfl
  · dsimp only [UPrime, Pi.sub_apply, id_eq];ring

theorem J_hasDerivAt (b : ImprovedBranch) (δ p : ℝ) :
    HasDerivAt (J b δ) (JPrime b δ p) p := by
  have hp := (hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)
  convert ((D_hasDerivAt b p).const_mul (V δ)).add
    ((hp.mul (A_hasDerivAt b p)).const_mul δ) using 1
  · funext z;dsimp only [J, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq];ring
  · dsimp only [JPrime, Pi.sub_apply, id_eq];ring

theorem count_ratio (b : ImprovedBranch) {δ p : ℝ} (hJ : J b δ p≠0) :
    count b δ p=1-δ+V δ*δ*(U b p/J b δ p) := by
  unfold count N
  field_simp [hJ] <;> ring

theorem count_hasDerivAt (b : ImprovedBranch) {δ p : ℝ} (hJ : J b δ p≠0) :
    HasDerivAt (count b δ)
      (V δ*δ*(-(U b p*JPrime b δ p-UPrime b p*J b δ p))/(J b δ p)^2) p := by
  have hq := (U_hasDerivAt b p).div (J_hasDerivAt b δ p) hJ
  have hn := (J_hasDerivAt b δ p).continuousAt.eventually_ne hJ
  have he : count b δ=ᶠ[nhds p](fun z=>1-δ+V δ*δ*(U b z/J b δ z)) :=
    hn.mono (fun z hz=>count_ratio b hz)
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (hasDerivAt_const p (1-δ)).add (hq.const_mul (V δ*δ)) using 1 <;>
    (try funext z) <;> ring

theorem admitted_count_antitone (b : ImprovedBranch) {δ lo : ℝ}
    (hδ : 0≤δ) (hδhi : δ≤3/4)
    (hg : ∀p∈Set.Icc lo (1/2),Admitted b δ p) :
    AntitoneOn (count b δ) (Set.Icc lo (1/2)) := by
  have hJ (p : ℝ) (hp : p∈Set.Icc lo (1/2)) : 0<J b δ p :=
    (admitted_witness_ranges b (hg p hp)).2.1
  have hguard (p : ℝ) (hp : p∈Set.Icc lo (1/2)) :
      0≤U b p*JPrime b δ p-UPrime b p*J b δ p := by
    have hh := hg p hp ⟨11,by decide⟩
    exact (show 0<U b p*JPrime b δ p-UPrime b p*J b δ p by
      simpa only [admissionGuard] using hh).le
  have hd (p : ℝ) (hp : p∈Set.Icc lo (1/2)) := count_hasDerivAt b (hJ p hp).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc lo (1/2))
  · intro p hp;exact (hd p hp).continuousAt.continuousWithinAt
  · intro p hp;exact (hd p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hd p (interior_subset hp)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by dsimp only [V];linarith) hδ)
        (neg_nonpos.mpr (hguard p (interior_subset hp)))
    · exact sq_nonneg _

def oldCPrime (k p : ℝ) : ℝ := -2*(1-p/(3*k))-2*(1-p)/(3*k)
def oldDPrime (k : ℝ) : ℝ := -1-2/(3*k)
def oldJPrime (k δ p : ℝ) : ℝ := V δ*oldDPrime k+δ*oldCPrime k p

theorem oldC_hasDerivAt (k p : ℝ) : HasDerivAt (oldC k) (oldCPrime k p) p := by
  have hp := hasDerivAt_id p
  convert (((hasDerivAt_const p (1:ℝ)).sub hp).mul
    ((hasDerivAt_const p (1:ℝ)).sub (hp.div_const (3*k)))).const_mul 2 using 1
  · funext z;dsimp only [oldC, Pi.mul_apply, Pi.sub_apply, id_eq];ring
  · dsimp only [oldCPrime, Pi.sub_apply, id_eq];ring

theorem oldD_hasDerivAt (k p : ℝ) : HasDerivAt (oldD k) (oldDPrime k) p := by
  have hp := hasDerivAt_id p
  convert ((hasDerivAt_const p (3:ℝ)).sub hp).sub ((hp.const_mul 2).div_const (3*k)) using 1
  · funext z;rfl
  · dsimp only [oldDPrime];ring

theorem oldJ_hasDerivAt (k δ p : ℝ) : HasDerivAt (oldJ k δ) (oldJPrime k δ p) p := by
  convert ((oldD_hasDerivAt k p).const_mul (V δ)).add
    ((oldC_hasDerivAt k p).const_mul δ) using 1
  · funext z;dsimp only [oldJ, Pi.add_apply]
  · rfl

/-- A direct polynomial sign certificate for the old branch. -/
theorem old_determinant_nonpos {k p : ℝ} (hk : 7/10≤k) (hp : p≤1/2) :
    oldCPrime k p*oldD k p-oldC k p*oldDPrime k≤0 := by
  have hk0 : 0<k := by linarith
  have he : (oldCPrime k p*oldD k p-oldC k p*oldDPrime k)*(3*k)^2=
      -36*k^2-6*k+36*k*p-2*(3*k+2)*p^2 := by
    unfold oldCPrime oldDPrime oldC oldD
    field_simp [hk0.ne'] <;> ring
  have hr : -36*k^2-6*k+36*k*p-2*(3*k+2)*p^2≤0 := by
    have h₁ := mul_nonneg hk0.le (show 0≤1/2-p by linarith)
    have h₂ := mul_nonneg (show 0≤3*k+2 by linarith) (sq_nonneg p)
    have h₃ := mul_nonneg hk0.le (show 0≤3*k-1 by linarith)
    nlinarith
  by_contra hn
  have hm := mul_pos (lt_of_not_ge hn) (sq_pos_of_pos (show 0<3*k by positivity))
  nlinarith

theorem old_count_hasDerivAt {k δ p : ℝ} (hJ : oldJ k δ p≠0) :
    HasDerivAt (fun z=>oldN k δ z/oldJ k δ z)
      ((δ*V δ/2)*(oldCPrime k p*oldJ k δ p-oldC k p*oldJPrime k δ p)/(oldJ k δ p)^2) p := by
  have hq := (oldC_hasDerivAt k p).div (oldJ_hasDerivAt k δ p) hJ
  have hn := (oldJ_hasDerivAt k δ p).continuousAt.eventually_ne hJ
  have he : (fun z=>oldN k δ z/oldJ k δ z)=ᶠ[nhds p]
      (fun z=>1-δ+(δ*V δ/2)*(oldC k z/oldJ k δ z)) := by
    apply hn.mono
    intro z hz
    unfold oldN
    field_simp [hz] <;> ring
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (hasDerivAt_const p (1-δ)).add (hq.const_mul (δ*V δ/2)) using 1 <;>
    (try funext z) <;> ring

theorem old_count_antitone {k δ : ℝ} (hk : 7/10≤k) (hδ : δ∈Set.Icc 0 (3/4)) :
    AntitoneOn (fun p=>oldN k δ p/oldJ k δ p) (Set.Icc 0 (1/2)) := by
  have hd (p : ℝ) (hp : p∈Set.Icc 0 (1/2)) := old_count_hasDerivAt
    (old_denominator_positive hk hδ.1 hδ.2 hp.1 hp.2).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1/2))
  · intro p hp;exact (hd p hp).continuousAt.continuousWithinAt
  · intro p hp;exact (hd p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    have hp' := interior_subset hp
    rw [(hd p hp').deriv]
    have hV : 0≤V δ := by dsimp only [V];linarith [hδ.2]
    have hdet : oldCPrime k p*oldJ k δ p-oldC k p*oldJPrime k δ p≤0 := by
      have he : oldCPrime k p*oldJ k δ p-oldC k p*oldJPrime k δ p=
          V δ*(oldCPrime k p*oldD k p-oldC k p*oldDPrime k) := by
        dsimp only [oldJ,oldJPrime];ring
      rw [he]
      exact mul_nonpos_of_nonneg_of_nonpos hV (old_determinant_nonpos hk hp'.2)
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (mul_nonneg hδ.1 hV) (by norm_num)) hdet)
      (sq_nonneg _)

/-- An available improved branch remains admitted over the whole
interval to the right, so its determinant guard controls that interval. -/
theorem available_count_antitone {b : Branch} {δ p p' : ℝ}
    (ha : Available b δ p) (hδ : δ∈Set.Icc 0 (3/4))
    (hp : p∈Set.Icc 0 (1/2)) (hp' : p'∈Set.Icc 0 (1/2)) (hpp : p≤p') :
    countN b kappa δ p'/countJ b kappa δ p'≤countN b kappa δ p/countJ b kappa δ p := by
  rcases ha with rfl | ⟨i,rfl,hi⟩
  · exact old_count_antitone (by norm_num [kappa,theta]) hδ hp hp' hpp
  · have hg : ∀q∈Set.Icc (window i).pLo (1/2),Admitted (window i).branch δ q :=
      fun q hq=>window_admitted i ⟨hi.1,hq⟩
    exact admitted_count_antitone (window i).branch hδ.1 hδ.2 hg hi.2
      ⟨hi.2.1.trans hpp,hp'.2⟩ hpp

/-- The very same finite envelope used by the edge certificate is
antitone. New windows can only add candidates; old available candidates
remain admissible and decrease. -/
theorem envelope_antitone {δ : ℝ} (hδ : δ∈Set.Icc 0 (3/4)) :
    AntitoneOn (envelope δ) (Set.Icc 0 (1/2)) := by
  intro p hp p' hp' hpp
  change envelope δ p'≤Finset.univ.inf' Finset.univ_nonempty (windowValue δ p)
  apply Finset.le_inf'
  intro i hi
  cases i with
  | none =>
    change envelope δ p'≤countN .old kappa δ p/countJ .old kappa δ p
    exact (envelope_le_available (Or.inl rfl : Available .old δ p')).trans
      (available_count_antitone (Or.inl rfl : Available .old δ p) hδ hp hp' hpp)
  | some i =>
    by_cases hw : (window i).Contains δ p
    · simp only [windowValue,if_pos hw]
      have ha : Available (.improved (window i).branch) δ p := Or.inr ⟨i,rfl,hw⟩
      exact (envelope_le_available (available_upward ha hpp hp'.2)).trans
        (available_count_antitone ha hδ hp hp' hpp)
    · simp only [windowValue,if_neg hw]
      exact (envelope_le_available (Or.inl rfl : Available .old δ p')).trans
        (available_count_antitone (Or.inl rfl : Available .old δ p) hδ hp hp' hpp)

end
end Candidate.SilPrior.FourthPower.ReturnMonotone
