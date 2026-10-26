import Candidate.Target830.Parameters
import Candidate.Target836.SourceProvider.HighPayment

/- Original module: Candidate.Target830.Source.ConeCore. -/
section

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Target830.Source.Valuation
noncomputable section
open scoped Classical BigOperators
open CenteredMomentActive
open Cycle63Moment.FirstNumeratorValuation

def linear (a x : Fin 6 → ℝ) : ℝ :=
  a 0*x 0+a 1*x 1+a 2*x 2+a 3*x 3+a 4*x 4+a 5*x 5

/-- The physically left-oriented local numerator; the reflected side swaps
the two valuations as well as the signed source orientation. -/
def point (i j : ℕ) : Fin 6 → ℝ :=
  ![(i:ℝ),(j:ℝ),1,if netExponent i j=0 then 0 else 1,
    (sourceExponent true i j:ℝ),if netExponent i j=5 then 1 else 0]

def weighted {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ) : Fin 6 → ℝ :=
  fun k => ∑ t∈s,w t*point (i t) (j t) k

theorem point_nonnegative (i j : ℕ) (k : Fin 6) : 0 ≤ point i j k := by
  fin_cases k <;> simp [point] <;> positivity

theorem weighted_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t) (k : Fin 6) :
    0 ≤ weighted s i j w k := by
  exact Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht) (point_nonnegative _ _ _))

/-- The two independent sixth-power rays reduce every positive valuation to
the 36 actual residue representatives. -/
theorem local_linear_nonnegative (a : Fin 6 → ℝ) (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hbase : ∀ i j : ℕ,1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → 0 ≤ linear a (point i j))
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : 0 ≤ linear a (point i j) := by
  let i0 := (i-1)%6+1
  let j0 := (j-1)%6+1
  have hi01 : 1 ≤ i0 := by dsimp [i0];omega
  have hi06 : i0 ≤ 6 := by dsimp [i0];omega
  have hj01 : 1 ≤ j0 := by dsimp [j0];omega
  have hj06 : j0 ≤ 6 := by dsimp [j0];omega
  have hi0i : i0 ≤ i := by dsimp [i0];omega
  have hj0j : j0 ≤ j := by dsimp [j0];omega
  have hn : netExponent i j=netExponent i0 j0 := by
    dsimp [netExponent,i0,j0]
    omega
  have he : sourceExponent true i j=sourceExponent true i0 j0 := by
    simp only [sourceExponent,hn]
  have hid : linear a (point i j)=linear a (point i0 j0)+
      a 0*((i:ℝ)-(i0:ℝ))+a 1*((j:ℝ)-(j0:ℝ)) := by
    simp [linear,point,hn,he]
    ring
  have hx : 0 ≤ (i:ℝ)-(i0:ℝ) := sub_nonneg.mpr (by exact_mod_cast hi0i)
  have hy : 0 ≤ (j:ℝ)-(j0:ℝ) := sub_nonneg.mpr (by exact_mod_cast hj0j)
  rw [hid]
  exact add_nonneg (add_nonneg (hbase i0 j0 hi01 hi06 hj01 hj06)
    (mul_nonneg ha0 hx)) (mul_nonneg ha1 hy)

theorem linear_weighted {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (a : Fin 6 → ℝ) :
    linear a (weighted s i j w)=∑ t∈s,w t*linear a (point (i t) (j t)) := by
  simp [linear,weighted,Finset.mul_sum,mul_add,Finset.sum_add_distrib,
    mul_assoc,mul_left_comm]

theorem weighted_linear_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (a : Fin 6 → ℝ) (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hbase : ∀ i j : ℕ,1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → 0 ≤ linear a (point i j)) :
    0 ≤ linear a (weighted s i j w) := by
  rw [linear_weighted]
  exact Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht)
    (local_linear_nonnegative a ha0 ha1 hbase (i t) (j t) (hi t ht) (hj t ht)))

def surplus (c d p R : ℝ) : ℝ :=
  (c+d-R-2*p-max (3*c-5*d-R) 0/6-max (3*d-5*c-R) 0/6)/2

def commonValue (rho : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  (1-rho)*max (x 0-x 1) 0-(1+rho)*x 3-max (3*x 0-5*x 1-x 3) 0/6+
    rho*x 4+x 5-surplus (x 0) (x 1) (x 2) (x 3)

theorem commonValue_affine (rho : ℝ) (x : Fin 6 → ℝ) :
    commonValue rho x=commonValue 0 x+
      rho*(-max (x 0-x 1) 0-x 3+x 4) := by
  unfold commonValue
  ring

end
end OAI.SevenEighths.Target830.Source.Valuation
#print axioms OAI.SevenEighths.Target830.Source.Valuation.local_linear_nonnegative
end

/- Original module: Candidate.Target830.Source.ConeCertificates. -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Source.Valuation
noncomputable section
open scoped Classical BigOperators
open CenteredMomentActive Cycle63Moment.FirstNumeratorValuation

def cone0_0_0 : Fin 6 → ℝ := ![25/38,1/2,-1,3/4,-1/4,-1]
theorem cone0_0_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_0_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_0_0,point,sourceExponent,netExponent]
theorem cone0_0_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_0_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_0_0
    (by norm_num [cone0_0_0]) (by norm_num [cone0_0_0]) cone0_0_0_residues

def cone0_0_1 : Fin 6 → ℝ := ![22/19,1/5,-1,17/20,-1/4,-1]
theorem cone0_0_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_0_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_0_1,point,sourceExponent,netExponent]
theorem cone0_0_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_0_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_0_1
    (by norm_num [cone0_0_1]) (by norm_num [cone0_0_1]) cone0_0_1_residues

def cone0_1_0 : Fin 6 → ℝ := ![11/76,65/76,-1,51/76,-1/4,-1]
theorem cone0_1_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_1_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_1_0,point,sourceExponent,netExponent]
theorem cone0_1_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_1_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_1_0
    (by norm_num [cone0_1_0]) (by norm_num [cone0_1_0]) cone0_1_0_residues

def cone0_1_1 : Fin 6 → ℝ := ![11/76,65/76,-1,51/76,-1/4,-1]
theorem cone0_1_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_1_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_1_1,point,sourceExponent,netExponent]
theorem cone0_1_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_1_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_1_1
    (by norm_num [cone0_1_1]) (by norm_num [cone0_1_1]) cone0_1_1_residues

theorem common_endpoint0 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (1/4) (weighted s i j w) ≤ (3/19)*weighted s i j w 0 := by
  let x := weighted s i j w
  change commonValue (1/4) x ≤ (3/19)*x 0
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  by_cases hc : x 1 ≤ x 0
  · have hm : 0 ≤ x 0-x 1 := by linarith
    have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · have hr := cone0_1_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_1_1 x at hr
      simp only [commonValue,surplus,max_eq_left hm,max_eq_left hb,max_eq_right hn]
      norm_num [linear,cone0_1_1] at hr
      linarith
    · have hr := cone0_1_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_1_0 x at hr
      have hb0 : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_left hm,max_eq_right hb0,max_eq_right hn]
      norm_num [linear,cone0_1_0] at hr
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cone0_0_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_0_1 x at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      norm_num [linear,cone0_0_1] at hr
      linarith
    · have hr := cone0_0_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_0_0 x at hr
      have hb0 : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_right hb0]
      norm_num [linear,cone0_0_0] at hr
      linarith

def cone1_0_0 : Fin 6 → ℝ := ![25/38,1/2,-1,259/304,-107/304,-1]
theorem cone1_0_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_0_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_0_0,point,sourceExponent,netExponent]
theorem cone1_0_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_0_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_0_0
    (by norm_num [cone1_0_0]) (by norm_num [cone1_0_0]) cone1_0_0_residues

def cone1_0_1 : Fin 6 → ℝ := ![245/228,1/4,-1,853/912,-107/304,-1]
theorem cone1_0_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_0_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_0_1,point,sourceExponent,netExponent]
theorem cone1_0_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_0_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_0_1
    (by norm_num [cone1_0_1]) (by norm_num [cone1_0_1]) cone1_0_1_residues

def cone1_1_0 : Fin 6 → ℝ := ![75/304,229/304,-1,235/304,-107/304,-1]
theorem cone1_1_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_1_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_1_0,point,sourceExponent,netExponent]
theorem cone1_1_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_1_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_1_0
    (by norm_num [cone1_1_0]) (by norm_num [cone1_1_0]) cone1_1_0_residues

def cone1_1_1 : Fin 6 → ℝ := ![75/304,229/304,-1,235/304,-107/304,-1]
theorem cone1_1_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_1_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_1_1,point,sourceExponent,netExponent]
theorem cone1_1_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_1_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_1_1
    (by norm_num [cone1_1_1]) (by norm_num [cone1_1_1]) cone1_1_1_residues

theorem common_endpoint1 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (107/304) (weighted s i j w) ≤ (3/19)*weighted s i j w 0 := by
  let x := weighted s i j w
  change commonValue (107/304) x ≤ (3/19)*x 0
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  by_cases hc : x 1 ≤ x 0
  · have hm : 0 ≤ x 0-x 1 := by linarith
    have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · have hr := cone1_1_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_1_1 x at hr
      simp only [commonValue,surplus,max_eq_left hm,max_eq_left hb,max_eq_right hn]
      norm_num [linear,cone1_1_1] at hr
      linarith
    · have hr := cone1_1_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_1_0 x at hr
      have hb0 : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_left hm,max_eq_right hb0,max_eq_right hn]
      norm_num [linear,cone1_1_0] at hr
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cone1_0_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_0_1 x at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      norm_num [linear,cone1_0_1] at hr
      linarith
    · have hr := cone1_0_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_0_0 x at hr
      have hb0 : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_right hb0]
      norm_num [linear,cone1_0_0] at hr
      linarith

def cone2_0_0 : Fin 6 → ℝ := ![1481/1900,326/475,-1,853/950,-23/50,-1]
theorem cone2_0_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_0_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_0_0,point,sourceExponent,netExponent]
theorem cone2_0_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_0_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_0_0
    (by norm_num [cone2_0_0]) (by norm_num [cone2_0_0]) cone2_0_0_residues

def cone2_0_1 : Fin 6 → ℝ := ![113/75,1/4,-1,313/300,-23/50,-1]
theorem cone2_0_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_0_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_0_1,point,sourceExponent,netExponent]
theorem cone2_0_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_0_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_0_1
    (by norm_num [cone2_0_1]) (by norm_num [cone2_0_1]) cone2_0_1_residues

def cone2_1_0 : Fin 6 → ℝ := ![563/740,637/925,-1,823/925,-23/50,-1]
theorem cone2_1_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_1_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_1_0,point,sourceExponent,netExponent]
theorem cone2_1_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_1_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_1_0
    (by norm_num [cone2_1_0]) (by norm_num [cone2_1_0]) cone2_1_0_residues

def cone2_1_1 : Fin 6 → ℝ := ![563/740,637/925,-1,823/925,-23/50,-1]
theorem cone2_1_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_1_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_1_1,point,sourceExponent,netExponent]
theorem cone2_1_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_1_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_1_1
    (by norm_num [cone2_1_1]) (by norm_num [cone2_1_1]) cone2_1_1_residues

theorem common_endpoint2 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (23/50) (weighted s i j w) ≤ (59/100)*weighted s i j w 0 := by
  let x := weighted s i j w
  change commonValue (23/50) x ≤ (59/100)*x 0
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  by_cases hc : x 1 ≤ x 0
  · have hm : 0 ≤ x 0-x 1 := by linarith
    have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · have hr := cone2_1_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_1_1 x at hr
      simp only [commonValue,surplus,max_eq_left hm,max_eq_left hb,max_eq_right hn]
      norm_num [linear,cone2_1_1] at hr
      linarith
    · have hr := cone2_1_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_1_0 x at hr
      have hb0 : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_left hm,max_eq_right hb0,max_eq_right hn]
      norm_num [linear,cone2_1_0] at hr
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cone2_0_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_0_1 x at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      norm_num [linear,cone2_0_1] at hr
      linarith
    · have hr := cone2_0_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_0_0 x at hr
      have hb0 : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_right hb0]
      norm_num [linear,cone2_0_0] at hr
      linarith

end
end OAI.SevenEighths.Target830.Source.Valuation
#print axioms OAI.SevenEighths.Target830.Source.Valuation.common_endpoint0
#print axioms OAI.SevenEighths.Target830.Source.Valuation.common_endpoint1
#print axioms OAI.SevenEighths.Target830.Source.Valuation.common_endpoint2
end

/- Original module: Candidate.Target830.Source.Cone. -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Target830.Source.Valuation
noncomputable section
open scoped Classical BigOperators

theorem affine_interval_bound {f : ℝ → ℝ} {a b A S M r : ℝ}
    (hf : ∀ z,f z=A+z*S) (hr : r ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f r ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with h | h
  · have := mul_le_mul_of_nonneg_right hr.2 h
    linarith
  · have := mul_le_mul_of_nonpos_right hr.1 h
    linarith

theorem common_weighted_bound {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t)
    (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (rho : ℝ) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50) :
    commonValue rho (weighted s i j w) ≤
      max (3/19) (4*rho-5/4)*weighted s i j w 0 := by
  let x := weighted s i j w
  have h0 := common_endpoint0 s i j w hw hi hj
  have h1 := common_endpoint1 s i j w hw hi hj
  have h2 := common_endpoint2 s i j w hw hi hj
  change commonValue (1/4) x ≤ (3/19)*x 0 at h0
  change commonValue (107/304) x ≤ (3/19)*x 0 at h1
  change commonValue (23/50) x ≤ (59/100)*x 0 at h2
  change commonValue rho x ≤ max (3/19) (4*rho-5/4)*x 0
  by_cases hs : rho ≤ 107/304
  · rw [max_eq_left (by linarith : 4*rho-5/4 ≤ (3/19:ℝ))]
    exact affine_interval_bound (f:=fun z => commonValue z x)
      (a:=1/4) (b:=107/304) (r:=rho) (M:=(3/19)*x 0)
      (fun z => commonValue_affine z x) ⟨hr,hs⟩ h0 h1
  · have hs' : (107/304:ℝ) ≤ rho := (lt_of_not_ge hs).le
    rw [max_eq_right (by linarith : (3/19:ℝ) ≤ 4*rho-5/4)]
    have hf : ∀ z,commonValue z x-(4*z-5/4)*x 0=
        commonValue 0 x+(5/4)*x 0+
          z*(-max (x 0-x 1) 0-x 3+x 4-4*x 0) := by
      intro z
      rw [commonValue_affine]
      ring
    have hh := affine_interval_bound (f:=fun z => commonValue z x-(4*z-5/4)*x 0)
      (a:=107/304) (b:=23/50) (r:=rho) (M:=0) hf ⟨hs',hrhi⟩
      (by norm_num;linarith [h1]) (by norm_num;linarith [h2])
    linarith

theorem common_weighted_saving {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t)
    (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (rho delta E : ℝ) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50) :
    let x := weighted s i j w
    ValuationGain.firstCommon rho delta (x 0) (x 1) (x 3) E (x 4) (x 5)-
      surplus (x 0) (x 1) (x 2) (x 3) ≤
      -(delta-max (3/19) (4*rho-5/4))*x 0-E := by
  have hh := common_weighted_bound s i j w hw hi hj rho hr hrhi
  dsimp only
  unfold commonValue ValuationGain.firstCommon at *
  nlinarith

theorem rho_eq_local (delta : ℝ) : rho delta=LocalMoment.unmarkedDensity delta := rfl

theorem rho_extended_range {delta : ℝ} (hd : 405/662 ≤ delta) (hdhi : delta ≤ 3/4) :
    1/4 ≤ rho delta ∧ rho delta ≤ 23/50 := by
  have hden : 0 < 3*(5-2*delta) := by linarith
  have hlo : 10*delta/(3*(5-2*delta)) ≤ 3/4 := by
    rw [div_le_iff₀ hden]
    linarith
  have hhi : 27/50 ≤ 10*delta/(3*(5-2*delta)) := by
    rw [le_div_iff₀ hden]
    linarith
  unfold rho
  constructor <;> linarith

end
end OAI.SevenEighths.Target830.Source.Valuation
#print axioms OAI.SevenEighths.Target830.Source.Valuation.common_weighted_saving
end
