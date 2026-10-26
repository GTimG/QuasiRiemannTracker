/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.FirstNumeratorValuation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.HighLedgerGeometry

set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OAI.SevenEighths.Record12518109Natural.Valuation
noncomputable section
open scoped Classical BigOperators
open CenteredMomentActive
open Record12518109Natural.FirstNumeratorValuation

def rho (delta : ℝ) : ℝ := 1-10*delta/(3*(5-2*delta))
def commonGamma (delta : ℝ) : ℝ := delta-max (3/19) (4*rho delta-5/4)
def firstCommon (rho delta c d R E Lc R0 : ℝ) : ℝ :=
  (1-rho)*max (c-d) 0-delta*c-(1+rho)*R-E-
    max (3*c-5*d-R) 0/6+rho*Lc+R0

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
end OAI.SevenEighths.Record12518109Natural.Valuation
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.local_linear_nonnegative
