import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.FirstNumeratorValuation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.UnmarkedDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The valuation cone of a first-source label with the balanced surplus. From tracker PR #63 (Zhongpai
Gao, `gao-balanced-marked-20261017`, `Target830/Source/{ConeCore,ConeCertificates,Cone}.lean`),
Apache-2.0. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.ValuationCone
noncomputable section
open scoped BigOperators
open CenteredMomentActive Cycle63Moment.FirstNumeratorValuation

/-! A common prime of the two conductor ideals of a first-source label, with valuations `i` in the first
ideal and `j` in the second, contributes per unit of its base-`Z` logarithmic norm the point
`(i, j, 1, [active], e, [cancelled])` to the six logarithms of the label: the norms of the two ideals,
of their common radical, of the active conductor, of the numerator (source exponent `e`) and of the
cancelled radical. The label's vector is the weighted sum of these points over its common primes. A
linear form with nonnegative coefficients of `i` and `j` that is nonnegative at the 36 residues of
`(i, j)` modulo 6 is therefore nonnegative at every label.

With the surplus `Σ` of the balanced source energy, the common part of the HIGH exponent is at most
`max (3/19) (4ρ - 5/4)` times the first ideal's logarithm for every density `ρ ∈ [1/4, 23/50]`; it is
affine in `ρ`, so the three densities `1/4`, `107/304` (where the two rates meet) and `23/50` suffice,
each by a linear form for every sign pattern of the maxima. -/

/-- The linear form with coefficients `a` at the six logarithms `x`. -/
def linear (a x : Fin 6 → ℝ) : ℝ :=
  a 0*x 0+a 1*x 1+a 2*x 2+a 3*x 3+a 4*x 4+a 5*x 5

/-- The six logarithms per unit norm of a common prime with valuations `i` and `j`, in the left
orientation. -/
def point (i j : ℕ) : Fin 6 → ℝ :=
  ![(i:ℝ),(j:ℝ),1,if netExponent i j=0 then 0 else 1,
    (sourceExponent true i j:ℝ),if netExponent i j=5 then 1 else 0]

/-- The six logarithms of a label whose common primes `t ∈ s` have valuations `i t`, `j t` and
logarithmic norms `w t`. -/
def weighted {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ) : Fin 6 → ℝ :=
  fun k => ∑ t∈s,w t*point (i t) (j t) k

theorem point_nonnegative (i j : ℕ) (k : Fin 6) : 0 ≤ point i j k := by
  fin_cases k <;> simp [point] <;> positivity

theorem weighted_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t) (k : Fin 6) :
    0 ≤ weighted s i j w k :=
  Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht) (point_nonnegative _ _ _))

/-- The sixth powers in the two ideals reduce every positive valuation to its residue in `1..6`. -/
theorem local_linear_nonnegative (a : Fin 6 → ℝ) (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hbase : ∀ i j : ℕ,1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → 0 ≤ linear a (point i j))
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : 0 ≤ linear a (point i j) := by
  let i0 := (i-1)%6+1
  let j0 := (j-1)%6+1
  have hi01 : 1 ≤ i0 := by dsimp [i0]; omega
  have hi06 : i0 ≤ 6 := by dsimp [i0]; omega
  have hj01 : 1 ≤ j0 := by dsimp [j0]; omega
  have hj06 : j0 ≤ 6 := by dsimp [j0]; omega
  have hi0i : i0 ≤ i := by dsimp [i0]; omega
  have hj0j : j0 ≤ j := by dsimp [j0]; omega
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
  simp [linear,weighted,Finset.mul_sum,mul_add,Finset.sum_add_distrib,mul_left_comm]

theorem weighted_linear_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (a : Fin 6 → ℝ) (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1)
    (hbase : ∀ i j : ℕ,1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → 0 ≤ linear a (point i j)) :
    0 ≤ linear a (weighted s i j w) := by
  rw [linear_weighted]
  exact Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht)
    (local_linear_nonnegative a ha0 ha1 hbase (i t) (j t) (hi t ht) (hj t ht)))

/-- The surplus of the balanced source energy for the logarithms `c`, `d` of the two ideals, `p` of
their common radical and `R` of the active conductor. -/
def surplus (c d p R : ℝ) : ℝ :=
  (c+d-R-2*p-max (3*c-5*d-R) 0/6-max (3*d-5*c-R) 0/6)/2

/-- The common part of the HIGH exponent at density `ρ`, less the surplus, at the six logarithms. -/
def commonValue (ρ : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  (1-ρ)*max (x 0-x 1) 0-(1+ρ)*x 3-max (3*x 0-5*x 1-x 3) 0/6+
    ρ*x 4+x 5-surplus (x 0) (x 1) (x 2) (x 3)

theorem commonValue_affine (ρ : ℝ) (x : Fin 6 → ℝ) :
    commonValue ρ x=commonValue 0 x+ρ*(-max (x 0-x 1) 0-x 3+x 4) := by
  unfold commonValue
  ring

/-! Linear-programming certificates, one per density endpoint and sign pattern of the maxima: at
density `1/4` and `107/304` the bound is `3/19` times the first logarithm, at `23/50` it is `59/100`. In
each pattern the bound follows from the form's nonnegativity by `linarith`. -/

def cone0a : Fin 6 → ℝ := ![25/38,1/2,-1,3/4,-1/4,-1]
def cone0b : Fin 6 → ℝ := ![22/19,1/5,-1,17/20,-1/4,-1]
def cone0c : Fin 6 → ℝ := ![11/76,65/76,-1,51/76,-1/4,-1]
def cone1a : Fin 6 → ℝ := ![25/38,1/2,-1,259/304,-107/304,-1]
def cone1b : Fin 6 → ℝ := ![245/228,1/4,-1,853/912,-107/304,-1]
def cone1c : Fin 6 → ℝ := ![75/304,229/304,-1,235/304,-107/304,-1]
def cone2a : Fin 6 → ℝ := ![1481/1900,326/475,-1,853/950,-23/50,-1]
def cone2b : Fin 6 → ℝ := ![113/75,1/4,-1,313/300,-23/50,-1]
def cone2c : Fin 6 → ℝ := ![563/740,637/925,-1,823/925,-23/50,-1]

/-- Every certificate is nonnegative at the 36 residues and has nonnegative valuation coefficients. -/
theorem certificates_nonnegative :
    ∀ a ∈ [cone0a,cone0b,cone0c,cone1a,cone1b,cone1c,cone2a,cone2b,cone2c],
      0 ≤ a 0 ∧ 0 ≤ a 1 ∧
        ∀ i j : ℕ,1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → 0 ≤ linear a (point i j) := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    refine ⟨by norm_num [cone0a,cone0b,cone0c,cone1a,cone1b,cone1c,cone2a,cone2b,cone2c],
      by norm_num [cone0a,cone0b,cone0c,cone1a,cone1b,cone1c,cone2a,cone2b,cone2c],?_⟩ <;>
    intro i j hi hi6 hj hj6 <;> interval_cases i <;> interval_cases j <;>
    norm_num [linear,point,sourceExponent,netExponent,
      cone0a,cone0b,cone0c,cone1a,cone1b,cone1c,cone2a,cone2b,cone2c]

theorem certificate_weighted {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) (a : Fin 6 → ℝ)
    (ha : a ∈ [cone0a,cone0b,cone0c,cone1a,cone1b,cone1c,cone2a,cone2b,cone2c]) :
    0 ≤ linear a (weighted s i j w) := by
  have hres := certificates_nonnegative a ha
  obtain ⟨h0,h1,hres⟩ := hres
  exact weighted_linear_nonnegative s i j w hw hi hj a h0 h1 hres

theorem common_endpoint0 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (1/4) (weighted s i j w) ≤ (3/19)*weighted s i j w 0 := by
  set x := weighted s i j w
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  have cert := certificate_weighted s i j w hw hi hj
  by_cases hc : x 1 ≤ x 0
  · have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    have hr := cert cone0c (by simp)
    norm_num [linear,cone0c] at hr
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · simp only [commonValue,surplus,max_eq_left (by linarith : 0 ≤ x 0-x 1),max_eq_left hb,max_eq_right hn]
      linarith
    · simp only [commonValue,surplus,max_eq_left (by linarith : 0 ≤ x 0-x 1),
        max_eq_right (by linarith : 3*x 0-5*x 1-x 3 ≤ 0),max_eq_right hn]
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cert cone0b (by simp)
      norm_num [linear,cone0b] at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      linarith
    · have hr := cert cone0a (by simp)
      norm_num [linear,cone0a] at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,
        max_eq_right (by linarith : 3*x 1-5*x 0-x 3 ≤ 0)]
      linarith

theorem common_endpoint1 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (107/304) (weighted s i j w) ≤ (3/19)*weighted s i j w 0 := by
  set x := weighted s i j w
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  have cert := certificate_weighted s i j w hw hi hj
  by_cases hc : x 1 ≤ x 0
  · have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    have hr := cert cone1c (by simp)
    norm_num [linear,cone1c] at hr
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · simp only [commonValue,surplus,max_eq_left (by linarith : 0 ≤ x 0-x 1),max_eq_left hb,max_eq_right hn]
      linarith
    · simp only [commonValue,surplus,max_eq_left (by linarith : 0 ≤ x 0-x 1),
        max_eq_right (by linarith : 3*x 0-5*x 1-x 3 ≤ 0),max_eq_right hn]
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cert cone1b (by simp)
      norm_num [linear,cone1b] at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      linarith
    · have hr := cert cone1a (by simp)
      norm_num [linear,cone1a] at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,
        max_eq_right (by linarith : 3*x 1-5*x 0-x 3 ≤ 0)]
      linarith

theorem common_endpoint2 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (23/50) (weighted s i j w) ≤ (59/100)*weighted s i j w 0 := by
  set x := weighted s i j w
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  have cert := certificate_weighted s i j w hw hi hj
  by_cases hc : x 1 ≤ x 0
  · have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    have hr := cert cone2c (by simp)
    norm_num [linear,cone2c] at hr
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · simp only [commonValue,surplus,max_eq_left (by linarith : 0 ≤ x 0-x 1),max_eq_left hb,max_eq_right hn]
      linarith
    · simp only [commonValue,surplus,max_eq_left (by linarith : 0 ≤ x 0-x 1),
        max_eq_right (by linarith : 3*x 0-5*x 1-x 3 ≤ 0),max_eq_right hn]
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cert cone2b (by simp)
      norm_num [linear,cone2b] at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      linarith
    · have hr := cert cone2a (by simp)
      norm_num [linear,cone2a] at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,
        max_eq_right (by linarith : 3*x 1-5*x 0-x 3 ≤ 0)]
      linarith

theorem affine_interval_bound {f : ℝ → ℝ} {a b A S M r : ℝ}
    (hf : ∀ z,f z=A+z*S) (hr : r ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f r ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with h | h
  · have := mul_le_mul_of_nonneg_right hr.2 h
    linarith
  · have := mul_le_mul_of_nonpos_right hr.1 h
    linarith

/-- The common part less the surplus is at most `max (3/19) (4ρ - 5/4)` times the first ideal's
logarithm for every density `ρ ∈ [1/4, 23/50]`. -/
theorem common_weighted_bound {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (ρ : ℝ) (hr : 1/4 ≤ ρ) (hrhi : ρ ≤ 23/50) :
    commonValue ρ (weighted s i j w) ≤ max (3/19) (4*ρ-5/4)*weighted s i j w 0 := by
  set x := weighted s i j w
  have h0 := common_endpoint0 s i j w hw hi hj
  have h1 := common_endpoint1 s i j w hw hi hj
  have h2 := common_endpoint2 s i j w hw hi hj
  by_cases hs : ρ ≤ 107/304
  · rw [max_eq_left (by linarith : 4*ρ-5/4 ≤ (3/19:ℝ))]
    exact affine_interval_bound (f:=fun z => commonValue z x) (a:=1/4) (b:=107/304) (r:=ρ)
      (M:=(3/19)*x 0) (fun z => commonValue_affine z x) ⟨hr,hs⟩ h0 h1
  · rw [max_eq_right (by linarith : (3/19:ℝ) ≤ 4*ρ-5/4)]
    have hf : ∀ z,commonValue z x-(4*z-5/4)*x 0=
        commonValue 0 x+(5/4)*x 0+z*(-max (x 0-x 1) 0-x 3+x 4-4*x 0) := by
      intro z
      rw [commonValue_affine]
      ring
    have hh := affine_interval_bound (f:=fun z => commonValue z x-(4*z-5/4)*x 0)
      (a:=107/304) (b:=23/50) (r:=ρ) (M:=0) hf ⟨(lt_of_not_ge hs).le,hrhi⟩
      (by norm_num; linarith [h1]) (by norm_num; linarith [h2])
    linarith

/-- The common part of the HIGH exponent of a first-source label at density `ρ` and bin `δ`, for the
logarithms `c`, `d` of its two ideals, `R` of the active conductor, `E` of the inactive projector,
`Lc` of the numerator and `R₀` of the cancelled radical. -/
def firstCommon (ρ δ c d R E Lc R₀ : ℝ) : ℝ :=
  (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-max (3*c-5*d-R) 0/6+ρ*Lc+R₀

/-- The balanced common rate: with the surplus, the common part costs the rate
`δ - max (3/19) (4ρ - 5/4)` per unit of the first ideal's logarithm. -/
theorem common_weighted_saving {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t)
    (ρ δ E : ℝ) (hr : 1/4 ≤ ρ) (hrhi : ρ ≤ 23/50) :
    let x := weighted s i j w
    firstCommon ρ δ (x 0) (x 1) (x 3) E (x 4) (x 5)-surplus (x 0) (x 1) (x 2) (x 3) ≤
      -(δ-max (3/19) (4*ρ-5/4))*x 0-E := by
  have hh := common_weighted_bound s i j w hw hi hj ρ hr hrhi
  dsimp only
  unfold commonValue firstCommon at *
  nlinarith

/-- The balanced common rate of the bin `δ`: the HIGH saving per unit of removed slot width. -/
def commonRate (δ : ℝ) : ℝ := δ-max (3/19) (4*LocalMoment.unmarkedDensity δ-5/4)

end

end OAI.SevenEighths.Cycle63Moment.ValuationCone

end Record1252270103Bootstrap.PR67
