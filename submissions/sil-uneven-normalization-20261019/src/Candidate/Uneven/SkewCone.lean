import Mathlib.Tactic


noncomputable section
namespace SkewNormalization

def clip (s r : ℝ) : ℝ := max (-s) (min s r)

theorem clip_bounds {s r : ℝ} (hs : 0 ≤ s) :
    -s ≤ clip s r ∧ clip s r ≤ s := by
  unfold clip
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem allocations_nonnegative {s r : ℝ} (hs : 0 ≤ s) :
    0 ≤ s+clip s r ∧ 0 ≤ s-clip s r := by
  have hh := clip_bounds (r := r) hs
  constructor <;> linarith

theorem clip_odd {s r : ℝ} (hs : 0 ≤ s) :
    clip s (-r) = -clip s r := by
  unfold clip
  simp only [max_def, min_def]
  split_ifs <;> linarith


theorem clip_lipschitz {s s' r r' u v : ℝ}
    (hs : |s'-s| ≤ u) (hr : |r'-r| ≤ v) :
    |clip s' r'-clip s r| ≤ u+v := by
  have hu := le_trans (abs_nonneg _) hs
  have hv := le_trans (abs_nonneg _) hr
  rcases abs_le.mp hs with ⟨hs1,hs2⟩
  rcases abs_le.mp hr with ⟨hr1,hr2⟩
  rw [abs_le]
  unfold clip
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

def side (c d r : ℝ) : ℝ := max (3*c-5*d-r) 0 / 6
def surplus (c d r p : ℝ) : ℝ :=
  (c+d-r-2*p-side c d r-side d c r)/2
def skew (c d r p : ℝ) : ℝ := clip (surplus c d r p) ((d-c)/10)

theorem surplus_symmetric (c d r p : ℝ) :
    surplus d c r p=surplus c d r p := by
  unfold surplus
  ring

theorem skew_reflect (c d r p : ℝ) (hs : 0 ≤ surplus c d r p) :
    skew d c r p = -skew c d r p := by
  unfold skew
  rw [surplus_symmetric, show (c-d)/10 = -((d-c)/10) by ring]
  exact clip_odd hs

theorem side_lipschitz {c d r c' d' r' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w) (hr : |r'-r| ≤ w) :
    |side c' d' r'-side c d r| ≤ 3*w/2 := by
  rcases abs_le.mp hc with ⟨hc1,hc2⟩
  rcases abs_le.mp hd with ⟨hd1,hd2⟩
  rcases abs_le.mp hr with ⟨hr1,hr2⟩
  rw [abs_le]
  unfold side
  simp only [max_def]
  split_ifs <;> constructor <;> linarith

theorem surplus_lipschitz {c d r p c' d' r' p' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (hp : |p'-p| ≤ w) :
    |surplus c' d' r' p'-surplus c d r p| ≤ 4*w := by
  have ha := side_lipschitz hc hd hr
  have hb := side_lipschitz hd hc hr
  rcases abs_le.mp hc with ⟨hc1,hc2⟩
  rcases abs_le.mp hd with ⟨hd1,hd2⟩
  rcases abs_le.mp hr with ⟨hr1,hr2⟩
  rcases abs_le.mp hp with ⟨hp1,hp2⟩
  rcases abs_le.mp ha with ⟨ha1,ha2⟩
  rcases abs_le.mp hb with ⟨hb1,hb2⟩
  rw [abs_le]
  unfold surplus
  constructor <;> linarith

theorem skew_lipschitz {c d r p c' d' r' p' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (hp : |p'-p| ≤ w) :
    |skew c' d' r' p'-skew c d r p| ≤ 21*w/5 := by
  have hs := surplus_lipschitz hc hd hr hp
  have hh : |(d'-c')/10-(d-c)/10| ≤ w/5 := by
    rcases abs_le.mp hc with ⟨hc1,hc2⟩
    rcases abs_le.mp hd with ⟨hd1,hd2⟩
    rw [abs_le]
    constructor <;> linarith
  have hh' := clip_lipschitz hs hh
  change |skew c' d' r' p'-skew c d r p| ≤ _ at hh'
  linarith

end SkewNormalization

namespace SkewCone
open SkewNormalization
def linear (a x : Fin 6 → ℝ) : ℝ :=
  a 0*x 0+a 1*x 1+a 2*x 2+a 3*x 3+a 4*x 4+a 5*x 5
def point (i j : ℕ) : Fin 6 → ℝ :=
  let n := (i+5*j)%6
  ![(i:ℝ),(j:ℝ),1,if n=0 then 0 else 1,
    (if n=0 ∨ n=5 then 0 else (1+n):ℕ),if n=5 then 1 else 0]
def admissible (a : Fin 6 → ℝ) : Prop :=
  0 ≤ a 0 ∧ 0 ≤ a 1 ∧
  ∀ i j : ℕ, 1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → 0 ≤ linear a (point i j)
def value (rho : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  (1-rho)*max (x 0-x 1) 0-(1+rho)*x 3-max (3*x 0-5*x 1-x 3) 0/6+
  rho*x 4+x 5-surplus (x 0) (x 1) (x 3) (x 2)-skew (x 0) (x 1) (x 3) (x 2)

theorem positive_valuation_linear (a : Fin 6 → ℝ) (ha : admissible a)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) : 0 ≤ linear a (point i j) := by
  let i0 := (i-1)%6+1
  let j0 := (j-1)%6+1
  have hi01 : 1 ≤ i0 := by dsimp [i0]; omega
  have hi06 : i0 ≤ 6 := by dsimp [i0]; omega
  have hj01 : 1 ≤ j0 := by dsimp [j0]; omega
  have hj06 : j0 ≤ 6 := by dsimp [j0]; omega
  have hi0i : i0 ≤ i := by dsimp [i0]; omega
  have hj0j : j0 ≤ j := by dsimp [j0]; omega
  have hn : (i+5*j)%6=(i0+5*j0)%6 := by dsimp [i0,j0]; omega
  have hid : linear a (point i j)=linear a (point i0 j0)+
      a 0*((i:ℝ)-(i0:ℝ))+a 1*((j:ℝ)-(j0:ℝ)) := by
    simp [linear,point,hn]
    ring
  have hx : 0 ≤ (i:ℝ)-(i0:ℝ) := sub_nonneg.mpr (by exact_mod_cast hi0i)
  have hy : 0 ≤ (j:ℝ)-(j0:ℝ) := sub_nonneg.mpr (by exact_mod_cast hj0j)
  rw [hid]
  exact add_nonneg (add_nonneg (ha.2.2 i0 j0 hi01 hi06 hj01 hj06)
    (mul_nonneg ha.1 hx)) (mul_nonneg ha.2.1 hy)

def weighted {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ) : Fin 6 → ℝ :=
  fun k => ∑ t ∈ s,w t*point (i t) (j t) k

theorem weighted_cone {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t ∈ s,0 ≤ w t)
    (hi : ∀ t ∈ s,0 < i t) (hj : ∀ t ∈ s,0 < j t) :
    (∀ k,0 ≤ weighted s i j w k) ∧
    (∀ a,admissible a → 0 ≤ linear a (weighted s i j w)) := by
  constructor
  · intro k
    apply Finset.sum_nonneg
    intro t ht
    apply mul_nonneg (hw t ht)
    fin_cases k <;> simp [point] <;> positivity
  · intro a ha
    have he : linear a (weighted s i j w)=∑ t ∈ s,w t*linear a (point (i t) (j t)) := by
      simp [linear,weighted,Finset.mul_sum,mul_add,Finset.sum_add_distrib,
        mul_assoc,mul_left_comm]
    rw [he]
    exact Finset.sum_nonneg (fun t ht => mul_nonneg (hw t ht)
      (positive_valuation_linear a ha (i t) (j t) (hi t ht) (hj t ht)))

lemma certificate_0 : admissible ![(2/5:ℝ),(0:ℝ),(0:ℝ),(5/4:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_1 : admissible ![(4/5:ℝ),(3/5:ℝ),(-1:ℝ),(3/4:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_2 : admissible ![(7/5:ℝ),(1:ℝ),(-2:ℝ),(1/4:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_3 : admissible ![(73/60:ℝ),(7/20:ℝ),(-1:ℝ),(5/6:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_4 : admissible ![(67/30:ℝ),(1/2:ℝ),(-2:ℝ),(5/12:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_5 : admissible ![(21/20:ℝ),(11/60:ℝ),(-1:ℝ),(2/3:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_6 : admissible ![(0:ℝ),(1/6:ℝ),(0:ℝ),(17/15:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_7 : admissible ![(1/20:ℝ),(27/20:ℝ),(-1:ℝ),(3/4:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_8 : admissible ![(13/20:ℝ),(7/4:ℝ),(-2:ℝ),(1/4:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_9 : admissible ![(0:ℝ),(27/50:ℝ),(0:ℝ),(33/25:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_10 : admissible ![(7/15:ℝ),(11/10:ℝ),(-1:ℝ),(5/6:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_11 : admissible ![(89/60:ℝ),(5/4:ℝ),(-2:ℝ),(5/12:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_12 : admissible ![(23/260:ℝ),(1/52:ℝ),(0:ℝ),(287/260:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_13 : admissible ![(3/10:ℝ),(14/15:ℝ),(-1:ℝ),(2/3:ℝ),(-1/4:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_14 : admissible ![(492/2425:ℝ),(984/2425:ℝ),(-166/485:ℝ),(5927/4850:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_15 : admissible ![(4/5:ℝ),(3/5:ℝ),(-1:ℝ),(24/25:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_16 : admissible ![(7/5:ℝ),(1:ℝ),(-2:ℝ),(23/50:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_17 : admissible ![(809/675:ℝ),(77/225:ℝ),(-44/45:ℝ),(1421/1350:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_18 : admissible ![(73/60:ℝ),(7/20:ℝ),(-1:ℝ),(313/300:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_19 : admissible ![(67/30:ℝ),(1/2:ℝ),(-2:ℝ),(47/75:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_20 : admissible ![(97/325:ℝ),(11/65:ℝ),(0:ℝ),(971/650:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_21 : admissible ![(43/50:ℝ),(1/2:ℝ),(-1:ℝ),(47/50:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_22 : admissible ![(528/2575:ℝ),(1056/2575:ℝ),(-181/515:ℝ),(6263/5150:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_23 : admissible ![(13/50:ℝ),(57/50:ℝ),(-1:ℝ),(24/25:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_24 : admissible ![(43/50:ℝ),(77/50:ℝ),(-2:ℝ),(23/50:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_25 : admissible ![(89/1150:ℝ),(471/1150:ℝ),(0:ℝ),(1729/1150:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_26 : admissible ![(203/300:ℝ),(89/100:ℝ),(-1:ℝ),(313/300:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_27 : admissible ![(127/75:ℝ),(26/25:ℝ),(-2:ℝ),(47/75:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

lemma certificate_28 : admissible ![(51/100:ℝ),(217/300:ℝ),(-1:ℝ),(263/300:ℝ),(-23/50:ℝ),(-1:ℝ)] := by
  refine ⟨by norm_num,by norm_num,?_⟩
  intro i j hi hi' hj hj'
  interval_cases i <;> interval_cases j <;> norm_num [linear,point]

theorem endpoint_low (x : Fin 6 → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hlin : ∀ a, admissible a → 0 ≤ linear a x)
    (hs : 0 ≤ surplus (x 0) (x 1) (x 3) (x 2)) :
    value (1/4:ℝ) x ≤ (2/5:ℝ)*x 0 := by
  have hx0 := hx 0
  have hx1 := hx 1
  have hx3 := hx 3
  by_cases h : 0 ≤ x 0-x 1

  · by_cases ha : 0 ≤ 3*x 0-5*x 1-x 3

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by rw [max_eq_left hb]; linarith

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_8

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_12

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_13

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_8

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_12

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_13

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 3*x 1-5*x 0-x 3 := by exact max_eq_left hb

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_11

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_9

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_10

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_8

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_6

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_7

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

  · by_cases ha : 0 ≤ 3*x 0-5*x 1-x 3

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by rw [max_eq_left hb]; linarith

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_2

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_0

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_5

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_2

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_0

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_5

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 3*x 1-5*x 0-x 3 := by exact max_eq_left hb

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_4

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_0

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_3

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_2

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_0

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_1

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

theorem endpoint_high (x : Fin 6 → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hlin : ∀ a, admissible a → 0 ≤ linear a x)
    (hs : 0 ≤ surplus (x 0) (x 1) (x 3) (x 2)) :
    value (23/50:ℝ) x ≤ (2/5:ℝ)*x 0 := by
  have hx0 := hx 0
  have hx1 := hx 1
  have hx3 := hx 3
  by_cases h : 0 ≤ x 0-x 1

  · by_cases ha : 0 ≤ 3*x 0-5*x 1-x 3

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by rw [max_eq_left hb]; linarith

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_24

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_22

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_28

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_24

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_22

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_28

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 3*x 1-5*x 0-x 3 := by exact max_eq_left hb

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_27

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_25

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_26

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = x 0-x 1 := by exact max_eq_left h

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_24

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_22

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_23

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

  · by_cases ha : 0 ≤ 3*x 0-5*x 1-x 3

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by rw [max_eq_left hb]; linarith

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_16

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_20

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_21

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 3*x 0-5*x 1-x 3 := by exact max_eq_left ha

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_16

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_20

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_21

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

    · by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 3*x 1-5*x 0-x 3 := by exact max_eq_left hb

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_19

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_17

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_18

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

      · have hma : max (3*x 0-5*x 1-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge ha)

        have hmb : max (3*x 1-5*x 0-x 3) 0 = 0 := by exact max_eq_right (le_of_not_ge hb)

        have hmc : max (x 0-x 1) 0 = 0 := by exact max_eq_right (le_of_not_ge h)

        by_cases hh : surplus (x 0) (x 1) (x 3) (x 2) ≤ (x 1-x 0)/10

        · have hc := hlin _ certificate_16

          have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = surplus (x 0) (x 1) (x 3) (x 2) := by
            unfold clip
            rw [min_eq_left hh, max_eq_right (by linarith)]

          norm_num [linear] at hc

          unfold value skew
          rw [ht,hmc,hma]

          simp only [surplus, side, hma, hmb] at *
          linarith

        · by_cases hl : (x 1-x 0)/10 ≤ -surplus (x 0) (x 1) (x 3) (x 2)

          · have hc := hlin _ certificate_14

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = -surplus (x 0) (x 1) (x 3) (x 2) := by
              unfold clip
              rw [min_eq_right (by linarith), max_eq_left hl]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith

          · have hc := hlin _ certificate_15

            have ht : clip (surplus (x 0) (x 1) (x 3) (x 2)) ((x 1-x 0)/10) = (x 1-x 0)/10 := by
              unfold clip
              rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

            norm_num [linear] at hc

            unfold value skew
            rw [ht,hmc,hma]

            simp only [surplus, side, hma, hmb] at *
            linarith


theorem full_range (x : Fin 6 → ℝ) (rho : ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hlin : ∀ a, admissible a → 0 ≤ linear a x)
    (hs : 0 ≤ surplus (x 0) (x 1) (x 3) (x 2))
    (hr0 : 1/4 ≤ rho) (hr1 : rho ≤ 23/50) :
    value rho x ≤ (2/5:ℝ)*x 0 := by
  have h0 := endpoint_low x hx hlin hs
  have h1 := endpoint_high x hx hlin hs
  have hid : (21/100:ℝ)*(value rho x-(2/5:ℝ)*x 0) =
      (23/50-rho)*(value (1/4) x-(2/5:ℝ)*x 0)+
      (rho-1/4)*(value (23/50) x-(2/5:ℝ)*x 0) := by
    unfold value
    ring
  have hh0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr1) (sub_nonpos.mpr h0)
  have hh1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr0) (sub_nonpos.mpr h1)
  linarith

theorem weighted_full_range {ι : Type*} (s : Finset ι) (i j : ι → ℕ)
    (w : ι → ℝ) (hw : ∀ t ∈ s,0 ≤ w t)
    (hi : ∀ t ∈ s,0 < i t) (hj : ∀ t ∈ s,0 < j t)
    (rho : ℝ) (hr0 : 1/4 ≤ rho) (hr1 : rho ≤ 23/50)
    (hs : 0 ≤ surplus (weighted s i j w 0) (weighted s i j w 1)
      (weighted s i j w 3) (weighted s i j w 2)) :
    value rho (weighted s i j w) ≤ (2/5:ℝ)*weighted s i j w 0 := by
  have hh := weighted_cone s i j w hw hi hj
  exact full_range _ rho hh.1 hh.2 hs hr0 hr1
end SkewCone
