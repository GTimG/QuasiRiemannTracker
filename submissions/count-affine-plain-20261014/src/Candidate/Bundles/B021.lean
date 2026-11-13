/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Mathlib.Tactic

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.Basis; sha256 08fce305df1a39de5659de9c76f4958224c35f0891e588b89f79227989d94d7c -/
section
                     

namespace Cycle61.Arithmetic.Bernstein

noncomputable def basis2 (u : ℝ) : Fin 3 → ℝ :=
  ![(1-u)^2, 2*u*(1-u), u^2]

noncomputable def basis3 (v : ℝ) : Fin 4 → ℝ :=
  ![(1-v)^3, 3*v*(1-v)^2, 3*v^2*(1-v), v^3]

noncomputable def tensor (c : Fin 3 → Fin 4 → ℝ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * (basis2 u i * basis3 v j)

theorem basis2_nonneg {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : Fin 3) :
    0 ≤ basis2 u i := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1-u := by linarith [hu.2]
  fin_cases i <;> simp [basis2] <;> positivity

theorem basis3_nonneg {v : ℝ} (hv : v ∈ Set.Icc 0 1) (j : Fin 4) :
    0 ≤ basis3 v j := by
  have hv0 : 0 ≤ v := hv.1
  have h : 0 ≤ 1-v := by linarith [hv.2]
  fin_cases j <;> simp [basis3] <;> positivity

theorem basis2_partition (u : ℝ) : (∑ i, basis2 u i) = 1 := by
  simp [basis2, Fin.sum_univ_succ]
  ring

theorem basis3_partition (v : ℝ) : (∑ j, basis3 v j) = 1 := by
  simp [basis3, Fin.sum_univ_succ]
  ring

theorem tensor_partition (u v : ℝ) :
    (∑ i, ∑ j, basis2 u i * basis3 v j) = 1 := by
  simp_rw [← Finset.mul_sum]
  rw [basis3_partition]
  simp only [mul_one]
  exact basis2_partition u

theorem tensor_lower_bound {c : Fin 3 → Fin 4 → ℝ} {m u v : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : m ≤ tensor c u v := by
  have hl : (∑ i : Fin 3, ∑ j : Fin 4, m * (basis2 u i * basis3 v j)) ≤
      tensor c u v := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hc i j)
      (mul_nonneg (basis2_nonneg hu i) (basis3_nonneg hv j))
  simpa only [← Finset.mul_sum, basis2_partition, basis3_partition, mul_one] using hl

theorem tensor_pos {c : Fin 3 → Fin 4 → ℝ} {m u v : ℝ}
    (hm : 0 < m) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : 0 < tensor c u v :=
  hm.trans_le (tensor_lower_bound hu hv hc)

theorem normalize_mem {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    (x-a)/(b-a) ∈ Set.Icc 0 1 := by
  have h : 0 < b-a := sub_pos.mpr hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt h)
  · apply (div_le_one h).mpr
    linarith [hx.2]

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.Basis -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.NewRow; sha256 b1fdfca9dd19b18909579b3183cbbdd15e06b10a436cf63068eafa59ff72591d -/
section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Cycle61.Arithmetic.Bernstein
noncomputable section
/- Exact successor proof at 4374299/5000000. The original polynomial box
certificate is regenerated as a global quadratic certificate in u=1/2-p.
Original source attribution remains in the surrounding module notice. -/
private theorem successor_quadratic_pos (a b c t : ℝ)
    (ha : 0 < a) (hgap : 0 < 4*a*c-b^2) : 0 < a*t^2+b*t+c := by
  have hid : 4*a*(a*t^2+b*t+c) = (2*a*t+b)^2+(4*a*c-b^2) := by ring
  have hp : 0 < 4*a*(a*t^2+b*t+c) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hgap
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*a)).mp hp

private theorem successor_quadratic_nonneg (a b c t : ℝ)
    (ha : 0 < a) (hgap : 0 ≤ 4*a*c-b^2) : 0 ≤ a*t^2+b*t+c := by
  have hid : 4*a*(a*t^2+b*t+c) = (2*a*t+b)^2+(4*a*c-b^2) := by ring
  have hp : 0 ≤ 4*a*(a*t^2+b*t+c) := by
    rw [hid]
    exact add_nonneg (sq_nonneg _) hgap
  exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*a)).mp hp

noncomputable def newRowPower (δ p : ℝ) : ℝ :=
  ((113814167513415349029739703 / 549278316342000000000000000 : ℝ) * δ ^ 2 + (-25615206623328552988243901 / 131826795922080000000000000 : ℝ) * δ + (1844249343483661 / 40484858400000000 : ℝ)) +
  ((1/2-p)*((1023042592502972486143337 / 2542955168250000000000000 : ℝ) * δ ^ 2 + (-16603443891808618616260099 / 82391747451300000000000000 : ℝ) * δ + (4237877421483661 / 101212146000000000 : ℝ)) + (1/2-p)^2*((4556192814664357514919989 / 15257731009500000000000000 : ℝ) * δ ^ 2 + (7189393507912291796779901 / 164783494902600000000000000 : ℝ) * δ + (0 / 1 : ℝ)) + (1/2-p)^3*((3732262134113761933 / 27463915817100000000 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ)))

theorem newRowGlobal_pos (δ p : ℝ) (hδ : 0 ≤ δ) (hp : p ≤ 1/2) :
    0 < newRowPower δ p := by
  have hu : 0 ≤ 1/2-p := by linarith
  have h0 : 0 < (113814167513415349029739703 / 549278316342000000000000000 : ℝ) * δ ^ 2 + (-25615206623328552988243901 / 131826795922080000000000000 : ℝ) * δ + (1844249343483661 / 40484858400000000 : ℝ) :=
    successor_quadratic_pos _ _ _ _ (by norm_num) (by norm_num)
  have h1 : 0 ≤ (1023042592502972486143337 / 2542955168250000000000000 : ℝ) * δ ^ 2 + (-16603443891808618616260099 / 82391747451300000000000000 : ℝ) * δ + (4237877421483661 / 101212146000000000 : ℝ) :=
    successor_quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h2 : 0 ≤ (4556192814664357514919989 / 15257731009500000000000000 : ℝ) * δ ^ 2 + (7189393507912291796779901 / 164783494902600000000000000 : ℝ) * δ + (0 / 1 : ℝ) := by positivity
  have h3 : 0 ≤ (3732262134113761933 / 27463915817100000000 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ) := by positivity
  unfold newRowPower
  exact add_pos_of_pos_of_nonneg h0 (by positivity)

theorem newRowBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/8)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < newRowPower δ p := by
  exact newRowGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem newRowBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc (0) (1/4)) :
    0 < newRowPower δ p := by
  exact newRowGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem newRowBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < newRowPower δ p := by
  exact newRowGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem newRowBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < newRowPower δ p := by
  exact newRowGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem newRowBox4_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < newRowPower δ p := by
  exact newRowGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem newRowBox5_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < newRowPower δ p := by
  exact newRowGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

end
end Cycle61.Arithmetic.Bernstein
end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.NewRow -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.OldHalf; sha256 6b4d80e895bf7389b2dca4661a712bab0b4c5d94d6e2c6fdb140167ed0a48877 -/
section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Cycle61.Arithmetic.Bernstein
noncomputable section
/- Exact successor proof at 4374299/5000000. The original polynomial box
certificate is regenerated as a global quadratic certificate in u=1/2-p.
Original source attribution remains in the surrounding module notice. -/
noncomputable def oldHalfPower (δ p : ℝ) : ℝ :=
  ((362909481949932573487 / 948509120178270000000 : ℝ) * δ ^ 2 + (-102372669222519891704029603 / 142276368026740500000000000 : ℝ) * δ + (108771292479268373 / 289177560000000000 : ℝ)) +
  ((1/2-p)*((2638803904157300519 / 13173737780253750000 : ℝ) * δ ^ 2 + (-26554563115195612286031799 / 71138184013370250000000000 : ℝ) * δ + (249944187933268373 / 722943900000000000 : ℝ)) + (1/2-p)^2*((134349778394337327 / 8782491853502500000 : ℝ) * δ ^ 2 + (70082298029182324489 / 284552736053481000000 : ℝ) * δ + (0 / 1 : ℝ)) + (1/2-p)^3*((10176554858314 / 94850912017827 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ)))

theorem oldHalfGlobal_pos (δ p : ℝ) (hδ : 0 ≤ δ) (hp : p ≤ 1/2) :
    0 < oldHalfPower δ p := by
  have hu : 0 ≤ 1/2-p := by linarith
  have h0 : 0 < (362909481949932573487 / 948509120178270000000 : ℝ) * δ ^ 2 + (-102372669222519891704029603 / 142276368026740500000000000 : ℝ) * δ + (108771292479268373 / 289177560000000000 : ℝ) :=
    successor_quadratic_pos _ _ _ _ (by norm_num) (by norm_num)
  have h1 : 0 ≤ (2638803904157300519 / 13173737780253750000 : ℝ) * δ ^ 2 + (-26554563115195612286031799 / 71138184013370250000000000 : ℝ) * δ + (249944187933268373 / 722943900000000000 : ℝ) :=
    successor_quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h2 : 0 ≤ (134349778394337327 / 8782491853502500000 : ℝ) * δ ^ 2 + (70082298029182324489 / 284552736053481000000 : ℝ) * δ + (0 / 1 : ℝ) := by positivity
  have h3 : 0 ≤ (10176554858314 / 94850912017827 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ) := by positivity
  unfold oldHalfPower
  exact add_pos_of_pos_of_nonneg h0 (by positivity)

theorem oldHalfBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldHalfPower δ p := by
  exact oldHalfGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

end
end Cycle61.Arithmetic.Bernstein
end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.OldHalf -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.OldJunction; sha256 04f8a9578dc551bc958663a9fbe3d5b86a7bea0e2020f692d01b45807b30a018 -/
section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace Cycle61.Arithmetic.Bernstein
noncomputable section
/- Exact successor proof at 4374299/5000000. The original polynomial box
certificate is regenerated as a global quadratic certificate in u=1/2-p.
Original source attribution remains in the surrounding module notice. -/
noncomputable def oldJunctionPower (δ p : ℝ) : ℝ :=
  ((394813599653478376441253 / 1897018240356540000000000 : ℝ) * δ ^ 2 + (-1118394132280832433862771 / 5691054721069620000000000 : ℝ) * δ + (1889391932688661 / 40484858400000000 : ℝ)) +
  ((1/2-p)*((42256092873020116850083 / 105389902242030000000000 : ℝ) * δ ^ 2 + (-286885896356943569597249 / 1422763680267405000000000 : ℝ) * δ + (4341610010688661 / 101212146000000000 : ℝ)) + (1/2-p)^2*((1306327205627435851 / 4391245926751250000 : ℝ) * δ ^ 2 + (3208465961393113801 / 71138184013370250000 : ℝ) * δ + (0 / 1 : ℝ)) + (1/2-p)^3*((12922938583939 / 94850912017827 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ)))

theorem oldJunctionGlobal_pos (δ p : ℝ) (hδ : 0 ≤ δ) (hp : p ≤ 1/2) :
    0 < oldJunctionPower δ p := by
  have hu : 0 ≤ 1/2-p := by linarith
  have h0 : 0 < (394813599653478376441253 / 1897018240356540000000000 : ℝ) * δ ^ 2 + (-1118394132280832433862771 / 5691054721069620000000000 : ℝ) * δ + (1889391932688661 / 40484858400000000 : ℝ) :=
    successor_quadratic_pos _ _ _ _ (by norm_num) (by norm_num)
  have h1 : 0 ≤ (42256092873020116850083 / 105389902242030000000000 : ℝ) * δ ^ 2 + (-286885896356943569597249 / 1422763680267405000000000 : ℝ) * δ + (4341610010688661 / 101212146000000000 : ℝ) :=
    successor_quadratic_nonneg _ _ _ _ (by norm_num) (by norm_num)
  have h2 : 0 ≤ (1306327205627435851 / 4391245926751250000 : ℝ) * δ ^ 2 + (3208465961393113801 / 71138184013370250000 : ℝ) * δ + (0 / 1 : ℝ) := by positivity
  have h3 : 0 ≤ (12922938583939 / 94850912017827 : ℝ) * δ ^ 2 + (0 / 1 : ℝ) * δ + (0 / 1 : ℝ) := by positivity
  unfold oldJunctionPower
  exact add_pos_of_pos_of_nonneg h0 (by positivity)

theorem oldJunctionBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/8)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldJunctionPower δ p := by
  exact oldJunctionGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem oldJunctionBox1_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (3/4)) (hp : p ∈ Set.Icc (0) (1/4)) :
    0 < oldJunctionPower δ p := by
  exact oldJunctionGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem oldJunctionBox2_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (9/16)) (hp : p ∈ Set.Icc (1/4) (3/8)) :
    0 < oldJunctionPower δ p := by
  exact oldJunctionGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem oldJunctionBox3_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8) (15/32)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < oldJunctionPower δ p := by
  exact oldJunctionGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem oldJunctionBox4_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32) (9/16)) (hp : p ∈ Set.Icc (3/8) (1/2)) :
    0 < oldJunctionPower δ p := by
  exact oldJunctionGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

theorem oldJunctionBox5_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (9/16) (3/4)) (hp : p ∈ Set.Icc (1/4) (1/2)) :
    0 < oldJunctionPower δ p := by
  exact oldJunctionGlobal_pos δ p (by linarith [hδ.1]) (by linarith [hp.2])

end
end Cycle61.Arithmetic.Bernstein
end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.OldJunction -/
