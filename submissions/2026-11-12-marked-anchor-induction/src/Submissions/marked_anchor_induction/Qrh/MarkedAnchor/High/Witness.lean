/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from the OpenAI baseline `HeckeDetectorSimultaneousSupport.from_actual_zero`,
`from_actual_maximum` and `HeckeDetectorSupportedWitness.actual_supported_witness_family`
(Apache-2.0): the fixed bound `i ≤ I` on the height index is replaced by the height budget
`(3 + (3i+2) Z^τ)^4 ≤ (Z^d)^η` itself (with `η ≤ 2`), which is all the proof uses. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness

/-!
# High.Witness

Supported same-zero witnesses at an UNBOUNDED height index. The HIGH rows of the packed leaf have
zero heights `3 (binIndex p h + 1) Z^τ`, with `h` up to `Z^(small)`; the baseline witness family needs
`i ≤ I` with `I` fixed before the scale. The proof only uses `I` through
* `uniform_zero_height` (`3i Z^τ ≤ (Z^d)^(1/2)`), and
* `uniform_height_budget` (`(3 + (3i+2) Z^τ)^4 ≤ (Z^d)^η`).

Both follow from the budget hypothesis, so `budget_supported_witness_family` takes the budget for
each `i`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical Topology
open Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows

/-- `from_actual_zero` with the height budget in place of `i ≤ I`. -/
theorem budget_from_actual_zero (dmin dmax τ ε e κ η : ℝ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η) (hη2 : η ≤ 2)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hFourier.and (hcost.and (hT.and (eventually_ge_atTop (1 : ℝ)))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hbud ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  -- the zero height from the budget
  have hheight : ((3*i : ℕ) : ℝ)*Z^τ ≤ U^(1/2 : ℝ) := by
    have hZτ : 0 ≤ Z^τ := Real.rpow_nonneg (by linarith) _
    have h1 : ((3*i : ℕ) : ℝ)*Z^τ ≤ 3+(3*i+2 : ℕ)*Z^τ := by
      have : ((3*i : ℕ) : ℝ) ≤ ((3*i+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3*i ≤ 3*i+2)
      nlinarith
    have h1' : 1 ≤ 3+(3*i+2 : ℕ)*Z^τ := by
      have : (0:ℝ) ≤ ((3*i+2 : ℕ) : ℝ)*Z^τ := by positivity
      linarith
    have h3 : U^η ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU1.le hη2
    have hx4 : (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (U^(1/2 : ℝ))^4 := by
      have : (U^(1/2 : ℝ))^4 = U^(2:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hUp.le]; norm_num
      rw [this]; exact hbud.trans h3
    have hx : 3+(3*i+2 : ℕ)*Z^τ ≤ U^(1/2 : ℝ) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hUp.le _) hx4
    exact h1.trans hx
  have hh := him.trans hheight
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq hbud
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,
    (by linarith [hsupport.2]),hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

/-- **Supported witnesses at an unbounded height index** (budget version of
`actual_supported_witness_family`). -/
theorem budget_supported_witness_family (dmin dmax τ ε e κ η : ℝ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η) (hη2 : η ≤ 2)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),
        (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := budget_from_actual_zero dmin dmax τ ε e κ η hdmin hdmax hτ hε he he' hκ
    hκ' hη hη2 hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hbud ha ha' hnext hcurrent hQ tstar ht ht'
  have hw (u : Row) : Nonempty (SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i) := by
    obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained (χ u) (hχ u)
      ((3*i : ℕ)*Z^τ) (ha.trans_le (hcurrent u))
    have hρ : a≤ρ.re := by rw [heq]; exact hcurrent u
    obtain ⟨J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hprod,hM,hS⟩ :=
      hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hbud ha.le ha' (hnext u) j (hQ u j) ρ hzero hρ him
        tstar ht ht'
    exact ⟨⟨⟨j,ρ,hzero,hρ,him,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
      nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩,hprod⟩⟩
  exact ⟨fun u => Classical.choice (hw u)⟩

end
end Qrh.MarkedAnchor.High
