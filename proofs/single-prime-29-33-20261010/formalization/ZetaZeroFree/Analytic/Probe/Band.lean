import ZetaZeroFree.Analytic.Probe.Collected
import ZetaZeroFree.Analytic.Probe.Assembly
import ZetaZeroFree.Analytic.Parameters
import ZetaZeroFree.Analytic.Starter.Nonvanishing
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

namespace ZetaZeroFree.Analytic.Probe
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ZetaZeroFree.Analytic.Rows
local notation "O" => HeckeFamily.O

lemma source_dyad_geometry_eventually (dmin dmax margin vmax δlo : ℝ)
    (_hdmin : 0<dmin) (hdmin1 : dmin≤δlo) (hmargin : 0<margin)
    (hdmax : vmax+2*margin≤dmax) :
    ∀ᶠZ : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δlo≤rowNorm u ∧ rowNorm u≤Z^vmax) →
      ∀k : ℕ,(rows∩dyadicRows 1 k).Nonempty →
        0≤sourceDyadExponent Z k ∧ sourceDyadExponent Z k≤vmax ∧
        dmin≤sourceDyadConductor Z margin k ∧ sourceDyadConductor Z margin k≤dmax ∧
        (∀u∈rows∩dyadicRows 1 k,
          Z^(sourceDyadExponent Z k)≤rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k)) ∧
        (∀u∈rows∩dyadicRows 1 k,rowNorm u≤Z^(sourceDyadConductor Z margin k-margin)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<δlo-dmin+2*margin by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hsmall hmarginZ
  intro rows hrows k hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  obtain ⟨u,hu⟩ := hne
  have hur := (Finset.mem_inter.mp hu).1
  have hud := mem_dyadicRows.mp (Finset.mem_inter.mp hu).2
  have hlow : (2:ℝ)^k≤rowNorm u := by simpa only [one_mul] using hud.2.1
  have hhigh : rowNorm u<2*(2:ℝ)^k := by simpa only [one_mul] using hud.2.2
  have hv0 : 0≤sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ,Real.rpow_zero]
    exact one_le_pow₀ (by norm_num)
  have hvmax : sourceDyadExponent Z k≤vmax := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    exact hlow.trans (hrows u hur).2.2
  have hvmin : dmin-2*margin≤sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    have hh : 2*Z^(dmin-2*margin)≤Z^δlo := by
      calc
        _ ≤ Z^(δlo-dmin+2*margin)*Z^(dmin-2*margin) := mul_le_mul_of_nonneg_right hsmall (by positivity)
        _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring
    linarith [(hrows u hur).2.1]
  have hnorm : ∀u∈rows∩dyadicRows 1 k,
      Z^(sourceDyadExponent Z k)≤rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k) := by
    intro u hu
    rw [sourceDyad_scale hZ]
    have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
    simpa only [one_mul] using And.intro hh.1 hh.2.le
  refine ⟨hv0,hvmax,?_,?_,hnorm,?_⟩
  · unfold sourceDyadConductor;linarith
  · unfold sourceDyadConductor;linarith
  · exact dyad_conductor_margin Z (sourceDyadExponent Z k) margin hZp hmarginZ _ (fun u hu=>(hnorm u hu).2)

lemma detector_maximum_le_eleven_twelfths {Label : Type*} [Fintype Label]
    (χ : Label → Character) (T : ℝ) : detectorMaximum χ T ≤ (11 / 12 : ℝ) := by
  rcases lt_or_ge (51 / 100 : ℝ) (detectorMaximum χ T) with h | h
  · obtain ⟨label, s, hz, hpole, ht, heq⟩ := detectorMaximum_attained χ T h
    rw [← heq]
    exact (HeckeZeroSupremum.zero_re_le_beta (χ label) (by rw [heq]; linarith)
      (by simpa only [not_and_or, or_comm] using hpole) hz).trans
      Starter.beta_le_eleven_twelfths
  · linarith

lemma central_exponent_with_halo {a beta d v ζ margin countLoss e eps loss mesh overhead : ℝ}
    {N : ℕ} (ha : 51 / 100 ≤ a) (ha' : 2 * a - 1 ≤ 5 / 6)
    (hζ : 0 ≤ ζ) (hmargin : 0 ≤ margin) (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hcount : 0 ≤ countLoss) (hd : d ≤ (25 / 33 : ℝ) + ζ + 2 * margin)
    (hvd : v ≤ d) (hh : d - v ≤ 2 * margin) :
    ((6 / 11) * a - 197 / 330 + (146 / 11) * e) +
      (5 / 33) * (-(4 / 25) + (a - 1 / 2) + mesh) + loss +
      d * (Exponent.R0 (2 * a - 1) + countLoss) +
      v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + overhead ≤
    (20 / 99 : ℝ) + 2 * ζ + 6 * margin + (146 / 11) * e +
      ((25 / 33 : ℝ) + ζ + 2 * margin) * (countLoss + 12 * e + eps * (N + 8)) +
      (5 / 33) * mesh + loss + overhead := by
  let δ := 2 * a - 1
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have hδ' : δ ≤ 5 / 6 := ha'
  have hden := Exponent.denominator_positive hδ'
  have hR : Exponent.R0 δ ≤ 1 := by
    unfold Exponent.R0
    have := div_nonneg (show 0 ≤ 10 * δ by positivity) (show 0 ≤ 3 * (5 - 2 * δ) by positivity)
    linarith
  have hs : 0 ≤ Exponent.slope δ := (Exponent.slope_positive hδ hδ').le
  have hs' : Exponent.slope δ ≤ 2 := by unfold Exponent.slope Exponent.z0; linarith
  have hE : Exponent.E δ beta d ≤ Exponent.b - beta + 2 * (ζ + 2 * margin) := by
    have heh := Exponent.E_le_boundary (beta := beta) hδ hδ' (le_refl Exponent.h)
    have hed := Exponent.E_difference δ beta d
    have hbuf : d - Exponent.h ≤ ζ + 2 * margin := by
      norm_num [Exponent.h, Exponent.x, Exponent.ell] at hd ⊢
      linarith
    by_cases hd' : d ≤ Exponent.h
    · have hx := Exponent.E_le_boundary (beta := beta) hδ hδ' hd'
      linarith
    · have hm := mul_le_mul hbuf hs' hs (by linarith : 0 ≤ ζ + 2 * margin)
      nlinarith
  have hq : -1 ≤ a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50 := by
    have hh : 0 ≤ eps * (N + 8) := by positivity
    linarith
  have hvq := central_halo_cost hq hvd hh
  have herr : 0 ≤ countLoss + 12 * e + eps * (N + 8) := by positivity
  have hde := mul_le_mul_of_nonneg_right hd herr
  have hid : ((6 / 11) * a - 197 / 330 + (146 / 11) * e) +
      (5 / 33) * (-(4 / 25) + (a - 1 / 2) + mesh) + loss +
      d * (Exponent.R0 δ + countLoss) +
      d * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) =
      beta - 67 / 99 + Exponent.E δ beta d + (146 / 11) * e +
        d * (countLoss + 12 * e + eps * (N + 8)) + (5 / 33) * mesh + loss := by
    dsimp [δ]
    unfold Exponent.E Exponent.a Exponent.h Exponent.x Exponent.y Exponent.ell Exponent.slope Exponent.z0
    ring
  norm_num [Exponent.b] at hE
  linarith

/-- The two finite partitions are exact; summing the cell estimates incurs only
one logarithmic count of norm shells and the fixed number of detector cells. -/
theorem finite_central_band_sum {N : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N → Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ j P, P ∈ T j → P.val ∉ S) (W : Fin N → ℝ → ℂ) (Yp : Fin N → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e heightBase upper C exponent : ℝ)
    (idx grid : FreeRow → ℕ) (n m : ℕ)
    (hrows : ∀ u ∈ rows, u.val ≠ 1 ∧ rowNorm u ≤ upper)
    (hlabel : ∀ u ∈ rows, idx u ≤ n ∧ grid u ≤ m) (_hC : 0 ≤ C)
    (hcell : ∀ k ∈ smallDyadicIndices upper, ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (m + 1),
      ‖finiteCentralCubeRows S hS hmax η (cubeBinRows (rows ∩ dyadicRows 1 k) idx grid i j)
        T hT W Yp W0 W1 X Y Z e (fun _ => 51 / 100 + e * j)
        (fun _ => (3 * i + 1 : ℕ) * heightBase)‖ ≤ C * Z ^ exponent) :
    ‖finiteCentralCubeRows S hS hmax η rows T hT W Yp W0 W1 X Y Z e
      (fun u => 51 / 100 + e * grid u) (fun u => (3 * idx u + 1 : ℕ) * heightBase)‖ ≤
      (smallDyadicIndices upper).card * (n + 1 : ℕ) * (m + 1 : ℕ) * C * Z ^ exponent := by
  let F := fun R a H => finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H
  have hp : F rows (fun u => 51 / 100 + e * grid u) (fun u => (3 * idx u + 1 : ℕ) * heightBase) =
      ∑ k ∈ smallDyadicIndices upper,
        F (rows ∩ dyadicRows 1 k) (fun u => 51 / 100 + e * grid u)
          (fun u => (3 * idx u + 1 : ℕ) * heightBase) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows upper hrows _
  change ‖F rows _ _‖ ≤ _
  rw [hp]
  calc
    _ ≤ ∑ k ∈ smallDyadicIndices upper, (n + 1 : ℕ) * (m + 1 : ℕ) * (C * Z ^ exponent) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hb := finiteCentralCubeRows_bin_partition S hS hmax η (rows ∩ dyadicRows 1 k)
        T hT W Yp W0 W1 X Y Z e heightBase idx grid n m
        (fun u hu => hlabel u (Finset.mem_inter.mp hu).1)
      change ‖finiteCentralCubeRows _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _‖ ≤ _
      rw [hb]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), C * Z ^ exponent := by
          apply Finset.sum_le_sum
          intro i hi
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => hcell k hk i hi j hj))
        _ = _ := by simp; ring
    _ = _ := by simp; ring

lemma finite_central_band_power {N : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N → Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ j P, P ∈ T j → P.val ∉ S) (W : Fin N → ℝ → ℂ) (Yp : Fin N → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e heightBase vmax C exponent dyadLoss Cd : ℝ)
    (idx grid : FreeRow → ℕ) (n m : ℕ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hrows : ∀ u ∈ rows, u.val ≠ 1 ∧ rowNorm u ≤ Z ^ vmax)
    (hlabel : ∀ u ∈ rows, idx u ≤ n ∧ grid u ≤ m)
    (hdyad : ((smallDyadicIndices (Z ^ vmax)).card : ℝ) ≤ Cd * Z ^ dyadLoss)
    (hcell : ∀ k ∈ smallDyadicIndices (Z ^ vmax), ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (m + 1),
      ‖finiteCentralCubeRows S hS hmax η (cubeBinRows (rows ∩ dyadicRows 1 k) idx grid i j)
        T hT W Yp W0 W1 X Y Z e (fun _ => 51 / 100 + e * j)
        (fun _ => (3 * i + 1 : ℕ) * heightBase)‖ ≤ C * Z ^ exponent) :
    ‖finiteCentralCubeRows S hS hmax η rows T hT W Yp W0 W1 X Y Z e
      (fun u => 51 / 100 + e * grid u) (fun u => (3 * idx u + 1 : ℕ) * heightBase)‖ ≤
      Cd * (n + 1 : ℕ) * (m + 1 : ℕ) * C * Z ^ (exponent + dyadLoss) := by
  apply (finite_central_band_sum S hS hmax η rows T hT W Yp W0 W1 X Y Z e heightBase
    (Z ^ vmax) C exponent idx grid n m hrows hlabel hC hcell).trans
  calc
    _ ≤ (Cd * Z ^ dyadLoss) * (n + 1 : ℕ) * (m + 1 : ℕ) * C * Z ^ exponent := by
      gcongr
    _ = _ := by rw [Real.rpow_add hZ]; ring

section ActualBand
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
local instance : Fintype (Sum Bool (RayQuotient.Characters M H)) := Fintype.ofFinite _
open ProbeRaySlots

/-- The actual inverse and zero-slot fourth moments are joined before choosing
height scales. Only the displayed arithmetic loss bounds remain as inputs. -/
theorem actual_finite_central_band
    (N : ℕ) (e eps c b A R dmin dmax rmin ε κ cost mesh δlo margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps)
    (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hδlo : 0 < δlo) (hmargin : 0 < margin)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh)
    (hcountbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (hepsBudget : eps * (N + 8) ≤ 1)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal) (hcore : sourceFixedCore S ≤ M)
    (W : Fin N → ℝ → ℂ) (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hWB : ∀ j t, ‖W j t‖ ≤ A)
    (ell : Fin N → ℝ) (hello : ∀ j, dmax * rmin ≤ ell j)
    (hellhi : ∀ j, ell j ≤ dmin * R) (hellsum : ∑ j, ell j = (5 / 33 : ℝ))
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (Φ : SchwartzMap ℝ ℂ) (radial δ plainLoss εm : ℝ)
    (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Iic radial)
    (hΦp : ∀ x, 0 ≤ (Φ x).re) (hΦ1 : ∀ x ∈ Icc (0 : ℝ) 1, Φ x = 1)
    (hradial : 0 < radial) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hplainLoss : 0 < plainLoss) (hplainBudget : δ + plainLoss ≤ εm) (hεm : 0 < εm)
    (ζ logLoss heightLoss dyadLoss p : ℝ) (hζ : 0 ≤ ζ)
    (hvmax : (25 / 33 : ℝ) + ζ ≤ 1) (hdlow : dmin ≤ δlo)
    (hdtop : (25 / 33 : ℝ) + ζ + 2 * margin ≤ dmax)
    (hlogLoss : 0 < logLoss) (hdyadLoss : 0 < dyadLoss)
    (hmain : (20 / 99 : ℝ) + 2 * ζ + 6 * margin + (146 / 11) * e +
      ((25 / 33 : ℝ) + ζ + 2 * margin) * (6 * ε + εm + 12 * e + eps * (N + 8)) +
      (5 / 33) * mesh + loss + logLoss + heightLoss ≤ p)
    (hfloor : (137 / 825 : ℝ) + (67 / 100) * ζ + (146 / 11) * e +
      ((25 / 33 : ℝ) + ζ) * (12 * e + eps * (N + 8)) + (5 / 33) * mesh + loss ≤ p) :
    ∃ inverseOrder plainOrder : ℕ, ∀ τ q : ℝ,
      0 < τ → 0 ≤ q → τ < q → q * (inverseOrder + plainOrder + 1) ≤ heightLoss →
      τ < dmin / 2 → 4 * τ < dmin * cost → τ * (2 + 4 * eps) < loss →
      ∀ n m : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ δlo ≤ rowNorm u ∧ rowNorm u ≤ Z ^ ((25 / 33 : ℝ) + ζ)) →
      ∀ idx grid : FreeRow → ℕ, (∀ u ∈ rows, idx u ≤ n ∧ grid u ≤ m) →
      (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (idx u + 1 : ℕ) * Z ^ τ) < 51 / 100 + e * grid u + 2 * e) →
      (∀ u ∈ rows, 51 / 100 + e * grid u ≤
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * idx u : ℕ) * Z ^ τ)) →
      let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j => pool (RayQuotient.identityClass M H) S c b (Yp j)
      (∀ j l, j ≠ l → Disjoint (T j) (T l)) →
      ‖finiteCentralCubeRows S hS hmax η rows T (sourcePoolOutside M H S N c b Yp) W Yp W0 W1
        (Z ^ (13 / 33 : ℝ)) (Z ^ (15 / 33 : ℝ)) Z e
        (fun u => 51 / 100 + e * grid u) (fun u => (3 * idx u + 1 : ℕ) * Z ^ τ)‖ ≤
        C * Z ^ (p + dyadLoss) := by
  have hdmax : 0 < dmax := hdmin.trans_le hdRange
  obtain ⟨inverseOrder, hcount⟩ := actual_source_count_uniform_order M H hH S hS hmax
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    dmin dmax δlo ε e κ cost margin εm hdmin hdRange hδlo hε hε1 he he1 hκ hκ1 hcost hmargin hεm hcountbudget
  obtain ⟨plainOrder, Cp, hCp, hplain⟩ := source_plain M H hH S hS hmax hcore
    Φ radial dmin δlo ε δ plainLoss εm hΦs hΦp hΦ1 hradial hdmin hδlo hε1
    hδ hδ1 hplainLoss hplainBudget
  refine ⟨inverseOrder, plainOrder, ?_⟩
  intro τ q hτ hq hτq horder hτzero hτheight hloss n m
  obtain ⟨D, hD, hcentral⟩ := actual_source_central_cube_with_shell_bound M H hH N n
    e eps c b A R dmin dmax rmin τ ε κ cost mesh δlo margin loss
    he he1 heps hc hcb hA hR hdmin hdmax.le hrmin hτ hε hκ hcost hmesh hδlo
    hbudget hgap hmargin (by linarith only [hτheight, hτ]) hloss S hS hfirst hmax W hWs hW hWB ell hello hellhi hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨K, hK, hoverhead⟩ := count_overhead_eventually
    (Label := Sum Bool (RayQuotient.Characters M H)) inverseOrder plainOrder dmin dmax q logLoss
    hdmin hdmax hq hlogLoss
  obtain ⟨Cd, hCd, hdyad⟩ := canonical_dyad_cost dyadLoss hdyadLoss
  intro η
  obtain ⟨Ci, hCi, hcountZ⟩ := hcount n τ hτ hτzero hτheight η
  let Ccell := D * max 1024 (4 * K * (Ci + 192 * Cp)) * (η.modulus.absNorm : ℝ) ^ (2 * eps)
  have hCcell : 0 < Ccell := by
    dsimp [Ccell]
    have hm : 0 < max 1024 (4 * K * (Ci + 192 * Cp)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact mul_pos (mul_pos hD hm) (Real.rpow_pos_of_pos (zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)) _)
  refine ⟨Cd * (n + 1 : ℕ) * (m + 1 : ℕ) * Ccell, by positivity, ?_⟩
  filter_upwards [hcentral η, hcountZ, hplain η, hoverhead,
    source_dyad_geometry_eventually dmin dmax margin ((25 / 33 : ℝ) + ζ) δlo hdmin hdlow hmargin hdtop,
    source_count_frequency_eventually n dmax τ q hdmax hτ hτq,
    eventually_gt_atTop (1 : ℝ)] with Z hcZ hcountZ hplainZ hoverheadZ hgeoZ hfreqZ hZ
  intro rows hrows idx grid hlabels hnext hcurrent
  dsimp only
  intro hdis
  let retained := rows.filter (fun u => (calibrationForSet S hmax).residueMonoid u.val ≠ 0)
  have hsub : retained ⊆ rows := Finset.filter_subset _ _
  let Yp : Fin N → ℝ := fun j => Z ^ (ell j)
  let T : Fin N → Finset ProbePhysical.PrimeIdeal := fun j => pool (RayQuotient.identityClass M H) S c b (Yp j)
  let hT := sourcePoolOutside M H S N c b Yp
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hcell (k : ℕ) (hk : k ∈ smallDyadicIndices (Z ^ ((25 / 33 : ℝ) + ζ)))
      (i : ℕ) (hi : i ∈ Finset.range (n + 1)) (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      ‖finiteCentralCubeRows S hS hmax η (cubeBinRows (retained ∩ dyadicRows 1 k) idx grid i j)
        T hT W Yp W0 W1 (Z ^ (13 / 33 : ℝ)) (Z ^ (15 / 33 : ℝ)) Z e
        (fun _ => 51 / 100 + e * j) (fun _ => (3 * i + 1 : ℕ) * Z ^ τ)‖ ≤ Ccell * Z ^ p := by
    let cells := cubeBinRows (retained ∩ dyadicRows 1 k) idx grid i j
    have hshellsub : cells ⊆ retained ∩ dyadicRows 1 k := Finset.filter_subset _ _
    have hsubR : cells ⊆ rows := hshellsub.trans (Finset.inter_subset_left.trans hsub)
    have hical : ∀ u ∈ cells, (calibrationForSet S hmax).residueMonoid u.val ≠ 0 := by
      intro u hu
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hshellsub hu)).1).2
    have hnext' : ∀ u ∈ cells, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < 51 / 100 + e * j + 2 * e := by
      intro u hu
      have hb := (mem_cubeBinRows _ idx grid i j u).mp hu
      simpa only [hb.2.1, hb.2.2] using hnext u (hsubR hu)
    by_cases hne : cells.Nonempty
    · have hg := hgeoZ retained (fun u hu => hrows u (hsub hu)) k (hne.mono hshellsub)
      let v := sourceDyadExponent Z k
      let d := sourceDyadConductor Z margin k
      let a : ℝ := 51 / 100 + e * j
      have ha : 51 / 100 ≤ a := by
        dsimp [a]
        exact le_add_of_nonneg_right (mul_nonneg he.le (Nat.cast_nonneg j))
      have ha12 : a ≤ 11 / 12 := by
        obtain ⟨u, hu⟩ := hne
        have hm := (mem_cubeBinRows _ idx grid i j u).mp hu
        have hb := hcurrent u (hsubR hu)
        rw [hm.2.1, hm.2.2] at hb
        exact hb.trans (detector_maximum_le_eleven_twelfths _ _)
      have hcur : ∀ u ∈ cells, a ≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3 * i : ℕ) * Z ^ τ) := by
        intro u hu
        have hm := (mem_cubeBinRows _ idx grid i j u).mp hu
        simpa only [hm.2.1, hm.2.2] using hcurrent u (hsubR hu)
      have hnorm := fun u hu => hg.2.2.2.2.1 u (hshellsub hu)
      let rowPower := a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50
      have hrowPower : rowPower ≤ 2 := by
        dsimp [rowPower]
        linarith only [ha12, he1, hepsBudget]
      have hcentralRows : ∀ u ∈ cells, u.val ≠ 1 ∧ Z ^ δlo ≤ rowNorm u ∧
          (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - margin) := by
        intro u hu
        exact ⟨(hrows u (hsubR hu)).1, (hrows u (hsubR hu)).2.1, hical u hu,
          hg.2.2.2.2.2 u (hshellsub hu)⟩
      change ‖finiteCentralCubeRows S hS hmax η cells T hT W Yp W0 W1
        (Z ^ (13 / 33 : ℝ)) (Z ^ (15 / 33 : ℝ)) Z e
        (fun _ => a) (fun _ => (3 * i + 1 : ℕ) * Z ^ τ)‖ ≤ Ccell * Z ^ p
      by_cases hjzero : j = 0
      · have haeq : a = 51 / 100 := by simp [a, hjzero]
        have hs := row_shell_crude_sum hZ.le hg.1 hrowPower cells hnorm
        have hb := hcZ d hg.2.2.1 hg.2.2.2.1 cells hcentralRows a i
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) ha (by linarith only [ha12]) hnext' hdis
          1024 (v * (1 + rowPower)) (by norm_num) hs
        have hf := floor_exponent_with_buffer (N := N) (mesh := mesh) (loss := loss) hg.2.1 he.le heps.le
        rw [haeq] at hb ⊢
        have hexp : ((6 / 11) * (51 / 100) - 197 / 330 + (146 / 11) * e) +
            (5 / 33) * (-(4 / 25) + (51 / 100 - 1 / 2) + mesh) + loss + v * (1 + rowPower) ≤ p := by
          dsimp [rowPower]
          rw [haeq]
          convert hf.trans hfloor using 1
          dsimp [v]
          ring
        apply hb.trans
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_left _ _) hD.le) (by positivity)
        · exact Real.rpow_le_rpow_of_exponent_le hZ.le hexp
        · positivity
        · exact hCcell.le
      · have haj : 51 / 100 < a := by
          have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjzero
          dsimp [a]
          have hx := mul_pos he hjpos
          linarith only [hx]
        have hrowsBand : cells ⊆ rowBand (Z ^ δlo) (2 * Z ^ ((25 / 33 : ℝ) + ζ)) := by
          intro u hu
          exact mem_rowBand.mpr ⟨(hrows u (hsubR hu)).1, (hrows u (hsubR hu)).2.1,
            lt_of_le_of_lt (hrows u (hsubR hu)).2.2 (by nlinarith only [Real.rpow_pos_of_pos hZp ((25 / 33 : ℝ) + ζ)])⟩
        have hplain' := hplainZ d hg.2.2.1 cells
          (fun u hu => (hrows u (hsubR hu)).2.1)
          (fun u hu => (hcentralRows u hu).2.2.2 |>.trans
            (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hmargin]))) (Z ^ q) (by positivity)
        have hc := hcountZ d hg.2.2.1 hg.2.2.2.1 (2 * Z ^ ((25 / 33 : ℝ) + ζ)) a (Z ^ q)
          (Cp * (1 + Z ^ q) ^ plainOrder) cells hrowsBand hical
          (fun u hu => (hcentralRows u hu).2.2.2) i
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) haj (by linarith only [ha12]) hnext' hcur
          (by positivity) (by positivity) (hfreqZ d hg.2.2.2.1 i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hplain'
        have ho := hoverheadZ d hg.2.2.1 hg.2.2.2.1 Ci Cp
          (Exponent.R0 (2 * a - 1) + 6 * ε + εm) hCi.le hCp.le
        have hc' : (cells.card : ℝ) ≤ K * (Ci + 192 * Cp) *
            Z ^ (logLoss + q * (inverseOrder + plainOrder + 1) + d * (Exponent.R0 (2 * a - 1) + 6 * ε + εm)) :=
          hc.trans ho
        have hw := row_shell_sum hZp hrowPower cells hnorm hc'
        have hb := hcZ d hg.2.2.1 hg.2.2.2.1 cells hcentralRows a i
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) ha (by linarith only [ha12]) hnext' hdis
          (4 * K * (Ci + 192 * Cp))
          (logLoss + q * (inverseOrder + plainOrder + 1) + d * (Exponent.R0 (2 * a - 1) + 6 * ε + εm) + v * rowPower)
          (by positivity) (by simpa only [mul_assoc] using hw)
        have hx := central_exponent_with_halo (N := N) (beta := HeckeZeroSupremum.beta)
          (d := d) (v := v) (loss := loss) (mesh := mesh)
          (countLoss := 6 * ε + εm) (overhead := logLoss + q * (inverseOrder + plainOrder + 1))
          ha (by linarith only [ha12]) hζ hmargin.le he.le heps.le (by positivity)
          (by dsimp [d, sourceDyadConductor]; linarith only [hg.2.1])
          (by dsimp [d, v, sourceDyadConductor]; linarith only [hmargin]) (by dsimp [d, v, sourceDyadConductor]; linarith only [hmargin])
        have hexp : ((6 / 11) * a - 197 / 330 + (146 / 11) * e) +
            (5 / 33) * (-(4 / 25) + (a - 1 / 2) + mesh) + loss +
            (logLoss + q * (inverseOrder + plainOrder + 1) + d * (Exponent.R0 (2 * a - 1) + 6 * ε + εm) + v * rowPower) ≤ p := by
          dsimp [rowPower]
          linarith only [hx, hmain, horder]
        apply hb.trans
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hD.le) (by positivity)
        · exact Real.rpow_le_rpow_of_exponent_le hZ.le hexp
        · positivity
        · exact hCcell.le
    · change ‖finiteCentralCubeRows S hS hmax η cells T hT W Yp W0 W1 _ _ _ _ _ _‖ ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [finiteCentralCubeRows, Finset.sum_empty, norm_zero]
      exact mul_nonneg hCcell.le (Real.rpow_nonneg hZp.le _)
  have hb := finite_central_band_power S hS hmax η retained T hT W Yp W0 W1
    (Z ^ (13 / 33 : ℝ)) (Z ^ (15 / 33 : ℝ)) Z e (Z ^ τ) ((25 / 33 : ℝ) + ζ)
    Ccell p dyadLoss Cd idx grid n m hZp hCcell.le
    (fun u hu => ⟨(hrows u (hsub hu)).1, (hrows u (hsub hu)).2.2⟩)
    (fun u hu => hlabels u (hsub hu)) (hdyad Z _ hZ.le hvmax) hcell
  rw [finiteCentralCubeRows_filter_calibration S hS hmax η rows T hT W Yp W0 W1
    (Z ^ (13 / 33 : ℝ)) (Z ^ (15 / 33 : ℝ)) Z e] at hb
  exact hb

end ActualBand

open CommonParameters

/-- The common source and common losses give a complete central band bound;
only the cube height is chosen after the two uniform polynomial orders. -/
theorem source_data_central_band_bound
    (hβ : Exponent.b < HeckeZeroSupremum.beta)
    (F : SourceData (contourE HeckeZeroSupremum.beta)) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ n : ℕ, ∀ η : Character,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ idx grid : FreeRow → ℕ, SourceBins F η Z τ n idx grid →
      ‖sourceCentralBand F η Z (smallLoss HeckeZeroSupremum.beta) τ idx grid‖ ≤
        C * Z ^ ((20 / 99 : ℝ) + 11 * smallLoss HeckeZeroSupremum.beta) := by
  let β := HeckeZeroSupremum.beta
  let u := smallLoss β
  let e := contourE β
  let eps := arithmeticEpsilon β
  let ε := witnessEpsilon β
  have hu : 0 < u := smallLoss_pos hβ
  rcases fixed_guards hβ with
    ⟨he, he1, heps, hε, hε1, hucap, hgeom, hcount, hbudget, hgap,
      _hsmall, _hprincipal, _hwindow, hepsBudget⟩
  have hcore : sourceFixedCore F.S ≤ F.modulus := inf_le_left
  obtain ⟨radial, hradial, hΦs⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let Φ := CenteredMomentDetectorPlainFiberSource.radialMajorant
  let WC : Fin 1 → ℝ → ℂ := fun _ y => (F.w y : ℂ)
  have hWCs : ∀ j, Function.support (WC j) ⊆ Ioo (1 : ℝ) 2 := by
    intro j y hy
    apply F.support
    change F.w y ≠ 0
    intro hy0
    exact (Function.mem_support.mp hy) (by simp [WC, hy0])
  have hWC : ∀ j, ContDiff ℝ ∞ (WC j) :=
    fun _ => Complex.ofRealCLM.contDiff.comp F.smooth
  have hWCB : ∀ j y, ‖WC j y‖ ≤ (1 : ℝ) := by
    intro j y
    simpa only [WC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.bounded y).1]
      using (F.bounded y).2
  have hmain : (20 / 99 : ℝ) + 2 * u + 6 * eps + (146 / 11) * e +
      ((25 / 33 : ℝ) + u + 2 * eps) * (6 * ε + ε + 12 * e + eps * ((1 : ℕ) + 8)) +
      (5 / 33) * u + u + u + u / 8 ≤ (20 / 99 : ℝ) + 10 * u := by
    have hx := central_loss_bound hβ
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
    dsimp [u, e, eps, ε, β] at *
    linarith only [hx, hu]
  have hfloor : (137 / 825 : ℝ) + (67 / 100) * u + (146 / 11) * e +
      ((25 / 33 : ℝ) + u) * (12 * e + eps * ((1 : ℕ) + 8)) + (5 / 33) * u + u ≤
      (20 / 99 : ℝ) + 10 * u := by
    have hx := floor_loss_bound hβ
    dsimp [u, e, eps, β]
    nlinarith only [hx]
  obtain ⟨inverseOrder, plainOrder, hband⟩ := actual_finite_central_band
    F.modulus ⊤ (by exact le_top) 1
    e eps 1 2 1 100 (1 / 400) (4 / 5) (1 / 10) ε e eps u (1 / 200) eps u
    he he1 heps (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hε hε1 he (by linarith only [he1])
    heps.le hu (by norm_num) heps hbudget hgap
    (by dsimp [e, eps, ε, β]; linarith only [hcount])
    (by dsimp [eps, β]; norm_num; linarith only [hepsBudget])
    F.S F.exclusions F.first F.maximal hcore WC hWCs hWC hWCB
    (fun (_ : Fin 1) => (5 / 33 : ℝ)) (by intro j; norm_num) (by intro j; norm_num) (by simp)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.w F.smooth F.compact F.positive_support (fun y => (F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y => (F.bounded y).2)
    Φ radial (ε / 4) (ε / 4) ε hΦs
    CenteredMomentDetectorPlainFiberSource.radialMajorant_nonneg
    CenteredMomentDetectorPlainFiberSource.radialMajorant_one hradial
    (by positivity) (by linarith only [hε1]) (by positivity) (by linarith only [hε]) hε
    u u (u / 8) u ((20 / 99 : ℝ) + 10 * u) hu.le
    (by linarith only [hucap]) (by norm_num) hgeom hu hu hmain hfloor
  obtain ⟨q, τ, hq, hτ, hτq, horder, _hqcap, hτzero, hτheight, hloss⟩ :=
    exists_height_choices (N := (inverseOrder + plainOrder + 1 : ℕ)) hu heps.le heps (by norm_num : (0 : ℝ) < 1 / 400)
      (by positivity)
  refine ⟨τ, hτ, ?_⟩
  intro n η
  obtain ⟨C, hC, hbound⟩ := hband τ q hτ hq.le hτq (by simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using horder) hτzero hτheight hloss
    n ⌊(49 / 100 : ℝ) / e⌋₊ η
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with Z hz
  intro idx grid hbins
  have hmaxeq (row : FreeRow) (height : ℝ) :
      @detectorMaximum (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fintype.ofFinite _)
        (sourceDetectorFamily F.S F.exclusions.prime η row (rayCubeFamily F.modulus ⊤ (by exact le_top) row)) height =
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η row
        (rayCubeFamily F.modulus ⊤ (by exact le_top) row)) height :=
    congrArg (fun inst : Fintype (Sum Bool (RayQuotient.Characters F.modulus ⊤)) =>
      @detectorMaximum _ inst _ height) (Subsingleton.elim _ _)
  have hb := hz (rowBand (Z ^ (1 / 200 : ℝ)) (Z ^ ((25 / 33 : ℝ) + u)))
    (fun row hrow => ⟨(mem_rowBand.mp hrow).1, (mem_rowBand.mp hrow).2.1,
      (mem_rowBand.mp hrow).2.2.le⟩) idx grid
    (fun row _ => ⟨(hbins.1 row).2.1, (hbins.1 row).2.2.1⟩)
    (fun row _ => by
      rw [hmaxeq]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hbins.2 row).2.2.2.2.1)
    (fun row _ => by rw [hmaxeq]; exact (hbins.2 row).2.2.1)
    (fun j l hne => (hne (Subsingleton.elim j l)).elim)
  change ‖sourceCentralBand F η Z u τ idx grid‖ ≤ C * Z ^ (((20 / 99 : ℝ) + 10 * u) + u) at hb
  rw [show ((20 / 99 : ℝ) + 10 * u) + u = (20 / 99 : ℝ) + 11 * u by ring] at hb
  exact hb

end
end ZetaZeroFree.Analytic.Probe
