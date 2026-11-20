/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceContinuum
import Candidate.C092.Contact

/-!
# Actual source-witness and radius continuations

The actual finite certificate pays the low response and every alternative
of one simultaneous inverse/ordinary witness pair at every positive radius.
The proof retains the lower tangent, real fifth-root curve, native transitions,
ratio-restored ordinary caps below H and true native fourth above one. A coarse
3/4 capacity-loss bound replaces P.2's .61 derivative calculation while staying
strictly inside its original 5/6 price allowance. Analytic admission of the
original marked energy, the high-response SN9 supplier and the o(1) witness
collars remain separate.
-/

set_option autoImplicit false
namespace QRH.Cycle092.Source
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate

/-- The actual source gain with the genuine unmarked continuation above Y. -/
def continuedGain (m : ℝ) : ℝ := if m ≤ sourceY then sourceGain m else 0

/-- The half-length correction remains monotone through the favorable native
jump from F(Y) < 0 to zero. No upper bound on the later witness is required. -/
theorem continued_halfGain_mono {m₀ m₁ : ℝ}
    (hm₀ : sourceY0 ≤ m₀) (hm : m₀ ≤ m₁) :
    m₀/2+continuedGain m₀ ≤ m₁/2+continuedGain m₁ := by
  by_cases h₀ : m₀ ≤ sourceY
  · by_cases h₁ : m₁ ≤ sourceY
    · simpa only [continuedGain, ite_eq_left h₀, ite_eq_left h₁] using halfGain_mono hm₀ hm h₁
    · have hY : sourceY ≤ m₁ := (le_of_not_ge h₁)
      have hh := halfGain_mono hm₀ h₀ (le_refl sourceY)
      rw [source_native_value] at hh
      simp only [continuedGain, ite_eq_left h₀, ite_eq_right h₁]
      linarith
  · have h₁ : ¬m₁ ≤ sourceY := fun h => h₀ (hm.trans h)
    simp only [continuedGain, ite_eq_right h₀, ite_eq_right h₁]
    linarith

/-- P5 written at an arbitrary nonnegative radius, with its original positive
part and the actual witness debit. At H its constant term is exactly 2u. -/
def ordinaryPrice (y e ν V m : ℝ) : ℝ :=
  -ν*(V*m-y)+e*max 0 ((1-V)/2-(u : ℝ)+(V*m-y)/2+sourceGain y-V*continuedGain m)

/-- Every larger actual ordinary witness improves the literal ordinary price,
for every nonnegative radius and every zero band above the response. -/
theorem ordinaryPrice_antitone {y e ν V m₀ m₁ : ℝ}
    (he : 0 ≤ e) (hν : e ≤ ν) (hV : 0 ≤ V)
    (hm₀ : sourceY0 ≤ m₀) (hm : m₀ ≤ m₁) :
    ordinaryPrice y e ν V m₁ ≤ ordinaryPrice y e ν V m₀ := by
  have hg := continued_halfGain_mono hm₀ hm
  have hd : 0 ≤ V*(m₁-m₀) := mul_nonneg hV (sub_nonneg.mpr hm)
  have hgV := mul_le_mul_of_nonneg_left hg hV
  have hmax :
      max 0 ((1-V)/2-(u : ℝ)+(V*m₁-y)/2+sourceGain y-V*continuedGain m₁) ≤
      max 0 ((1-V)/2-(u : ℝ)+(V*m₀-y)/2+sourceGain y-V*continuedGain m₀)+V*(m₁-m₀) := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) hd
    · have hbase := le_max_right 0 ((1-V)/2-(u : ℝ)+(V*m₀-y)/2+sourceGain y-V*continuedGain m₀)
      nlinarith
  have hemax := mul_le_mul_of_nonneg_left hmax he
  have hde := mul_le_mul_of_nonneg_right hν hd
  unfold ordinaryPrice
  nlinarith

/-- The rational certificate's native gain agrees with the literal real gain. -/
theorem ordinaryGain_cast (m : ℚ) :
    (ordinaryGain m : ℝ) = continuedGain (m : ℝ) := by
  have hY : (Y : ℝ) = sourceY := by norm_num [Y, sourceY]
  by_cases hm : m ≤ Y
  · have hmR : (m : ℝ) ≤ sourceY := by rw [←hY]; exact_mod_cast hm
    simp only [ordinaryGain, ite_eq_left hm, continuedGain, ite_eq_left hmR]
    exact gain_cast m
  · have hmR : ¬(m : ℝ) ≤ sourceY := by
      rw [←hY]; exact_mod_cast hm
    simp only [ordinaryGain, ite_eq_right hm, Rat.cast_zero, continuedGain, ite_eq_right hmR]

/-- The checked band price is exactly P5 at H, with no scalar loss. -/
theorem ordinaryPrice_at_H (y e ν : ℝ) (c : Cutoff) :
    ordinaryPrice y e ν (H : ℝ) (c.ordinary : ℝ) = ordinaryCostWithBand y e ν c := by
  rw [ordinaryPrice, ←ordinaryGain_cast]
  unfold ordinaryCostWithBand
  have hconst : (1-(H : ℝ))/2-(u : ℝ) = 2*(u : ℝ) := by
    norm_num [H,u]
  rw [hconst]

/-- A checked ordinary cutoff pays every larger actual ordinary witness,
with precisely the same strict reserve. -/
theorem checked_ordinary_pays_larger {y e ν m : ℝ} (c : Cutoff)
    (he : 0 ≤ e) (hν : e ≤ ν)
    (hc : sourceY0 ≤ (c.ordinary : ℝ)) (hm : (c.ordinary : ℝ) ≤ m)
    (hpaid : PaidWithBand y e ν c) :
    ordinaryPrice y e ν (H : ℝ) m < (u-rho : ℚ) := by
  have h := ordinaryPrice_antitone (y := y) he hν
    (by norm_num [H,u] : (0 : ℝ) ≤ (H : ℝ)) hc hm
  rw [ordinaryPrice_at_H] at h
  exact h.trans_lt hpaid.2.2

/-- Absolute source capacity at the frozen retained cap n/H and the actual
ordinary witness m. Above Y the continued gain is exactly zero. -/
def frozenCapacity (n m : ℝ) : ℝ :=
  (1-n/(H : ℝ)-m)/2+continuedGain m

/-- P4/P5 price retaining the checked H cap while the actual radius increases. -/
def frozenOrdinaryPrice (n y e ν V m : ℝ) : ℝ :=
  -ν*(V*m-y)+e*max 0 (sourceWidth n y-(u : ℝ)-V*frozenCapacity n m)

/-- The frozen-cap price agrees exactly with the tested price at H. -/
theorem frozenOrdinaryPrice_at_H (n y e ν m : ℝ) :
    frozenOrdinaryPrice n y e ν (H : ℝ) m = ordinaryPrice y e ν (H : ℝ) m := by
  unfold frozenOrdinaryPrice ordinaryPrice frozenCapacity sourceWidth
  congr 2
  congr 1
  have hH : (H : ℝ) ≠ 0 := by norm_num [H,u]
  field_simp
  ring

/-- Every actual ordinary witness up to 1/2 has positive frozen capacity on
P1's ordered cap domain, also after switching to the native quota. -/
theorem frozenCapacity_positive {n y m : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (hm₀ : sourceY0 ≤ m) (hm₁ : m ≤ 1/2) :
    0 < frozenCapacity n m := by
  have hnY : n ≤ sourceRatio*sourceY :=
    hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
  have hH : (0 : ℝ) < (H : ℝ) := by norm_num [H,u]
  have hnHalf : n/(H : ℝ) < 1/2 := by
    apply (div_lt_iff₀ hH).2
    norm_num [sourceRatio,sourceY,H,u] at hnY ⊢
    linarith
  have hmpos : 0 < m := source_domain.1.trans_le hm₀
  unfold frozenCapacity continuedGain
  split_ifs with hmY
  · have hg := sourceGain_antitone hmY (le_refl sourceY)
    rw [source_native_value] at hg
    have hmSmall : m ≤ 243/625 := by simpa [sourceY] using hmY
    linarith
  · linarith

/-- At fixed H caps the true available absolute width increases with radius;
the original positive part therefore decreases as does the witness debit. -/
theorem frozenOrdinaryPrice_radius_antitone {n y e ν m V₀ V₁ : ℝ}
    (he : 0 ≤ e) (hν : 0 ≤ ν) (hm : 0 ≤ m)
    (hcap : 0 ≤ frozenCapacity n m) (hV : V₀ ≤ V₁) :
    frozenOrdinaryPrice n y e ν V₁ m ≤ frozenOrdinaryPrice n y e ν V₀ m := by
  have hwidth := mul_le_mul_of_nonneg_right hV hcap
  have hmax := max_le_max_left 0 (sub_le_sub_left hwidth (sourceWidth n y-(u : ℝ)))
  have hemax := mul_le_mul_of_nonneg_left hmax he
  have hdebit := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hV hm) hν
  unfold frozenOrdinaryPrice
  linarith

/-- The actual ordinary price for every larger witness and every V≥H is
paid by the existing scalar certificate, using the frozen checked cap.
The witness is still bounded by its genuine 1/2 endpoint. -/
theorem checked_ordinary_pays_larger_radius {n y e ν m V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν)
    (hc : sourceY0 ≤ (c.ordinary : ℝ)) (hm : (c.ordinary : ℝ) ≤ m)
    (hm₁ : m ≤ 1/2) (hV : (H : ℝ) ≤ V)
    (hpaid : PaidWithBand y e ν c) :
    frozenOrdinaryPrice n y e ν V m < (u-rho : ℚ) := by
  have hm₀ := hc.trans hm
  have hrad := frozenOrdinaryPrice_radius_antitone (y := y) he (he.trans hν)
    (source_domain.1.le.trans hm₀) (frozenCapacity_positive hy hn hm₀ hm₁).le hV
  rw [frozenOrdinaryPrice_at_H] at hrad
  exact hrad.trans_lt (checked_ordinary_pays_larger c he hν hc hm hpaid)

/-- The literal required excess allowance in P2. -/
def radialAllowance (V : ℝ) : ℝ := (u-rho : ℚ)+(5/6)*max 0 ((H : ℝ)-V)

/-- The native-fourth price remains strictly below P2 throughout its lower
radius sector, by the checked .98 edge and its smaller adverse slope. -/
theorem native_lower_radius_paid {V : ℝ} (hV : V ≤ 98/100) :
    (3/4 : ℝ)*max 0 ((1-V)/2+sourceGain sourceY0-(u : ℝ)) < radialAllowance V := by
  have hHV : 0 ≤ (H : ℝ)-V := by norm_num [H,u]; linarith
  have hgain : 0 < sourceGain sourceY0 := by
    norm_num [sourceGain,sourceY0,sourceY,sourceSeam,lowerGain,QRH.Cycle090.upperGain]
  have hbracket : 0 ≤ (1-V)/2+sourceGain sourceY0-(u : ℝ) := by
    norm_num [u]; linarith
  have hedge := native_radial_edge
  unfold radialAllowance
  rw [max_eq_right hHV, max_eq_right hbracket]
  norm_num [sourceU,sourceH,sourceRho,H,u,rho] at hedge ⊢
  linarith

/-- The two genuine unmarked fourths pay every radius below the .875 edge. -/
theorem unmarked_lower_radius_paid {V : ℝ} (hV : V ≤ 7/8) :
    (3/4 : ℝ)*(sourceWMax-(u : ℝ)) < radialAllowance V := by
  have hHV : 0 ≤ (H : ℝ)-V := by norm_num [H,u]; linarith
  have hedge := middle_radial_edge
  unfold radialAllowance
  rw [max_eq_right hHV]
  norm_num [sourceU,sourceH,sourceRho,H,u,rho] at hedge ⊢
  linarith

/-- The original pointwise core price pays the whole small-radius sector,
with the actual ordered lengths bounded by P1's domain. -/
theorem pointwise_lower_radius_paid {n y V : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y) (hV : V ≤ 2/25) :
    (3/4 : ℝ)*(n+y)+sourceWMax-(u : ℝ) < radialAllowance V := by
  have hlength : n+y ≤ (1+sourceRatio)*sourceY := by
    have hny := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    linarith
  have hHV : 0 ≤ (H : ℝ)-V := by norm_num [H,u]; linarith
  have hedge := small_radial_edge
  unfold radialAllowance
  rw [max_eq_right hHV]
  norm_num [sourceU,sourceH,sourceRho,H,u,rho] at hedge ⊢
  linarith

/-- Adding a quarter of the label makes each source branch increasing. -/
theorem upperQuarterGain_strictMono : StrictMonoOn
    (fun y : ℝ => y/4+QRH.Cycle090.upperGain y) (Set.Icc sourceSeam sourceY) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · unfold QRH.Cycle090.upperGain; fun_prop
  · intro y hy
    have hm : y ∈ Set.Icc sourceSeam sourceY := interior_subset hy
    have hd := ((hasDerivAt_id y).div_const 4).add (upperGain_hasDerivAt y)
    change HasDerivAt (fun z : ℝ => z/4+QRH.Cycle090.upperGain z)
      (1/4+upperGainSlope y) y at hd
    rw [hd.deriv]
    linarith [(upperGain_slope_bounds hm.1 hm.2).1]

theorem lowerQuarterGain_strictMono : StrictMonoOn
    (fun y : ℝ => y/4+lowerGain y) (Set.Icc sourceY0 sourceSeam) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · unfold lowerGain; fun_prop
  · intro y hy
    have hm : y ∈ Set.Icc sourceY0 sourceSeam := interior_subset hy
    have hd := ((hasDerivAt_id y).div_const 4).add (lowerGain_hasDerivAt y)
    change HasDerivAt (fun z : ℝ => z/4+lowerGain z) (1/4+lowerGainSlope y) y at hd
    rw [hd.deriv]
    linarith [(lowerGain_slope_bounds hm.1 hm.2).1]

/-- Exact global secant control, including the joined source seam. -/
theorem sourceGain_quarter_secant {w r : ℝ}
    (hw : sourceY0 ≤ w) (hwr : w ≤ r) (hr : r ≤ sourceY) :
    sourceGain w-sourceGain r ≤ (r-w)/4 := by
  have hq : w/4+sourceGain w ≤ r/4+sourceGain r := by
    by_cases hws : sourceSeam ≤ w
    · have hrs := hws.trans hwr
      simpa only [sourceGain,ite_eq_left hws,ite_eq_left hrs] using
        upperQuarterGain_strictMono.monotoneOn ⟨hws,hwr.trans hr⟩ ⟨hrs,hr⟩ hwr
    · by_cases hrs : sourceSeam ≤ r
      · have hl := lowerQuarterGain_strictMono.monotoneOn
          ⟨hw,le_of_not_ge hws⟩ ⟨source_domain.2.1.le,le_rfl⟩ (le_of_not_ge hws)
        have hu := upperQuarterGain_strictMono.monotoneOn
          ⟨le_rfl,source_domain.2.2.le⟩ ⟨hrs,hr⟩ hrs
        rw [source_seam_join] at hl
        simpa only [sourceGain,ite_eq_right hws,ite_eq_left hrs] using hl.trans hu
      · simpa only [sourceGain,ite_eq_right hws,ite_eq_right hrs] using
          lowerQuarterGain_strictMono.monotoneOn
            ⟨hw,le_of_not_ge hws⟩ ⟨hw.trans hwr,le_of_not_ge hrs⟩ hwr
  linarith

/-- A coarse bound leaves ample room in the radial 5/6 budget. -/
theorem sourceGain_le_cent {m : ℝ} (hm₀ : sourceY0 ≤ m) (hm₁ : m ≤ sourceY) :
    sourceGain m ≤ 1/100 := by
  have h := sourceGain_antitone hm₀ hm₁
  have hcorner : sourceGain sourceY0 < (1/100 : ℝ) := by
    norm_num [sourceGain,sourceY0,sourceY,sourceSeam,lowerGain,QRH.Cycle090.upperGain]
  linarith

/-- The actual ratio-restoring label below H. -/
def adjustedWitness (n m V : ℝ) : ℝ := max m (n/(sourceRatio*V))

/-- A conservative admitted substitute capacity: the gain is taken at the
larger ordinary witness label, hence below the actual reordered source gain.
At the native transition the true actual witness m is retained. -/
def lowerOrdinaryCapacity (n m V : ℝ) : ℝ :=
  let w := adjustedWitness n m V
  if w ≤ sourceY then (V-n-V*w)/2+V*sourceGain w else (V-n-V*m)/2

/-- At H the original ratio guard prevents any raising of the witness label. -/
theorem adjustedWitness_at_H {n y m : ℝ}
    (hn : n ≤ sourceRatio*y) (hm : y/(H : ℝ) ≤ m) :
    adjustedWitness n m (H : ℝ) = m := by
  apply max_eq_left
  have hRatioPos : 0 < sourceRatio := by norm_num [sourceRatio]
  have hH : 0 < (H : ℝ) := H_real_bounds.1
  apply (div_le_iff₀ (mul_pos hRatioPos hH)).2
  have hmy := (div_le_iff₀ hH).mp hm
  nlinarith

/-- The actual ratio-restored absolute witness length cannot exceed its
original absolute H-cap. -/
theorem adjustedWitness_absolute_bound {n y m V : ℝ}
    (hn : n ≤ sourceRatio*y) (hm : y/(H : ℝ) ≤ m)
    (hm₀ : 0 ≤ m) (hV₀ : 0 < V) (hV₁ : V ≤ (H : ℝ)) :
    V*adjustedWitness n m V ≤ (H : ℝ)*m := by
  have hRatioPos : 0 < sourceRatio := by norm_num [sourceRatio]
  have hH : 0 < (H : ℝ) := H_real_bounds.1
  have hmy := (div_le_iff₀ hH).mp hm
  have hnHm : n ≤ sourceRatio*((H : ℝ)*m) := by nlinarith
  have hbound : adjustedWitness n m V ≤ ((H : ℝ)*m)/V := by
    apply max_le
    · exact (le_div_iff₀ hV₀).2 (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hV₁ hm₀)
    · apply (div_le_iff₀ (mul_pos hRatioPos hV₀)).2
      have : (((H : ℝ)*m)/V)*(sourceRatio*V) = sourceRatio*((H : ℝ)*m) := by field_simp
      rw [this]
      exact hnHm
  simpa [mul_comm] using (le_div_iff₀ hV₀).mp hbound

/-- The conservative substitute capacity loses at most 3/4 per radius unit.
This weaker bound than P.2's .61 still fits its strict 5/6 allowance. -/
theorem lowerOrdinaryCapacity_loss {n y m V : ℝ}
    (hn : n ≤ sourceRatio*y) (hm : y/(H : ℝ) ≤ m)
    (hm₀ : sourceY0 ≤ m) (hm₁ : m ≤ 1/2)
    (hV₀ : 0 < V) (hV₁ : V ≤ (H : ℝ)) :
    (H : ℝ)*frozenCapacity n m-lowerOrdinaryCapacity n m V ≤
      (3/4)*((H : ℝ)-V) := by
  let w := adjustedWitness n m V
  have hw₀ : m ≤ w := le_max_left _ _
  have hδ : 0 ≤ (H : ℝ)-V := sub_nonneg.mpr hV₁
  have hmpos : 0 ≤ m := source_domain.1.le.trans hm₀
  have habs : V*w ≤ (H : ℝ)*m := adjustedWitness_absolute_bound hn hm hmpos hV₀ hV₁
  have hH : (H : ℝ) ≠ 0 := H_real_bounds.1.ne'
  have hid : (H : ℝ)*frozenCapacity n m =
      ((H : ℝ)-n-(H : ℝ)*m)/2+(H : ℝ)*continuedGain m := by
    unfold frozenCapacity
    field_simp
  rw [hid]
  unfold lowerOrdinaryCapacity
  change _ - (if w ≤ sourceY then (V-n-V*w)/2+V*sourceGain w else (V-n-V*m)/2) ≤ _
  by_cases hmY : m ≤ sourceY
  · rw [continuedGain,ite_eq_left hmY]
    by_cases hwY : w ≤ sourceY
    · rw [ite_eq_left hwY]
      have hsec := sourceGain_quarter_secant hm₀ hw₀ hwY
      have hsecV := mul_le_mul_of_nonneg_left hsec hV₀.le
      have hg := sourceGain_le_cent hm₀ hmY
      have hgδ := mul_le_mul_of_nonneg_left hg hδ
      have hmδ := mul_le_mul_of_nonneg_left hm₁ hδ
      nlinarith
    · rw [ite_eq_right hwY]
      have hratio : sourceY < n/(sourceRatio*V) := by
        rcases (lt_max_iff).mp (lt_of_not_ge hwY) with h | h
        · exact False.elim ((not_lt.mpr hmY) h)
        · exact h
      have hRatioPos : 0 < sourceRatio := by norm_num [sourceRatio]
      have hratio' := (lt_div_iff₀ (mul_pos hRatioPos hV₀)).mp hratio
      have hmy := (div_le_iff₀ H_real_bounds.1).mp hm
      have hVm : V*sourceY < (H : ℝ)*m := by nlinarith
      have hsec := sourceGain_quarter_secant hm₀ hmY (le_refl sourceY)
      rw [source_native_value] at hsec
      have hsecH := mul_le_mul_of_nonneg_left hsec H_real_bounds.1.le
      have hY : sourceY < 1 := by norm_num [sourceY]
      have hmδ := mul_nonneg hδ hmpos
      nlinarith
  · have hwY : ¬w ≤ sourceY := fun h => hmY (hw₀.trans h)
    rw [continuedGain,ite_eq_right hmY,ite_eq_right hwY]
    have hmδ := mul_nonneg hδ hmpos
    nlinarith

/-- The actual ordinary substitution price below H with ratio restoration. -/
def lowerOrdinaryPrice (n y e ν V m : ℝ) : ℝ :=
  -ν*(V*m-y)+e*max 0 (sourceWidth n y-(u : ℝ)-lowerOrdinaryCapacity n m V)

/-- The actual lower-radius substitute is paid by the checked H price. -/
theorem checked_ordinary_lower_radius {n y e ν m V : ℝ} (c : Cutoff)
    (hn : n ≤ sourceRatio*y) (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    (hc : y/(H : ℝ) ≤ (c.ordinary : ℝ)) (hc₀ : sourceY0 ≤ (c.ordinary : ℝ))
    (hm : (c.ordinary : ℝ) ≤ m) (hm₁ : m ≤ 1/2)
    (hV₀ : 0 < V) (hV₁ : V ≤ (H : ℝ)) (hp : PaidWithBand y e ν c) :
    lowerOrdinaryPrice n y e ν V m < radialAllowance V := by
  have hm₀ := hc₀.trans hm
  have hmpos : 0 ≤ m := source_domain.1.le.trans hm₀
  have hδ : 0 ≤ (H : ℝ)-V := sub_nonneg.mpr hV₁
  have hcap := lowerOrdinaryCapacity_loss hn (hc.trans hm) hm₀ hm₁ hV₀ hV₁
  have hmax : max 0 (sourceWidth n y-(u : ℝ)-lowerOrdinaryCapacity n m V) ≤
      max 0 (sourceWidth n y-(u : ℝ)-(H : ℝ)*frozenCapacity n m)+(3/4)*((H : ℝ)-V) := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) (mul_nonneg (by norm_num) hδ)
    · have hb := le_max_right 0 (sourceWidth n y-(u : ℝ)-(H : ℝ)*frozenCapacity n m)
      linarith
  have hmaxe := mul_le_mul_of_nonneg_left hmax he₀
  have hνm : ν*m ≤ 3/8 := by
    have hn := mul_le_mul_of_nonneg_left hm₁ (he₀.trans hν)
    nlinarith
  have hslope : ν*m+e*(3/4) ≤ 5/6 := by
    norm_num [responseUpper] at he₁
    nlinarith [he₁]
  have hscale := mul_le_mul_of_nonneg_left hslope hδ
  have hpH := checked_ordinary_pays_larger c he₀ hν hc₀ hm hp
  rw [←frozenOrdinaryPrice_at_H n] at hpH
  unfold lowerOrdinaryPrice frozenOrdinaryPrice at *
  unfold radialAllowance
  rw [max_eq_right hδ]
  nlinarith

/-- Full conservative ordinary price, using ratio-restored caps below H and
frozen H caps above H. Both prices keep the actual witness in its debit. -/
def actualOrdinaryPrice (n y e ν V m : ℝ) : ℝ :=
  if V ≤ (H : ℝ) then lowerOrdinaryPrice n y e ν V m else frozenOrdinaryPrice n y e ν V m

/-- A checked ordinary branch pays the full larger-witness alternative for
every radius at least .98, including genuine cap-ratio restoration below H. -/
theorem checked_ordinary_pays_all_radii {n y e ν m V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ)) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    (hc : y/(H : ℝ) ≤ (c.ordinary : ℝ)) (hc₀ : sourceY0 ≤ (c.ordinary : ℝ))
    (hm : (c.ordinary : ℝ) ≤ m) (hm₁ : m ≤ 1/2)
    (hV₀ : (98/100 : ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    actualOrdinaryPrice n y e ν V m < radialAllowance V := by
  unfold actualOrdinaryPrice
  split_ifs with hV
  · exact checked_ordinary_lower_radius c hn he₀ he₁ hν hν₁ hc hc₀ hm hm₁
      (by linarith) hV hp
  · have hh := checked_ordinary_pays_larger_radius c hy hn he₀ hν hc₀ hm hm₁
      (le_of_not_ge hV) hp
    unfold radialAllowance
    rw [max_eq_left (by linarith : (H : ℝ)-V ≤ 0)]
    simpa only [mul_zero,add_zero] using hh

/-- The tiny continued-cubic starting strip has nonpositive gain. -/
theorem sourceGain_native_strip_nonpos {s : ℝ}
    (hs₀ : sourceY ≤ s) (hs₁ : s ≤ sourceY/(H : ℝ)) : sourceGain s ≤ 0 := by
  have hseam := source_domain.2.2.le.trans hs₀
  rw [sourceGain,ite_eq_left hseam]
  have hd₀ : 0 ≤ s-sourceY := sub_nonneg.mpr hs₀
  have hd₁ : s-sourceY ≤ 1/100000 := by
    have hx : sourceY/(H : ℝ)-sourceY ≤ (1/100000 : ℝ) := by norm_num [sourceY,H,u]
    linarith
  have hsq : (sourceY-s)^2 ≤ (1/100000 : ℝ)^2 := by nlinarith
  have hcube := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (sourceY-s))
    (sub_nonpos.mpr hs₀)
  unfold QRH.Cycle090.upperGain
  nlinarith

/-- The native continuation improves the checked cubic on the starting strip. -/
theorem continuedGain_at_H_ge {y : ℝ} (hy : y ≤ sourceY) :
    sourceGain (y/(H : ℝ)) ≤ continuedGain (y/(H : ℝ)) := by
  by_cases hm : y/(H : ℝ) ≤ sourceY
  · simp [continuedGain,hm]
  · rw [continuedGain,ite_eq_right hm]
    exact sourceGain_native_strip_nonpos (le_of_not_ge hm)
      ((div_le_div_iff_of_pos_right H_real_bounds.1).2 hy)

/-- Low-response absolute source capacity, with the actual native continuation. -/
def lowAbsoluteCapacity (y V : ℝ) : ℝ := (V-y)/2+V*continuedGain (y/V)

/-- The true low-response capacity has at most the same coarse 3/4 radial
loss, through both the source seam and favorable native transition. -/
theorem lowAbsoluteCapacity_loss {y V : ℝ}
    (hy₀ : sourceY0 ≤ y) (_hy₁ : y ≤ sourceY)
    (hV₀ : 0 < V) (hV₁ : V ≤ (H : ℝ)) :
    lowAbsoluteCapacity y (H : ℝ)-lowAbsoluteCapacity y V ≤
      (3/4)*((H : ℝ)-V) := by
  let m := y/(H : ℝ)
  let w := y/V
  have hypos : 0 ≤ y := source_domain.1.le.trans hy₀
  have hm₀ : sourceY0 ≤ m := by
    have hyH : y ≤ y/(H : ℝ) := (le_div_iff₀ H_real_bounds.1).2
      (mul_le_of_le_one_right hypos H_real_bounds.2.le)
    exact hy₀.trans hyH
  have hmw : m ≤ w := by
    apply (div_le_div_iff₀ H_real_bounds.1 hV₀).2
    nlinarith
  have hmabs : (H : ℝ)*m = y := by dsimp [m]; field_simp [H_real_bounds.1.ne']
  have hwabs : V*w = y := by dsimp [w]; field_simp
  have hδ : 0 ≤ (H : ℝ)-V := sub_nonneg.mpr hV₁
  unfold lowAbsoluteCapacity
  change ((H : ℝ)-y)/2+(H : ℝ)*continuedGain m-
    ((V-y)/2+V*continuedGain w) ≤ _
  by_cases hmY : m ≤ sourceY
  · rw [continuedGain,ite_eq_left hmY]
    by_cases hwY : w ≤ sourceY
    · rw [continuedGain,ite_eq_left hwY]
      have hsec := sourceGain_quarter_secant hm₀ hmw hwY
      have hsecV := mul_le_mul_of_nonneg_left hsec hV₀.le
      have hg := sourceGain_le_cent hm₀ hmY
      have hgδ := mul_le_mul_of_nonneg_left hg hδ
      have hmHalf : m ≤ 1/2 := by
        have : sourceY < (1/2 : ℝ) := by norm_num [sourceY]
        linarith
      have hmδ := mul_le_mul_of_nonneg_left hmHalf hδ
      nlinarith
    · rw [continuedGain,ite_eq_right hwY]
      have hVm : V*sourceY < y := by
        have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hwY) hV₀
        linarith
      have hsec := sourceGain_quarter_secant hm₀ hmY (le_refl sourceY)
      rw [source_native_value] at hsec
      have hsecH := mul_le_mul_of_nonneg_left hsec H_real_bounds.1.le
      have hY : sourceY < 1 := by norm_num [sourceY]
      nlinarith [mul_nonneg hδ (show 0 ≤ 1-sourceY by linarith)]
  · have hwY : ¬w ≤ sourceY := fun h => hmY (hmw.trans h)
    rw [continuedGain,ite_eq_right hmY,continuedGain,ite_eq_right hwY]
    linarith

/-- Actual low-response price below H, with its original positive part. -/
def lowRadialPrice (y e V : ℝ) : ℝ :=
  e*max 0 ((1-V)/2-(u : ℝ)+sourceGain y-V*continuedGain (y/V))

/-- At H the actual native starting strip can only improve the checked price. -/
theorem lowRadialPrice_at_H_le {y e : ℝ} (hy : y ≤ sourceY) (he : 0 ≤ e) :
    lowRadialPrice y e (H : ℝ) ≤ e*max 0 (lowBracketAt y) := by
  have hg := mul_le_mul_of_nonneg_left (continuedGain_at_H_ge hy) H_real_bounds.1.le
  have hconst : (1-(H : ℝ))/2-(u : ℝ) = 2*(u : ℝ) := by norm_num [H,u]
  unfold lowRadialPrice lowBracketAt
  rw [hconst]
  exact mul_le_mul_of_nonneg_left (max_le_max_left 0 (by linarith)) he

/-- The checked low response pays the true source at every smaller near-H
radius; no perspective-derivative bound is assumed. -/
theorem checked_low_lower_radius {y e V : ℝ}
    (hy₀ : sourceY0 ≤ y) (hy₁ : y ≤ sourceY)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hV₀ : 0 < V) (hV₁ : V ≤ (H : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ)) :
    lowRadialPrice y e V < radialAllowance V := by
  have hδ : 0 ≤ (H : ℝ)-V := sub_nonneg.mpr hV₁
  have hcap := lowAbsoluteCapacity_loss hy₀ hy₁ hV₀ hV₁
  have hmax : max 0 ((1-V)/2-(u : ℝ)+sourceGain y-V*continuedGain (y/V)) ≤
      max 0 ((1-(H : ℝ))/2-(u : ℝ)+sourceGain y-(H : ℝ)*continuedGain (y/(H : ℝ)))+
        (3/4)*((H : ℝ)-V) := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) (mul_nonneg (by norm_num) hδ)
    · have hb := le_max_right 0 ((1-(H : ℝ))/2-(u : ℝ)+sourceGain y-
        (H : ℝ)*continuedGain (y/(H : ℝ)))
      unfold lowAbsoluteCapacity at hcap
      linarith
  have hmaxe := mul_le_mul_of_nonneg_left hmax he₀
  have hpH := (lowRadialPrice_at_H_le hy₁ he₀).trans_lt hp
  have hslope : e*(3/4) ≤ 5/6 := by norm_num [responseUpper] at he₁; linarith
  have hscale := mul_le_mul_of_nonneg_left hslope hδ
  unfold lowRadialPrice at *
  unfold radialAllowance
  rw [max_eq_right hδ]
  nlinarith

/-- The checked H pair is frozen for larger-radius low response. -/
def frozenLowCapacity (n y : ℝ) : ℝ :=
  (1-n/(H : ℝ)-y/(H : ℝ))/2+continuedGain (y/(H : ℝ))

theorem continuedGain_lower_bound (m : ℝ) : -(1/10000000 : ℝ) ≤ continuedGain m := by
  unfold continuedGain
  split_ifs with hm
  · have h := sourceGain_antitone hm (le_refl sourceY)
    rw [source_native_value] at h
    exact h
  · norm_num

theorem frozenLowCapacity_positive {n y : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y) : 0 < frozenLowCapacity n y := by
  have hsum : n+y ≤ (1+sourceRatio)*sourceY := by
    have hny := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    linarith
  have hg := continuedGain_lower_bound (y/(H : ℝ))
  have hquot := (div_le_div_iff_of_pos_right H_real_bounds.1).2 hsum
  unfold frozenLowCapacity
  have hsumdiv : n/(H : ℝ)+y/(H : ℝ) = (n+y)/(H : ℝ) := by ring
  rw [←hsumdiv] at hquot
  norm_num [sourceRatio,sourceY,H,u] at hquot
  norm_num [H,u] at hg ⊢
  linarith

/-- Low-response actual price on both sides of H. -/
def actualLowPrice (n y e V : ℝ) : ℝ :=
  if V ≤ (H : ℝ) then lowRadialPrice y e V
  else e*max 0 (sourceWidth n y-(u : ℝ)-V*frozenLowCapacity n y)

/-- A checked low response pays every radius at least .98 with the actual
source/native split below H and the frozen whole H pair above it. -/
theorem checked_low_pays_all_radii {n y e V : ℝ}
    (hy₀ : sourceY0 ≤ y) (hy₁ : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hV₀ : (98/100 : ℝ) ≤ V)
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ)) :
    actualLowPrice n y e V < radialAllowance V := by
  unfold actualLowPrice
  split_ifs with hV
  · exact checked_low_lower_radius hy₀ hy₁ he₀ he₁ (by linarith) hV hp
  · have hcap := frozenLowCapacity_positive hy₁ hn
    have hwidth := mul_le_mul_of_nonneg_right (le_of_not_ge hV) hcap.le
    have hmax := mul_le_mul_of_nonneg_left (max_le_max_left 0
      (sub_le_sub_left hwidth (sourceWidth n y-(u : ℝ)))) he₀
    have hid : e*max 0 (sourceWidth n y-(u : ℝ)-(H : ℝ)*frozenLowCapacity n y) =
        lowRadialPrice y e (H : ℝ) := by
      have hb : sourceWidth n y-(u : ℝ)-(H : ℝ)*frozenLowCapacity n y =
          (1-(H : ℝ))/2-(u : ℝ)+sourceGain y-(H : ℝ)*continuedGain (y/(H : ℝ)) := by
        unfold sourceWidth frozenLowCapacity
        field_simp [H_real_bounds.1.ne']
        ring
      unfold lowRadialPrice
      rw [hb]
    rw [hid] at hmax
    have hpay := hmax.trans_lt ((lowRadialPrice_at_H_le hy₁ he₀).trans_lt hp)
    unfold radialAllowance
    rw [max_eq_left (by linarith : (H : ℝ)-V ≤ 0)]
    simpa only [mul_zero,add_zero] using hpay

/-- N8's actual inverse quota: lower tangent, real curved arm, then native. -/
def inverseQuota (r : ℝ) : ℝ :=
  if r < 3/4 then (1-r)/2+5805911/100000000-(379981/5000000)*r
  else if 7/9 ≤ r then (1-r)/2 else curvedQuota r

open QRH.ContactContinuation

/-- The weighted fifth-power inequality gives a supporting line at every
positive radical anchor, not only the isolated physical contact. -/
theorem radical_support {r w : ℝ} (hr : 2/3 ≤ r) (hw : 2/3 < w) :
    radical r ≤ radical w * weight r w := by
  have hw0 : 0 < w := by linarith
  have hwm : 0 < w-2/3 := by linarith
  have hr0 : 0 ≤ r := by linarith
  have ha : 0 ≤ r/w := div_nonneg hr0 hw0.le
  have hb : 0 ≤ (r-2/3)/(w-2/3) := div_nonneg (by linarith) hwm.le
  have hag := weighted_fifth ha hb
  have hwp : 0 ≤ weight r w := by unfold weight; positivity
  have he : (radical w)^5 * ((r/w)^4*((r-2/3)/(w-2/3))) =
      (5/16 : ℝ)^5*7*r^4*(r-2/3) := by
    rw [radical_pow hw.le]
    have hn : -2+w*3 ≠ 0 := by linarith
    field_simp [ne_of_gt hw0, ne_of_gt hwm, hn]
    ring_nf
    field_simp [hn]
    ring
  apply (pow_le_pow_iff_left₀ (by unfold radical; positivity)
    (mul_nonneg (by unfold radical; positivity) hwp) (by decide : (5 : ℕ) ≠ 0)).mp
  rw [radical_pow hr, ← he, mul_pow]
  exact mul_le_mul_of_nonneg_left hag (pow_nonneg (by unfold radical; positivity) 5)

/-- A deliberately coarse exact bound suffices for inverse-witness monotonicity. -/
theorem radical_le_quarter {r : ℝ} (hr : 3/4 ≤ r) (hr₁ : r ≤ 7/9) :
    radical r ≤ 1/4 := by
  have hr0 : 0 ≤ r := by linarith
  have hrm : 0 ≤ r-2/3 := by linarith
  apply (pow_le_pow_iff_left₀ (by unfold radical; positivity)
    (by norm_num : (0 : ℝ) ≤ 1/4) (by decide : (5 : ℕ) ≠ 0)).mp
  rw [radical_pow (by linarith)]
  calc
    (5/16 : ℝ)^5*7*r^4*(r-2/3) ≤ (5/16 : ℝ)^5*7*(7/9)^4*(7/9-2/3) := by gcongr
    _ ≤ (1/4 : ℝ)^5 := by norm_num

/-- The actual radical grows by at most the witness displacement on its
curved arm. The proof is a fifth-power inequality, without differentiating rpow. -/
theorem radical_increment_le {r w : ℝ}
    (hw : 3/4 ≤ w) (hwr : w ≤ r) (hr : r ≤ 7/9) :
    radical r-radical w ≤ r-w := by
  have hw0 : 0 < w := by linarith
  have hwm : 0 < w-2/3 := by linarith
  have hd : 0 ≤ r-w := sub_nonneg.mpr hwr
  have h₁ : r/w ≤ 1+2*(r-w) := by
    apply (div_le_iff₀ hw0).2
    nlinarith [mul_nonneg hd (show 0 ≤ 2*w-1 by linarith)]
  have h₂ : (r-2/3)/(w-2/3) ≤ 1+12*(r-w) := by
    apply (div_le_iff₀ hwm).2
    nlinarith [mul_nonneg hd (show 0 ≤ 12*(w-2/3)-1 by linarith)]
  have hweight : weight r w ≤ 1+4*(r-w) := by unfold weight; linarith
  have ht := radical_support (r := r) (w := w) (by linarith) (by linarith)
  have hrad0 : 0 ≤ radical w := by unfold radical; positivity
  have hmult := mul_le_mul_of_nonneg_left hweight hrad0
  have hrad := radical_le_quarter hw (hwr.trans hr)
  nlinarith [mul_le_mul_of_nonneg_right hrad hd]

/-- On the curved arm the response-diagonal count deficit increases with the
actual inverse witness. -/
theorem curved_deficit_mono {w r : ℝ}
    (hw : 3/4 ≤ w) (hwr : w ≤ r) (hr : r ≤ 7/9) :
    w+curvedQuota w ≤ r+curvedQuota r := by
  have h := radical_increment_le hw hwr hr
  change _ ≤ _ at h
  unfold curvedQuota
  change (w+((1-w)/2+11/16*w-7/24-radical w)) ≤
    (r+((1-r)/2+11/16*r-7/24-radical r))
  linarith

/-- The actual curve is above the certified lower tangent at the 3/4 seam. -/
theorem inverse_tangent_seam :
    (1-(3/4 : ℝ))/2+5805911/100000000-(379981/5000000)*(3/4) ≤ curvedQuota (3/4) := by
  have hrad : radical (3/4) ≤ 22289/100000 := by
    apply (pow_le_pow_iff_left₀ (by unfold radical; positivity)
      (by norm_num : (0 : ℝ) ≤ 22289/100000) (by decide : (5 : ℕ) ≠ 0)).mp
    rw [radical_pow (by norm_num)]
    norm_num
  change _ ≤ (1-(3/4 : ℝ))/2+(11/16)*(3/4)-7/24-radical (3/4)
  linarith

/-- At 7/9 the real curved quota is exactly the native mean quota. -/
theorem inverse_native_seam : curvedQuota (7/9) = (1-(7/9 : ℝ))/2 := by
  have hrad : radical (7/9) = 35/144 := by
    have h0 : 0 ≤ radical (7/9) := by unfold radical; positivity
    apply le_antisymm
    · apply (pow_le_pow_iff_left₀ h0 (by norm_num : (0 : ℝ) ≤ 35/144)
        (by decide : (5 : ℕ) ≠ 0)).mp
      rw [radical_pow (by norm_num)]
      norm_num
    · apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 35/144) h0
        (by decide : (5 : ℕ) ≠ 0)).mp
      rw [radical_pow (by norm_num)]
      norm_num
  change (1-(7/9 : ℝ))/2+(11/16)*(7/9)-7/24-radical (7/9) = _
  rw [hrad]
  norm_num

/-- The two genuinely admitted arms before the native continuation. -/
def preNativeQuota (r : ℝ) : ℝ :=
  if r < 3/4 then (1-r)/2+5805911/100000000-(379981/5000000)*r else curvedQuota r

theorem preNative_deficit_mono {w r : ℝ} (hwr : w ≤ r) (hr : r ≤ 7/9) :
    w+preNativeQuota w ≤ r+preNativeQuota r := by
  by_cases hw : w < 3/4
  · by_cases hr₀ : r < 3/4
    · simp only [preNativeQuota,ite_eq_left hw,ite_eq_left hr₀]
      linarith
    · have hl : w+((1-w)/2+5805911/100000000-(379981/5000000)*w) ≤
          (3/4 : ℝ)+((1-3/4)/2+5805911/100000000-(379981/5000000)*(3/4)) := by linarith
      have hc := curved_deficit_mono (w := 3/4) le_rfl (le_of_not_gt hr₀) hr
      have hs := inverse_tangent_seam
      simp only [preNativeQuota,ite_eq_left hw,ite_eq_right hr₀]
      linarith
  · have hr₀ : ¬r < 3/4 := fun h => hw (hwr.trans_lt h)
    simp only [preNativeQuota,ite_eq_right hw,ite_eq_right hr₀]
    exact curved_deficit_mono (le_of_not_gt hw) hwr hr

theorem inverseQuota_below {r : ℝ} (hr : r < 7/9) :
    inverseQuota r = preNativeQuota r := by
  by_cases hr₀ : r < 3/4
  · simp [inverseQuota,preNativeQuota,hr₀]
  · simp [inverseQuota,preNativeQuota,hr₀,not_le.mpr hr]

theorem inverseQuota_native {r : ℝ} (hr : 7/9 ≤ r) :
    inverseQuota r = (1-r)/2 := by
  have hr₀ : ¬r < 3/4 := by linarith
  simp [inverseQuota,hr₀,hr]

/-- The genuine diagonal deficit increases through both actual source seams;
no tangent continuation above 3/4 or curve continuation above 7/9 is used. -/
theorem inverse_diagonal_mono {w r : ℝ} (hwr : w ≤ r) :
    w+inverseQuota w ≤ r+inverseQuota r := by
  by_cases hw : w < 7/9
  · by_cases hr : r < 7/9
    · rw [inverseQuota_below hw,inverseQuota_below hr]
      exact preNative_deficit_mono hwr hr.le
    · have hb := preNative_deficit_mono (r := 7/9) hw.le le_rfl
      have hj : preNativeQuota (7/9) = (1-(7/9 : ℝ))/2 := by
        rw [preNativeQuota,ite_eq_right (by norm_num),inverse_native_seam]
      rw [hj] at hb
      rw [inverseQuota_below hw,inverseQuota_native (le_of_not_gt hr)]
      linarith
  · have hr : 7/9 ≤ r := (le_of_not_gt hw).trans hwr
    rw [inverseQuota_native (le_of_not_gt hw),inverseQuota_native hr]
    linarith

/-- Increasing the actual inverse witness improves the full common-band
count deficit whenever the actual zero band dominates the response. -/
theorem inverse_deficit_mono {w r e ν : ℝ}
    (he : 0 ≤ e) (hν : e ≤ ν) (hwr : w ≤ r) :
    ν*w+e*inverseQuota w ≤ ν*r+e*inverseQuota r := by
  have hd := mul_le_mul_of_nonneg_left (inverse_diagonal_mono hwr) he
  have hn := mul_le_mul_of_nonneg_left hwr (sub_nonneg.mpr hν)
  nlinarith

/-- Every certified rational inverse quota is below the actual appropriate
N8 arm, with the root guard used only on the genuine curved interval. -/
theorem quota_le_inverseQuota {r root : ℚ} (hg : RootGuard r root) :
    (quota r root : ℝ) ≤ inverseQuota (r : ℝ) := by
  by_cases hlo : r < 3/4
  · have hloR : (r : ℝ) < 3/4 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hlo
      simpa only [Rat.cast_div,Rat.cast_ofNat] using h
    simp [quota,inverseQuota,hlo,hloR]
  · have hloR : ¬(r : ℝ) < 3/4 := by
      have h := (Rat.cast_le (K := ℝ)).mpr (le_of_not_gt hlo)
      exact not_lt.mpr (by simpa only [Rat.cast_div,Rat.cast_ofNat] using h)
    by_cases hhi : 7/9 ≤ r
    · have hhiR : (7/9 : ℝ) ≤ r := by
        have h := (Rat.cast_le (K := ℝ)).mpr hhi
        simpa only [Rat.cast_div,Rat.cast_ofNat] using h
      simp [quota,inverseQuota,hlo,hloR,hhi,hhiR]
    · have hhiR : ¬(7/9 : ℝ) ≤ r := by
        have h := (Rat.cast_lt (K := ℝ)).mpr (lt_of_not_ge hhi)
        exact not_le.mpr (by simpa only [Rat.cast_div,Rat.cast_ofNat] using h)
      rw [inverseQuota,ite_eq_right hloR,ite_eq_right hhiR]
      exact quota_le_curvedQuota (le_of_not_gt hlo) (lt_of_not_ge hhi) hg

/-- The literal P6 inverse price, retaining the actual inverse witness and
its genuine N8 quota. -/
def inversePrice (y e ν V r : ℝ) : ℝ :=
  ν*y+e*(1/2-V/4-y/2+sourceGain y-(u : ℝ))-V*(ν*r+e*inverseQuota r)/2

/-- The original certified short cost bounds the literal cost at every larger
actual inverse witness. -/
theorem inversePrice_le_checked {y e ν r : ℝ} (c : Cutoff)
    (he : 0 ≤ e) (hν : e ≤ ν) (hg : RootGuard c.inverse c.rootUpper)
    (hr : (c.inverse : ℝ) ≤ r) :
    inversePrice y e ν (H : ℝ) r ≤ shortCostWithBand y e ν c := by
  have hq := mul_le_mul_of_nonneg_left (quota_le_inverseQuota hg) he
  have hd := inverse_deficit_mono he hν hr
  have hH : 0 ≤ (H : ℝ) := by norm_num [H,u]
  have hdef : ν*(c.inverse : ℝ)+e*(quota c.inverse c.rootUpper : ℝ) ≤
      ν*r+e*inverseQuota r := by linarith
  have hm := mul_le_mul_of_nonneg_left hdef hH
  unfold inversePrice shortCostWithBand capacityAt
  linarith

/-- A checked short-inverse branch pays its actual larger witness with the
same strict reserve and without a quota monotonicity premise. -/
theorem checked_inverse_pays_larger {y e ν r : ℝ} (c : Cutoff)
    (he : 0 ≤ e) (hν : e ≤ ν) (hg : RootGuard c.inverse c.rootUpper)
    (hr : (c.inverse : ℝ) ≤ r) (hp : PaidWithBand y e ν c) :
    inversePrice y e ν (H : ℝ) r < (u-rho : ℚ) :=
  (inversePrice_le_checked c he hν hg hr).trans_lt hp.1

/-- A coarse exact bound on every genuine inverse quota is enough to pay the
near-H adverse radial slope. -/
theorem inverseQuota_le_half {r : ℝ} (hr₀ : 367/500 ≤ r) (_hr₁ : r ≤ 1) :
    inverseQuota r ≤ 1/2 := by
  unfold inverseQuota
  split_ifs with hlo hhi
  · linarith
  · linarith
  · have hrad : 0 ≤ radical r := by
      unfold radical
      have : 0 ≤ r-2/3 := by linarith
      positivity
    change (1-r)/2+11/16*r-7/24-radical r ≤ _
    linarith

/-- Below H the inverse price's adverse slope is strictly below 5/6 on the
actual response and zero-band domain, for every genuine short witness. -/
theorem inversePrice_lower_radius_paid {y e ν r V : ℝ}
    (he₀ : 0 ≤ e)
    (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    (hr₀ : 367/500 ≤ r) (hr₁ : r ≤ 1) (hV : V ≤ (H : ℝ))
    (hp : inversePrice y e ν (H : ℝ) r < (u-rho : ℚ)) :
    inversePrice y e ν V r < radialAllowance V := by
  have hq := mul_le_mul_of_nonneg_left (inverseQuota_le_half hr₀ hr₁) he₀
  have hnr := mul_le_mul_of_nonneg_left hr₁ (he₀.trans hν)
  have hslope : e/4+(ν*r+e*inverseQuota r)/2 ≤ 5/6 := by
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hV)
  have hid : inversePrice y e ν V r-inversePrice y e ν (H : ℝ) r =
      ((H : ℝ)-V)*(e/4+(ν*r+e*inverseQuota r)/2) := by
    unfold inversePrice
    ring
  unfold radialAllowance
  rw [max_eq_right (sub_nonneg.mpr hV)]
  linarith

/-- The actual inverse quota remains nonnegative up to the short-inverse
endpoint, including its genuinely unmarked zero-width endpoint at one. -/
theorem inverseQuota_nonneg {r : ℝ} (hr₀ : 367/500 ≤ r) (hr₁ : r ≤ 1) :
    0 ≤ inverseQuota r := by
  unfold inverseQuota
  split_ifs with hlo hhi
  · linarith
  · linarith
  · have hrad := radical_le_quarter (le_of_not_gt hlo) (le_of_not_ge hhi)
    change 0 ≤ (1-r)/2+11/16*r-7/24-radical r
    linarith

/-- The genuine retained ordinary fourth uses the native cap V(1/2-n)
above one, continuously joined to its smaller-radius cap at one. -/
def nativeFourthCap (n V : ℝ) : ℝ :=
  if V ≤ 1 then (V/2-n)/2 else V*(1/2-n)

theorem nativeFourthCap_mono {n V₀ V₁ : ℝ}
    (hn : n ≤ 1/2) (hV : V₀ ≤ V₁) :
    nativeFourthCap n V₀ ≤ nativeFourthCap n V₁ := by
  unfold nativeFourthCap
  by_cases h₀ : V₀ ≤ 1
  · by_cases h₁ : V₁ ≤ 1
    · rw [ite_eq_left h₀,ite_eq_left h₁]
      linarith
    · rw [ite_eq_left h₀,ite_eq_right h₁]
      nlinarith [mul_nonneg (show 0 ≤ V₁-1 by linarith) (show 0 ≤ 1/2-n by linarith)]
  · have h₁ : ¬V₁ ≤ 1 := fun h => h₀ (hV.trans h)
    rw [ite_eq_right h₀,ite_eq_right h₁]
    exact mul_le_mul_of_nonneg_right hV (by linarith)

/-- The full inverse price with the correct native cap above unit radius. -/
def actualInversePrice (n y e ν V r : ℝ) : ℝ :=
  ν*y+e*(sourceWidth n y-(u : ℝ)-nativeFourthCap n V)-V*(ν*r+e*inverseQuota r)/2

theorem actualInversePrice_below_one {n y e ν V r : ℝ} (hV : V ≤ 1) :
    actualInversePrice n y e ν V r = inversePrice y e ν V r := by
  unfold actualInversePrice inversePrice nativeFourthCap sourceWidth
  rw [ite_eq_left hV]
  ring

/-- Increasing radius improves the actual inverse price, including the
change to the true native cap at unit radius. -/
theorem actualInversePrice_radius_antitone {n y e ν r V₀ V₁ : ℝ}
    (hn : n ≤ 1/2) (he : 0 ≤ e) (hν : e ≤ ν)
    (hr₀ : 367/500 ≤ r) (hr₁ : r ≤ 1) (hV : V₀ ≤ V₁) :
    actualInversePrice n y e ν V₁ r ≤ actualInversePrice n y e ν V₀ r := by
  have hc := mul_le_mul_of_nonneg_left (nativeFourthCap_mono hn hV) he
  have hd : 0 ≤ ν*r+e*inverseQuota r :=
    add_nonneg (mul_nonneg (he.trans hν) (by linarith))
      (mul_nonneg he (inverseQuota_nonneg hr₀ hr₁))
  have hm := mul_le_mul_of_nonneg_right hV hd
  unfold actualInversePrice
  linarith

/-- A checked inverse cutoff pays every larger actual short inverse at every
radius V≥.98, with the exact lower-radius P2 allowance and genuine native cap. -/
theorem checked_inverse_pays_all_radii {n y e ν r V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hr₀ : 367/500 ≤ r)
    (hr : (c.inverse : ℝ) ≤ r) (hr₁ : r ≤ 1)
    (_hV₀ : (98/100 : ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    actualInversePrice n y e ν V r < radialAllowance V := by
  have hH₁ : (H : ℝ) ≤ 1 := by norm_num [H,u]
  have hpay := checked_inverse_pays_larger c he₀ hν hg hr hp
  by_cases hV : V ≤ (H : ℝ)
  · rw [actualInversePrice_below_one (hV.trans hH₁)]
    exact inversePrice_lower_radius_paid he₀ hν hν₁ hr₀ hr₁ hV hpay
  · have hn₁ : n ≤ 1/2 := by
      have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
      norm_num [sourceRatio,sourceY] at h
      linarith
    have hrad := actualInversePrice_radius_antitone (n := n) (y := y)
      hn₁ he₀ hν hr₀ hr₁ (le_of_not_ge hV)
    rw [actualInversePrice_below_one hH₁] at hrad
    unfold radialAllowance
    rw [max_eq_left (by linarith : (H : ℝ)-V ≤ 0)]
    simpa only [mul_zero,add_zero] using hrad.trans_lt hpay

/-- The genuine amplified inverse deficit, evaluated at its actual inverse
length rather than replacing it by a simultaneous ordinary length. -/
def longDeficit (ν r : ℝ) : ℝ := 5/6-((5/6)-ν)*r

/-- The original long witness r≤T gives at least the tested amplified deficit. -/
theorem longDeficit_cutoff {ν r T : ℝ} (hν : ν ≤ 3/4) (hr : r ≤ T) :
    longDeficit ν T ≤ longDeficit ν r := by
  have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5/6-ν by linarith)
  unfold longDeficit
  linarith

/-- Actual amplified-inverse price with the correct retained native cap. -/
def actualLongPrice (n y e ν V r : ℝ) : ℝ :=
  ν*y+e*(sourceWidth n y-(u : ℝ)-nativeFourthCap n V)-V*longDeficit ν r/2

theorem actualLongPrice_at_H (n y e ν : ℝ) (c : Cutoff) :
    actualLongPrice n y e ν (H : ℝ) ((c.inverse : ℝ)+(c.ordinary : ℝ)) =
      longCostWithBand y e ν c := by
  unfold actualLongPrice nativeFourthCap
  rw [ite_eq_left H_real_bounds.2.le]
  unfold longCostWithBand sourceWidth capacityAt longDeficit
  ring

theorem actualLongPrice_le_checked {n y e ν r : ℝ} (c : Cutoff)
    (hν : ν ≤ 3/4) (hr : r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ)) :
    actualLongPrice n y e ν (H : ℝ) r ≤ longCostWithBand y e ν c := by
  rw [←actualLongPrice_at_H n y e ν c]
  have h := mul_le_mul_of_nonneg_left (longDeficit_cutoff hν hr) H_real_bounds.1.le
  unfold actualLongPrice
  linarith

/-- The retained pre-division scalar capacity is positive on the source domain. -/
theorem capacityAt_nonneg {y : ℝ} (hy : y ≤ sourceY) : 0 ≤ capacityAt y := by
  have hg := sourceGain_antitone hy (le_refl sourceY)
  rw [source_native_value] at hg
  unfold capacityAt
  norm_num [H,u,sourceY] at hy ⊢
  linarith

/-- A paid amplified branch on the actual source domain forces a positive
zero band. This is derived from its price, rather than adding a response floor. -/
theorem paid_long_band_gt_sixth {y e ν : ℝ} (c : Cutoff)
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ sourceY)
    (he₀ : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hp : PaidWithBand y e ν c) : 1/6 < ν := by
  have hT : (27/25 : ℚ) < c.inverse+c.ordinary := hg.2.2.2.1
  have hTR : (27/25 : ℝ) < (c.inverse : ℝ)+(c.ordinary : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hT
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using h
  have hν₀ := he₀.trans hν
  have hecap := mul_nonneg he₀ (capacityAt_nonneg hy₁)
  have hprod := mul_le_mul_of_nonneg_left hTR.le (show 0 ≤ 5/6-ν by linarith)
  have hνy := mul_le_mul_of_nonneg_left hy₀ hν₀
  have hpaid := hp.2.1
  unfold longCostWithBand at hpaid
  by_contra h
  have hsmall := le_of_not_gt h
  norm_num [H,u,rho] at hpaid
  nlinarith

/-- Every genuine amplified witness in the tested finite cutoff range has
strictly positive deficit on a paid branch. -/
theorem paid_longDeficit_positive {y e ν r : ℝ} (c : Cutoff)
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ sourceY)
    (he₀ : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hr : r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ)) (hp : PaidWithBand y e ν c) :
    0 < longDeficit ν r := by
  have hνlo := paid_long_band_gt_sixth c hy₀ hy₁ he₀ hν hν₁ hg hp
  have hT : c.inverse+c.ordinary < (6/5 : ℚ) := hg.2.2.2.2.1
  have hTR : (c.inverse : ℝ)+(c.ordinary : ℝ) < (6/5 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hT
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using h
  have hmul := mul_le_mul_of_nonneg_left (hr.trans hTR.le) (show 0 ≤ 5/6-ν by linarith)
  unfold longDeficit
  nlinarith

/-- The amplified price has an adverse lower-radius slope below 5/6. -/
theorem actualLongPrice_lower_radius_paid {n y e ν r V : ℝ}
    (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    (hr : 1 ≤ r) (hV : V ≤ (H : ℝ))
    (hp : actualLongPrice n y e ν (H : ℝ) r < (u-rho : ℚ)) :
    actualLongPrice n y e ν V r < radialAllowance V := by
  have hD : longDeficit ν r ≤ 5/6 := by
    unfold longDeficit
    have hmul := mul_nonneg (show 0 ≤ 5/6-ν by linarith) (show 0 ≤ r by linarith)
    linarith
  have hslope : e/4+longDeficit ν r/2 ≤ 5/6 := by linarith
  have hscale := mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hV)
  have hid : actualLongPrice n y e ν V r-actualLongPrice n y e ν (H : ℝ) r =
      ((H : ℝ)-V)*(e/4+longDeficit ν r/2) := by
    unfold actualLongPrice nativeFourthCap
    rw [ite_eq_left (hV.trans H_real_bounds.2.le),ite_eq_left H_real_bounds.2.le]
    ring
  unfold radialAllowance
  rw [max_eq_right (sub_nonneg.mpr hV)]
  linarith

/-- A paid long-inverse finite cutoff pays every actual amplified witness
1≤r≤T at every radius at least .98, including the genuine native cap above one. -/
theorem checked_long_pays_all_radii {n y e ν r V : ℝ} (c : Cutoff)
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hr₀ : 1 ≤ r)
    (hr₁ : r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ))
    (_hV₀ : (98/100 : ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    actualLongPrice n y e ν V r < radialAllowance V := by
  have hpH := (actualLongPrice_le_checked (n := n) c hν₁ hr₁).trans_lt hp.2.1
  by_cases hV : V ≤ (H : ℝ)
  · exact actualLongPrice_lower_radius_paid hν hν₁ hr₀ hV hpH
  · have hn₁ : n ≤ 1/2 := by
      have h := hn.trans (mul_le_mul_of_nonneg_left hy₁ (by norm_num [sourceRatio]))
      norm_num [sourceRatio,sourceY] at h
      linarith
    have hcap := mul_le_mul_of_nonneg_left (nativeFourthCap_mono hn₁ (le_of_not_ge hV)) he₀
    have hD := paid_longDeficit_positive c hy₀ hy₁ he₀ hν hν₁ hg hr₁ hp
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_ge hV) hD.le
    have hrad : actualLongPrice n y e ν V r ≤ actualLongPrice n y e ν (H : ℝ) r := by
      unfold actualLongPrice
      linarith
    unfold radialAllowance
    rw [max_eq_left (by linarith : (H : ℝ)-V ≤ 0)]
    simpa only [mul_zero,add_zero] using hrad.trans_lt hpH

/-- The ratio-restored substitute really belongs to an earlier ordered source:
its short cap is at least y/H and its two caps satisfy the actual ratio bound.
Its conservative capacity is below the actual reordered P1 capacity. -/
theorem adjustedWitness_source_domain {n y m V : ℝ}
    (hy₀ : sourceY0 ≤ y) (hn₀ : y ≤ n) (_hn₁ : n ≤ sourceRatio*y)
    (hm : y/(H : ℝ) ≤ m) (hV₀ : 0 < V) (hV₁ : V ≤ (H : ℝ))
    (hwY : adjustedWitness n m V ≤ sourceY) :
    y/(H : ℝ) ≤ min (n/V) (adjustedWitness n m V) ∧
    sourceY0 ≤ min (n/V) (adjustedWitness n m V) ∧
    min (n/V) (adjustedWitness n m V) ≤ sourceY ∧
    max (n/V) (adjustedWitness n m V) ≤
      sourceRatio*min (n/V) (adjustedWitness n m V) ∧
    lowerOrdinaryCapacity n m V ≤ V*sourceWidth
      (max (n/V) (adjustedWitness n m V)) (min (n/V) (adjustedWitness n m V)) := by
  let w := adjustedWitness n m V
  have hypos : 0 ≤ y := source_domain.1.le.trans hy₀
  have hRatioPos : 0 < sourceRatio := by norm_num [sourceRatio]
  have hyH : y ≤ y/(H : ℝ) := (le_div_iff₀ H_real_bounds.1).2
    (mul_le_of_le_one_right hypos H_real_bounds.2.le)
  have hret : y/(H : ℝ) ≤ n/V := by
    apply (div_le_div_iff₀ H_real_bounds.1 hV₀).2
    have ha := mul_le_mul_of_nonneg_left hV₁ hypos
    have hb := mul_le_mul_of_nonneg_right hn₀ H_real_bounds.1.le
    nlinarith
  have hw : y/(H : ℝ) ≤ w := hm.trans (le_max_left _ _)
  have hshort : y/(H : ℝ) ≤ min (n/V) w := le_min hret hw
  have hshort₀ := hy₀.trans (hyH.trans hshort)
  have hret₀ : 0 ≤ n/V := (source_domain.1.le.trans hy₀).trans (hyH.trans hret)
  have hw₀ : 0 ≤ w := (source_domain.1.le.trans hy₀).trans (hyH.trans hw)
  have hleft : n/V ≤ sourceRatio*w := by
    have hh := (div_le_iff₀ (mul_pos hRatioPos hV₀)).mp (le_max_right m (n/(sourceRatio*V)))
    apply (div_le_iff₀ hV₀).2
    change n ≤ w*(sourceRatio*V) at hh
    nlinarith
  have hright : w ≤ sourceRatio*(n/V) := by
    have hY : sourceY ≤ sourceRatio*sourceY0 := by norm_num [sourceY,sourceRatio,sourceY0]
    exact hwY.trans (hY.trans (mul_le_mul_of_nonneg_left (hy₀.trans (hyH.trans hret)) hRatioPos.le))
  have hratio : max (n/V) w ≤ sourceRatio*min (n/V) w := by
    rw [mul_min_of_nonneg _ _ hRatioPos.le]
    apply max_le
    · exact le_min (by nlinarith [mul_nonneg hret₀ (show 0 ≤ sourceRatio-1 by norm_num [sourceRatio])]) hleft
    · exact le_min hright (by nlinarith [mul_nonneg hw₀ (show 0 ≤ sourceRatio-1 by norm_num [sourceRatio])])
  refine ⟨hshort,hshort₀,(min_le_right _ _).trans hwY,hratio,?_⟩
  have hg := sourceGain_antitone (min_le_right (n/V) w) hwY
  have hgV := mul_le_mul_of_nonneg_left hg hV₀.le
  have hsum : max (n/V) w+min (n/V) w = n/V+w := by
    rcases le_total (n/V) w with h | h
    · rw [max_eq_right h,min_eq_left h]; ring
    · rw [max_eq_left h,min_eq_right h]
  have hscale := congrArg (fun z : ℝ => V*z) hsum
  have hcancel : V*(n/V) = n := by field_simp
  unfold lowerOrdinaryCapacity
  rw [ite_eq_left hwY]
  unfold sourceWidth
  change (V-n-V*w)/2+V*sourceGain w ≤ _
  nlinarith

/-- Complete scalar continuation for the actual simultaneous inverse/ordinary
witness pair at every regular radius at least .98. The three high alternatives
are selected on that same pair, with its genuine inverse upper cutoff and
simultaneous sum lower cutoff. This is a scalar price cover, not analytic
admission of the original marked energy or an o(1) collar theorem. -/
theorem source_scalar_complete_cover {n y e ν : ℝ}
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ (243/625 : ℝ))
    (_hn₀ : y ≤ n) (hn₁ : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hν : e ≤ ν) (hν₁ : ν ≤ 3/4) :
    ∃ c ∈ sourceCells, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) ∧
      ((e ≤ (c.threshold : ℝ) ∧ e*max 0 (lowBracketAt y) < (u-rho : ℚ) ∧
        ∀ V : ℝ, (98/100 : ℝ) ≤ V → actualLowPrice n y e V < radialAllowance V) ∨
       ((c.threshold : ℝ) ≤ e ∧ ∃ p ∈ c.cutoffs.zipIdx,
          CutoffGuard c.upper p.1 ∧ PaidWithBand y e ν p.1 ∧
          ∀ r m V : ℝ, 0 ≤ r → r ≤ (p.1.inverse : ℝ)+(p.1.ordinary : ℝ) →
            (p.1.inverse : ℝ)+(p.1.ordinary : ℝ) ≤ r+m → m ≤ 1/2 →
            (98/100 : ℝ) ≤ V →
            ((1 ≤ r ∧ actualLongPrice n y e ν V r < radialAllowance V) ∨
             (r < 1 ∧ (p.1.inverse : ℝ) ≤ r ∧
                actualInversePrice n y e ν V r < radialAllowance V) ∨
             (r < (p.1.inverse : ℝ) ∧ actualOrdinaryPrice n y e ν V m < radialAllowance V)))) := by
  obtain ⟨c,hc,hyl,hyu,hcase⟩ :=
    source_scalar_continuum_with_band hy₀ hy₁ he₀ he₁ hν
  have hy₀' : sourceY0 ≤ y := by simpa [sourceY0] using hy₀
  have hy₁' : y ≤ sourceY := by simpa [sourceY] using hy₁
  refine ⟨c,hc,hyl,hyu,?_⟩
  rcases hcase with ⟨hlow,hpaid⟩ | ⟨hhigh,p,hp,hguard,hpaid,hr,hm,hsum⟩
  · exact Or.inl ⟨hlow,hpaid,fun V hV => checked_low_pays_all_radii hy₀' hy₁' hn₁ he₀ he₁ hV hpaid⟩
  · refine Or.inr ⟨hhigh,p,hp,hguard,hpaid,?_⟩
    have hr₀ : (367/500 : ℚ) < p.1.inverse := hguard.2.2.2.2.2.1
    have hr₀R : (367/500 : ℝ) < p.1.inverse := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hr₀
      simpa only [Rat.cast_div,Rat.cast_ofNat] using h
    have hroot := hguard.2.2.2.2.2.2.2.2
    have hypos : 0 ≤ y := source_domain.1.le.trans hy₀'
    have hyH : y ≤ y/(H : ℝ) := (le_div_iff₀ H_real_bounds.1).2
      (mul_le_of_le_one_right hypos H_real_bounds.2.le)
    have hc₀ := hy₀'.trans (hyH.trans hm)
    intro r m V _hr₀ hr₁ hrm hm₁ hV
    by_cases hrLong : 1 ≤ r
    · exact Or.inl ⟨hrLong,checked_long_pays_all_radii p.1 hy₀ hy₁' hn₁
        he₀ hν hν₁ hguard hrLong hr₁ hV hpaid⟩
    · have hrSmall : r < 1 := lt_of_not_ge hrLong
      by_cases hrShort : (p.1.inverse : ℝ) ≤ r
      · exact Or.inr (Or.inl ⟨hrSmall,hrShort,checked_inverse_pays_all_radii p.1 hy₁' hn₁
          he₀ hν hν₁ hroot (by linarith) hrShort hrSmall.le hV hpaid⟩)
      · have hmLarge : (p.1.ordinary : ℝ) ≤ m := by linarith
        exact Or.inr (Or.inr ⟨lt_of_not_ge hrShort,checked_ordinary_pays_all_radii p.1 hy₁' hn₁
          he₀ he₁ hν hν₁ hm hc₀ hmLarge hm₁ hV hpaid⟩)

/-- Literal complementary-sector prices of P.2; these do not invoke the
regular source when its radius is below .98. -/
def outerSourcePrice (n y V : ℝ) : ℝ :=
  if V < 2/25 then (3/4)*(n+y)+sourceWMax-(u : ℝ)
  else if V < 7/8 then (3/4)*(sourceWMax-(u : ℝ))
  else (3/4)*max 0 ((1-V)/2+sourceGain sourceY0-(u : ℝ))

theorem outerSourcePrice_paid {n y V : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y) (hV : V < 98/100) :
    outerSourcePrice n y V < radialAllowance V := by
  unfold outerSourcePrice
  split_ifs with hsmall hmiddle
  · exact pointwise_lower_radius_paid hy hn hsmall.le
  · exact unmarked_lower_radius_paid hmiddle.le
  · exact native_lower_radius_paid hV.le

/-- The original complementary sector is used below .98; the actual continued
regular price is used only on its genuine regular-radius domain. -/
def regularOrOuterPrice (n y V regular : ℝ) : ℝ :=
  if V < 98/100 then outerSourcePrice n y V else regular

/-- The complete all-positive-radius scalar source cover. Every high branch
is on one actual same-zero witness pair; each complementary radius uses its
original paid sector. The finite response domain is exactly e≤.5002. The
separate high-response SN9 analytic supplier is not asserted here. -/
theorem source_scalar_all_radius_cover {n y e ν : ℝ}
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ (243/625 : ℝ))
    (hn₀ : y ≤ n) (hn₁ : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hν : e ≤ ν) (hν₁ : ν ≤ 3/4) :
    ∃ c ∈ sourceCells, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) ∧
      ((e ≤ (c.threshold : ℝ) ∧ e*max 0 (lowBracketAt y) < (u-rho : ℚ) ∧
        ∀ V : ℝ, 0 < V → regularOrOuterPrice n y V (actualLowPrice n y e V) < radialAllowance V) ∨
       ((c.threshold : ℝ) ≤ e ∧ ∃ p ∈ c.cutoffs.zipIdx,
          CutoffGuard c.upper p.1 ∧ PaidWithBand y e ν p.1 ∧
          ∀ r m V : ℝ, 0 ≤ r → r ≤ (p.1.inverse : ℝ)+(p.1.ordinary : ℝ) →
            (p.1.inverse : ℝ)+(p.1.ordinary : ℝ) ≤ r+m → m ≤ 1/2 → 0 < V →
            ((1 ≤ r ∧ regularOrOuterPrice n y V (actualLongPrice n y e ν V r) < radialAllowance V) ∨
             (r < 1 ∧ (p.1.inverse : ℝ) ≤ r ∧
                regularOrOuterPrice n y V (actualInversePrice n y e ν V r) < radialAllowance V) ∨
             (r < (p.1.inverse : ℝ) ∧
                regularOrOuterPrice n y V (actualOrdinaryPrice n y e ν V m) < radialAllowance V)))) := by
  obtain ⟨c,hc,hyl,hyu,hcase⟩ := source_scalar_complete_cover hy₀ hy₁ hn₀ hn₁ he₀ he₁ hν hν₁
  have hyY : y ≤ sourceY := by simpa [sourceY] using hy₁
  refine ⟨c,hc,hyl,hyu,?_⟩
  rcases hcase with ⟨hlow,hpaid,hfun⟩ | ⟨hhigh,p,hp,hguard,hpaid,hfun⟩
  · refine Or.inl ⟨hlow,hpaid,?_⟩
    intro V _hV₀
    unfold regularOrOuterPrice
    split_ifs with hV
    · exact outerSourcePrice_paid hyY hn₁ hV
    · exact hfun V (le_of_not_gt hV)
  · refine Or.inr ⟨hhigh,p,hp,hguard,hpaid,?_⟩
    intro r m V hr₀ hr₁ hrm hm₁ _hV₀
    by_cases hV : V < 98/100
    · have hout := outerSourcePrice_paid hyY hn₁ hV
      have hcased := hfun r m (98/100) hr₀ hr₁ hrm hm₁ le_rfl
      rcases hcased with ⟨hr,_⟩ | ⟨hr,hri,_⟩ | ⟨hr,_⟩
      · exact Or.inl ⟨hr,by simpa only [regularOrOuterPrice,ite_eq_left hV] using hout⟩
      · exact Or.inr (Or.inl ⟨hr,hri,by simpa only [regularOrOuterPrice,ite_eq_left hV] using hout⟩)
      · exact Or.inr (Or.inr ⟨hr,by simpa only [regularOrOuterPrice,ite_eq_left hV] using hout⟩)
    · simpa only [regularOrOuterPrice,ite_eq_right hV] using
        hfun r m V hr₀ hr₁ hrm hm₁ (le_of_not_gt hV)

end
end QRH.Cycle092.Source
