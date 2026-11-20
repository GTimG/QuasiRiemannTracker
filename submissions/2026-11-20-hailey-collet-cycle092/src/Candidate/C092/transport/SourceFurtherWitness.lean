/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual B.5.1 witnesses and their explicit support/spike collars. -/
import Candidate.C092.Source
import Candidate.C092.transport.SignedEnergy

set_option autoImplicit false
namespace QRH.Cycle092.SourceFurtherWitness
noncomputable section
open QRH.Cycle092.Source QRH.SourceCertificate QRH.Cycle090
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

/-- The literal finite-cutoff sum, in the real source normalization. -/
def totalCutoff (c : Cutoff) : ℝ := (c.inverse : ℝ)+(c.ordinary : ℝ)

theorem cutoff_detector_domain {b : ℚ} (c : Cutoff) (hg : CutoffGuard b c) :
    1 ≤ totalCutoff c ∧ totalCutoff c ≤ 3/2 := by
  have hlo := (Rat.cast_lt (K := ℝ)).mpr hg.2.2.2.1
  have hhi := (Rat.cast_lt (K := ℝ)).mpr hg.2.2.2.2.1
  norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] at hlo hhi
  unfold totalCutoff
  constructor <;> linarith

/-- The genuine upstream theorem supplies every selected source cutoff, with
one common early threshold before the later row family and the cutoff choice. -/
theorem actual_source_witness_family (dmin dmax tau ε mesh kappa eta : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (htau : 0 < tau)
    (hzero : tau < dmin/2) (hheight : 4*tau < dmin*eta)
    (hε : 0 < ε) (hmesh : 0 < mesh) (hmesh₁ : mesh < 1/1000)
    (hkappa : 0 < kappa) (hkappa₁ : kappa ≤ 1) (heta : 0 ≤ eta)
    (hbudget : 12*mesh*((22 : ℝ)+2)+8*kappa+2*eta ≤ ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row → Label → Character)
        (hχ : ∀ u j, (χ u j).residue ≠ 1) (a : ℝ) (i : ℕ), i ≤ I → 51/100 < a → a ≤ 1 →
        (∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^tau) < a+2*mesh) →
        (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^tau)) →
        (∀ u j, (χ u j).modulus.absNorm ≤ Z^d) →
        ∀ {b : ℚ} (c : Cutoff), CutoffGuard b c →
          Nonempty (∀ u, SupportedWitness (χ u) (Z^d) a ε (totalCutoff c)
            (Z^tau) ((Z^d)^(tau/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := actual_supported_witness_family dmin dmax tau ε mesh kappa eta I
    hdmin hdmax htau hzero hheight hε hmesh hmesh₁ hkappa hkappa₁ heta hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd₁ Row Label _ χ hχ a i hi ha ha₁ hnext hcurrent hQ b c hg
  obtain ⟨hT₀,hT₁⟩ := cutoff_detector_domain c hg
  exact hZ₀ Z hZ d hd hd₁ χ hχ a i hi ha ha₁ hnext hcurrent hQ (totalCutoff c) hT₀ hT₁

/-- Collar conditions are consequences of the actual witness, rather than
new hypotheses replacing its same-zero construction. -/
theorem actual_witness_lengths {Label : Type*} {χ : Label → Character}
    {U a ε T allowance : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i) :
    w.r ≤ totalCutoff c+ε ∧ totalCutoff c-w.r-ε ≤ w.m ∧
    0 ≤ w.m ∧ w.m ≤ 1/2+75*ε :=
  ⟨w.inverse_length_upper,w.product_length_lower,w.plain_length_lower,w.plain_length_upper⟩

/-- The actual same pair gives an ordinary witness within ε of its recorded
cutoff whenever its inverse misses the recorded inverse threshold. -/
theorem actual_ordinary_collar {Label : Type*} {χ : Label → Character}
    {U a ε T allowance : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i)
    (hr : w.r < (c.inverse : ℝ)) : (c.ordinary : ℝ)-ε ≤ w.m := by
  have h := w.product_length_lower
  unfold totalCutoff at h
  linarith

/-- The ordinary cap is rounded upward, while the actual witness stays in
its comparison debit and in the underlying polynomial. -/
def collaredOrdinaryCap (c : Cutoff) (m : ℝ) : ℝ := max m (c.ordinary : ℝ)

theorem actual_ordinary_cap_collar {Label : Type*} {χ : Label → Character}
    {U a ε T allowance : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i)
    (hε : 0 ≤ ε) (hr : w.r < (c.inverse : ℝ)) :
    0 ≤ collaredOrdinaryCap c w.m-w.m ∧ collaredOrdinaryCap c w.m-w.m ≤ ε := by
  have hm := actual_ordinary_collar c w hr
  unfold collaredOrdinaryCap
  constructor
  · exact sub_nonneg.mpr (le_max_left _ _)
  · apply sub_le_iff_le_add.mpr
    exact max_le (by linarith) (by linarith)

/-- P6's actual inverse spike has the exact -2ε exponent supplied by B.5.1. -/
def collaredInversePrice (n y e ν V r ε : ℝ) : ℝ :=
  actualInversePrice n y e ν V r+V*ε

/-- The genuine amplified spike has its same -2ε loss; the actual r, including
its upper cutoff collar, remains inside the amplified deficit. -/
def collaredLongPrice (n y e ν V r ε : ℝ) : ℝ :=
  actualLongPrice n y e ν V r+V*ε

/-- Ordinary P4 keeps the actual m in the debit, its dominating rounded cap
in the source, and its actual 2Vε spike loss. -/
def collaredOrdinaryPrice (n y e ν V m ε : ℝ) (c : Cutoff) : ℝ :=
  actualOrdinaryPrice n y e ν V (collaredOrdinaryCap c m)+
    ν*V*(collaredOrdinaryCap c m-m)+2*V*ε

/-- The already checked short branch needs no support repair: its actual
length remains on the paid side of the inverse cutoff. -/
theorem actual_short_price_paid {Label : Type*} {χ : Label → Character}
    {U a ε T allowance n y e ν V : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y e ν c)
    (hr₀ : (c.inverse : ℝ) ≤ w.r) (hr₁ : w.r < 1) (hV : (98/100 : ℝ) ≤ V) :
    collaredInversePrice n y e ν V w.r ε < radialAllowance V+V*ε := by
  have hlo := (Rat.cast_lt (K := ℝ)).mpr hg.2.2.2.2.2.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hlo
  have h := checked_inverse_pays_all_radii c hy hn he hν hν₁ hg.2.2.2.2.2.2.2.2
    (by linarith) hr₀ hr₁.le hV hp
  unfold collaredInversePrice
  linarith

/-- The actual inverse upper collar costs at most 5Vε/12 in addition to its
original Vε spike loss. The original cutoff price is still the paid anchor. -/
theorem actual_long_price_paid {Label : Type*} {χ : Label → Character}
    {U a ε T allowance n y e ν V : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i)
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y e ν c)
    (hε : 0 ≤ ε) (hV : (98/100 : ℝ) ≤ V) :
    collaredLongPrice n y e ν V w.r ε < radialAllowance V+(17/12)*V*ε := by
  have hdom := cutoff_detector_domain c hg
  have hanchor := checked_long_pays_all_radii c hy₀ hy₁ hn he hν hν₁ hg
    hdom.1 (le_refl (totalCutoff c)) hV hp
  have hr := w.inverse_length_upper
  have hA : 0 ≤ 5/6-ν := by linarith
  have hmul := mul_le_mul_of_nonneg_left hr hA
  have hdef : longDeficit ν (totalCutoff c)-longDeficit ν w.r ≤ (5/6-ν)*ε := by
    unfold longDeficit
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hdef (show 0 ≤ V by linarith)
  have hband : (5/6-ν)*ε ≤ (5/6)*ε := by
    have hν₀ := he.trans hν
    nlinarith
  have hbandV := mul_le_mul_of_nonneg_left hband (show 0 ≤ V by linarith)
  unfold collaredLongPrice actualLongPrice at *
  nlinarith

/-- Absolute source capacity used in the actual ordinary branch. -/
def ordinaryCapacity (n m V : ℝ) : ℝ :=
  if V ≤ (H : ℝ) then lowerOrdinaryCapacity n m V else V*frozenCapacity n m

theorem actualOrdinaryPrice_as_capacity (n y e ν V m : ℝ) :
    actualOrdinaryPrice n y e ν V m =
      -ν*(V*m-y)+e*max 0 (sourceWidth n y-(u : ℝ)-ordinaryCapacity n m V) := by
  unfold actualOrdinaryPrice ordinaryCapacity
  split_ifs <;> rfl

/-- Beyond 1/2 both labels use the genuine native continuation, so their
capacity difference is exactly half their absolute witness displacement. -/
theorem native_ordinary_capacity_difference {n m V : ℝ} (hm : 1/2 ≤ m) :
    ordinaryCapacity n (1/2) V-ordinaryCapacity n m V = V*(m-1/2)/2 := by
  have hmY : ¬m ≤ sourceY := by norm_num [sourceY] at *; linarith
  have hhalfY : ¬(1/2 : ℝ) ≤ sourceY := by norm_num [sourceY]
  have hwm : ¬adjustedWitness n m V ≤ sourceY := by
    have h := le_max_left m (n/(sourceRatio*V))
    exact fun hh => hmY (h.trans hh)
  have hwh : ¬adjustedWitness n (1/2) V ≤ sourceY := by
    have h := le_max_left (1/2 : ℝ) (n/(sourceRatio*V))
    exact fun hh => hhalfY (h.trans hh)
  unfold ordinaryCapacity
  split_ifs with hV
  · simp only [lowerOrdinaryCapacity,ite_eq_right hwm,ite_eq_right hwh]
    ring
  · simp only [frozenCapacity,continuedGain,ite_eq_right hmY,ite_eq_right hhalfY]
    ring

/-- The native ordinary price keeps decreasing after the exact half-length
endpoint. This is used only with the actual bounded 75ε witness extension. -/
theorem actualOrdinaryPrice_native_extension {n y e ν V m : ℝ}
    (he : 0 ≤ e) (hν : e ≤ ν) (hV : 0 ≤ V) (hm : 1/2 ≤ m) :
    actualOrdinaryPrice n y e ν V m ≤ actualOrdinaryPrice n y e ν V (1/2) := by
  have hcap := native_ordinary_capacity_difference (n := n) (V := V) hm
  have hd : 0 ≤ V*(m-1/2)/2 := by positivity
  have hmax : max 0 (sourceWidth n y-(u : ℝ)-ordinaryCapacity n m V) ≤
      max 0 (sourceWidth n y-(u : ℝ)-ordinaryCapacity n (1/2) V)+V*(m-1/2)/2 := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) hd
    · have h := le_max_right 0 (sourceWidth n y-(u : ℝ)-ordinaryCapacity n (1/2) V)
      linarith
  have hemax := mul_le_mul_of_nonneg_left hmax he
  have hband := mul_nonneg (show 0 ≤ ν-e/2 by linarith) (show 0 ≤ V*(m-1/2) by positivity)
  rw [actualOrdinaryPrice_as_capacity,actualOrdinaryPrice_as_capacity]
  nlinarith

/-- The paid ordinary cutoff also pays its actual short bounded extension;
the algebraic statement is stronger, while capacity legality is checked below. -/
theorem checked_ordinary_pays_extended {n y e ν m V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ)) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H : ℝ) ≤ (c.ordinary : ℝ)) (hc₀ : sourceY0 ≤ (c.ordinary : ℝ))
    (hm : (c.ordinary : ℝ) ≤ m) (hV : (98/100 : ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    actualOrdinaryPrice n y e ν V m < radialAllowance V := by
  by_cases hm₁ : m ≤ 1/2
  · exact checked_ordinary_pays_all_radii c hy hn he₀ he₁ hν hν₁ hc hc₀ hm hm₁ hV hp
  · have hhalf : (c.ordinary : ℝ) ≤ 1/2 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hg.2.2.2.2.2.2.2.1
      norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
      linarith
    exact (actualOrdinaryPrice_native_extension he₀ hν (by linarith) (le_of_not_ge hm₁)).trans_lt
      (checked_ordinary_pays_all_radii c hy hn he₀ he₁ hν hν₁ hc hc₀ hhalf le_rfl hV hp)

/-- The actual collared dominating cap remains in a genuinely positive native
width range. The small ε bound is fixed before the witness is selected. -/
theorem actual_ordinary_cap_upper {Label : Type*} {χ : Label → Character}
    {U a ε T allowance : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i)
    {b : ℚ} (hg : CutoffGuard b c) (hε : ε ≤ 1/7500) :
    collaredOrdinaryCap c w.m ≤ 51/100 := by
  have h := (Rat.cast_lt (K := ℝ)).mpr hg.2.2.2.2.2.2.2.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  unfold collaredOrdinaryCap
  exact max_le (by linarith [w.plain_length_upper]) (by linarith)

/-- The actual ordinary witness collar costs at most 11Vε/4, including its
2Vε spike loss and the debit for using the dominating source cap. -/
theorem actual_ordinary_price_paid {Label : Type*} {χ : Label → Character}
    {U a ε T allowance n y e ν V : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ U a ε (totalCutoff c) T allowance i)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ)) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H : ℝ) ≤ (c.ordinary : ℝ)) (hc₀ : sourceY0 ≤ (c.ordinary : ℝ))
    (hp : PaidWithBand y e ν c) (hε : 0 ≤ ε) (hr : w.r < (c.inverse : ℝ))
    (hV : (98/100 : ℝ) ≤ V) :
    collaredOrdinaryPrice n y e ν V w.m ε c < radialAllowance V+(11/4)*V*ε := by
  have hpaid := checked_ordinary_pays_extended (m := collaredOrdinaryCap c w.m) c hy hn he₀ he₁ hν hν₁ hg hc hc₀
    (le_max_right w.m (c.ordinary : ℝ)) hV hp
  have hgap := actual_ordinary_cap_collar c w hε hr
  have hν₀ := he₀.trans hν
  have hgapν := mul_le_mul_of_nonneg_left hgap.2 hν₀
  have hεband := mul_le_mul_of_nonneg_right hν₁ hε
  have hscale := mul_le_mul_of_nonneg_left (hgapν.trans hεband) (show 0 ≤ V by linarith)
  unfold collaredOrdinaryPrice
  nlinarith

/-- The bounded actual ordinary extension has positive source capacity, on
both sides of H. Thus the native extension used above does not ask for a
negative quota or silently replace the actual ordinary length. -/
theorem ordinaryCapacity_positive_extended {n y m V : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (hm : m ≤ 51/100) (hV : (98/100 : ℝ) ≤ V) :
    0 < ordinaryCapacity n m V := by
  have hnY := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
  have hnNum : n ≤ (5589/12500 : ℝ) := by norm_num [sourceRatio,sourceY] at hnY; exact hnY
  have hVpos : 0 < V := by linarith
  unfold ordinaryCapacity
  split_ifs with hVH
  · unfold lowerOrdinaryCapacity
    dsimp only
    split_ifs with hwY
    · have hg := sourceGain_antitone hwY (le_refl sourceY)
      rw [source_native_value] at hg
      have hgV := mul_le_mul_of_nonneg_left hg hVpos.le
      have hwV := mul_le_mul_of_nonneg_left hwY hVpos.le
      have hbase := mul_nonneg (show 0 ≤ V-98/100 by linarith)
        (show 0 ≤ 1-sourceY-2/10000000 by norm_num [sourceY])
      norm_num [sourceY] at hwV hbase
      nlinarith
    · have hmV := mul_le_mul_of_nonneg_left hm hVpos.le
      have hbase := mul_nonneg (show 0 ≤ V-98/100 by linarith) (show 0 ≤ (49/100 : ℝ) by norm_num)
      nlinarith
  · have hnH : n/(H : ℝ) ≤ 9/20 := by
      apply (div_le_iff₀ H_real_bounds.1).2
      norm_num [H,u]
      linarith
    have hg := continuedGain_lower_bound m
    have hcap : 0 < frozenCapacity n m := by unfold frozenCapacity; linarith
    exact mul_pos hVpos hcap

/-- Actual witness selection and both spike collars now feed the same finite
source cutoff. The zero-band parameter is literally 2a-1 for this witness.
The explicit error is at most 3Vε; no exact-cutoff witness is substituted. -/
theorem source_actual_witness_cover {n y e ν : ℝ}
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ (243/625 : ℝ))
    (_hn₀ : y ≤ n) (hn₁ : n ≤ sourceRatio*y)
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hν : e ≤ ν) (hν₁ : ν ≤ 3/4) :
    ∃ c ∈ sourceCells, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) ∧
      ((e ≤ (c.threshold : ℝ) ∧ e*max 0 (lowBracketAt y) < (u-rho : ℚ)) ∨
       ((c.threshold : ℝ) ≤ e ∧ ∃ p ∈ c.cutoffs.zipIdx,
          CutoffGuard c.upper p.1 ∧ PaidWithBand y e ν p.1 ∧
          ∀ {Label : Type*} {χ : Label → Character} {U ε T allowance : ℝ} {i : ℕ},
            ∀ V : ℝ, (98/100 : ℝ) ≤ V →
            ∀ w : SupportedWitness χ (U^V) ((1+ν)/2) ε (totalCutoff p.1) T allowance i,
              0 ≤ ε →
              ((1 ≤ w.r ∧ collaredLongPrice n y e ν V w.r ε < radialAllowance V+3*V*ε) ∨
               (w.r < 1 ∧ (p.1.inverse : ℝ) ≤ w.r ∧
                  collaredInversePrice n y e ν V w.r ε < radialAllowance V+3*V*ε) ∨
               (w.r < (p.1.inverse : ℝ) ∧ (p.1.ordinary : ℝ)-ε ≤ w.m ∧
                  collaredOrdinaryPrice n y e ν V w.m ε p.1 < radialAllowance V+3*V*ε)))) := by
  obtain ⟨c,hc,hyl,hyu,hcase⟩ := source_scalar_continuum_with_band hy₀ hy₁ he₀ he₁ hν
  have hyY : y ≤ sourceY := by simpa [sourceY] using hy₁
  have hyY₀ : sourceY0 ≤ y := by simpa [sourceY0] using hy₀
  refine ⟨c,hc,hyl,hyu,?_⟩
  rcases hcase with hlo | ⟨hhigh,p,hp,hguard,hpaid,hr,hm,hsum⟩
  · exact Or.inl hlo
  · refine Or.inr ⟨hhigh,p,hp,hguard,hpaid,?_⟩
    have hypos : 0 ≤ y := source_domain.1.le.trans hyY₀
    have hyH : y ≤ y/(H : ℝ) := (le_div_iff₀ H_real_bounds.1).2
      (mul_le_of_le_one_right hypos H_real_bounds.2.le)
    have hc₀ := hyY₀.trans (hyH.trans hm)
    intro Label χ U ε T allowance i V hV w hε
    have hVε : 0 ≤ V*ε := mul_nonneg (by linarith) hε
    by_cases hlong : 1 ≤ w.r
    · have h := actual_long_price_paid p.1 w hy₀ hyY hn₁ he₀ hν hν₁ hguard hpaid hε hV
      exact Or.inl ⟨hlong,by nlinarith⟩
    · by_cases hshort : (p.1.inverse : ℝ) ≤ w.r
      · have h := actual_short_price_paid p.1 w hyY hn₁ he₀ hν hν₁ hguard hpaid hshort
          (lt_of_not_ge hlong) hV
        exact Or.inr (Or.inl ⟨lt_of_not_ge hlong,hshort,by nlinarith⟩)
      · have hr₀ := lt_of_not_ge hshort
        have h := actual_ordinary_price_paid p.1 w hyY hn₁ he₀ he₁ hν hν₁ hguard hm hc₀ hpaid hε hr₀ hV
        exact Or.inr (Or.inr ⟨hr₀,actual_ordinary_collar p.1 w hr₀,by nlinarith⟩)

/-- A fixed ambient radial cap converts the actual support/spike error into
a uniform early mesh choice, leaving half the original positive reserve. -/
theorem collared_price_keeps_half_reserve {price V ε M : ℝ}
    (_hV₀ : 0 ≤ V) (hV₁ : V ≤ M) (hε₀ : 0 ≤ ε)
    (hε₁ : 6*M*ε ≤ (rho : ℝ))
    (hp : price < radialAllowance V+3*V*ε) :
    price < (u : ℝ)-(rho : ℝ)/2+(5/6)*max 0 ((H : ℝ)-V) := by
  have hprod := mul_le_mul_of_nonneg_right hV₁ hε₀
  unfold radialAllowance at hp
  push_cast at hp
  linarith

/-- The early witness decrement can be chosen uniformly before rows, profiles,
cutoffs, zero bands, and live heights, for a fixed positive radial cap M. -/
theorem early_witness_mesh_exists {M : ℝ} (hM : 0 < M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1/7500 ∧ 6*M*ε₀ ≤ (rho : ℝ) := by
  let ε₀ : ℝ := min (1/7500) ((rho : ℝ)/(6*M))
  have hrho : 0 < (rho : ℝ) := by norm_num [rho]
  have hd : 0 < 6*M := by positivity
  refine ⟨ε₀,lt_min (by norm_num) (div_pos hrho hd),min_le_left _ _,?_⟩
  have h := (le_div_iff₀ hd).mp (min_le_right (1/7500 : ℝ) ((rho : ℝ)/(6*M)))
  dsimp [ε₀]
  nlinarith

/-- A high paid cutoff itself supplies the real-part domain required by the
actual upstream zero-witness theorem; no new floor premise is introduced. -/
theorem paid_cutoff_actual_band_domain {y e ν : ℝ} (c : Cutoff)
    (hy₀ : (369/1000 : ℝ) ≤ y) (hy₁ : y ≤ sourceY)
    (he₀ : 0 ≤ e) (hν : e ≤ ν) (hν₁ : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y e ν c) :
    51/100 < (1+ν)/2 ∧ (1+ν)/2 ≤ 1 := by
  have h := paid_long_band_gt_sixth c hy₀ hy₁ he₀ hν hν₁ hg hp
  constructor <;> linarith

/-- The actual P4 energy uses the supported ordinary polynomial at its real
length and zero. Only its upper cap is raised to max(m,m0); the exact exponent
loss for this change is at most (2a+1)Vε, including the original spike loss. -/
theorem actual_ordinary_energy_at_dominating_cap {Label : Type*} {χ : Label → Character}
    {U V a ε T allowance y δ : ℝ} {i : ℕ} (c : Cutoff)
    (w : SupportedWitness χ (U^V) a ε (totalCutoff c) T allowance i)
    (A_y A_n Q : ℂ) (reverse : Bool)
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hband : 0 ≤ 2*a-1) (hε : 0 ≤ ε)
    (hr : w.r < (c.inverse : ℝ)) (hy : ‖A_y‖^2 ≤ U^((2*a-1)*y+δ)) :
    ‖A_n*A_y*Q‖^2 ≤
      U^((2*a-1)*(y-V*collaredOrdinaryCap c w.m)+δ+(2*a+1)*V*ε)*
        ‖A_n*QRH.Cycle092.SignedEnergy.oriented reverse
          (QRH.Cycle092.SignedEnergy.actualPlain w)*Q‖^2 := by
  have hraw := QRH.Cycle092.SignedEnergy.actual_same_zero
    (zero_lt_one.trans_le hU) w A_y A_n Q reverse hy
  have hgap := actual_ordinary_cap_collar c w hε hr
  have hscale := mul_le_mul_of_nonneg_left hgap.2 (mul_nonneg hband hV)
  have hex : (2*a-1)*(y-V*w.m)+δ+2*V*ε ≤
      (2*a-1)*(y-V*collaredOrdinaryCap c w.m)+δ+(2*a+1)*V*ε := by nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hU hex) (sq_nonneg _))

end
end QRH.Cycle092.SourceFurtherWitness
