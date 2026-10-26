import Candidate.Cycle63.Physical.CoupledRadicalSaving

namespace MarkedAllocationReserve
noncomputable section

/-- Retaining the first allocation norm gives a strict loss when slots disappear. -/
theorem first_common_saving (ρ δ κ c d p R E Bc Lc R₀ : ℝ)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hδ : κ ≤ δ)
    (hsum : 1 + κ ≤ ρ + δ) (hfive : 1 ≤ 5*ρ) (hfour : 1 ≤ 4*ρ)
    (hgap : 4*ρ-1-δ ≤ -κ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-Bc+ρ*Lc+R₀ ≤
      -κ*c-E-Bc := by
  have hfirst : (1-ρ)*max (c-d) 0-δ*c ≤ -κ*c-(δ-κ)*p := by
    by_cases hcd : d ≤ c
    · rw [max_eq_left (sub_nonneg.mpr hcd)]
      have h1 := mul_nonneg (show 0 ≤ ρ+δ-1-κ by linarith) (sub_nonneg.mpr hcd)
      have h2 := mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hpD)
      nlinarith
    · rw [max_eq_right (show c-d ≤ 0 by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hpC)]
  have hnum := mul_le_mul_of_nonneg_left hLc hρ
  have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
  have hrad := mul_le_mul_of_nonneg_left hRp (show 0 ≤ 4*ρ-1 by linarith)
  have hrest := mul_nonpos_of_nonpos_of_nonneg (show 4*ρ-1-δ+κ ≤ 0 by linarith) hp
  nlinarith

/-- The second allocation has the stronger direct delta loss. -/
theorem second_common_saving (δ b g t : ℝ) (hg : g ≤ b) :
    g-t-(1+δ)*b ≤ -δ*b-t := by nlinarith

theorem both_common_saving (ρ δ κ c d p R E Bc Lc R₀ b g t : ℝ)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hδ : κ ≤ δ)
    (hsum : 1 + κ ≤ ρ + δ) (hfive : 1 ≤ 5*ρ) (hfour : 1 ≤ 4*ρ)
    (hgap : 4*ρ-1-δ ≤ -κ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hb : 0 ≤ b) (hg : g ≤ b) (hE : 0 ≤ E) (hB : 0 ≤ Bc) (ht : 0 ≤ t) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-Bc+ρ*Lc+R₀+g-t-(1+δ)*b ≤
      -κ*(c+b) := by
  have h1 := first_common_saving ρ δ κ c d p R E Bc Lc R₀
    hρ hκ hδ hsum hfive hfour hgap hp hpC hpD hRp hR₀ hLc
  have h2 := second_common_saving δ b g t hg
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hb]

/-- In the narrow high-zero range the first allocation can pay one twentieth. -/
theorem density_sum_gap (δ : ℝ) (hlo : 17/25 ≤ δ) (hhi : δ ≤ 7/10) :
    1 + 1/20 ≤ (1-10*δ/(3*(5-2*δ))) + δ := by
  have hd : 0 < 3*(5-2*δ) := by linarith
  have hpoly := mul_nonneg (show 0 ≤ 7/10-δ by linarith)
    (show 0 ≤ 120*δ-22 by linarith)
  have hf : 10*δ/(3*(5-2*δ)) ≤ δ-1/20 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

/-- Few removed slots leave both enough frequency scale and enough live width.
The constants allow one thousandth of source rounding loss. -/
theorem small_allocation_geometry (M c d b a R Lc ω err live q : ℝ)
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hsmall : c+b ≤ M/50) (hR : R ≤ c) (hLc : 0 ≤ Lc)
    (ha : a ≤ 3*M/250) (hω : ω ≤ M/1000) (herr : 0 ≤ err)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err)
    (hlive : 17*M/500-c-b-M/1000 ≤ live) :
    887*M/1000 ≤ q ∧ 13*M/1000 ≤ live := by
  have hm : max (c-d) 0 ≤ c := max_le (by linarith) hc
  constructor <;> linarith

/-- The same small-allocation range bounds the frequency above and supplies
one hundredth of its logarithmic scale in live slots. -/
theorem small_allocation_supply (M c d b a R Lc ω err live q : ℝ)
    (hc : 0 ≤ c) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hsmall : c+b ≤ M/50) (hR : R ≤ c) (hLc : Lc ≤ 5*R)
    (herr : err-ω ≤ M/1000)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err)
    (hlive : 17*M/500-c-b-M/1000 ≤ live) :
    q ≤ 1081*M/1000 ∧ q/100 ≤ live := by
  have hm : 0 ≤ max (c-d) 0 := le_max_right _ _
  have hM : 0 ≤ M := by linarith
  constructor <;> linarith

/-- The sixthpower tail and the almost-full core both retain a thousandth. -/
theorem sixthpower_split_saving (ρ v : ℝ) (hρ : 2/7 ≤ ρ) (hv : 247/250 ≤ v) :
    1/1000 ≤ (6*ρ-1)/500 ∧ 1/1000 ≤ v*(3/2800) := by
  constructor <;> linarith

/-- A uniform saving follows by separating large allocations from marked rows. -/
theorem allocation_or_marked (M removed q E base : ℝ)
    (hM : 0 ≤ M)
    (hplain : E ≤ base-removed/20)
    (hmarked : removed ≤ M/50 → 887*M/1000 ≤ q ∧
      E ≤ base-q*(3/2800)) :
    E ≤ base-19*M/20000 := by
  by_cases hsmall : removed ≤ M/50
  · obtain ⟨hq,he⟩ := hmarked hsmall
    linarith
  · have hlarge : M/50 ≤ removed := le_of_lt (lt_of_not_ge hsmall)
    linarith

/-- A reserve after the raw-row split, retaining room for analytic losses. -/
theorem allocation_or_raw_marked (M removed q E base : ℝ)
    (hM : 0 ≤ M)
    (hplain : E ≤ base-removed/20)
    (hmarked : removed ≤ M/50 → 887*M/1000 ≤ q ∧
      E ≤ base-q/1000) :
    E ≤ base-887*M/1000000 := by
  by_cases hsmall : removed ≤ M/50
  · obtain ⟨hq,he⟩ := hmarked hsmall
    linarith
  · have hlarge : M/50 ≤ removed := le_of_lt (lt_of_not_ge hsmall)
    linarith

/-- The source frequency loses at most twice the common allocation norm,
in addition to the amplifier and the controlled frequency loss. -/
theorem raw_frequency_lower (M c d b a R Lc ω err q : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hR : R ≤ c) (hLc : 0 ≤ Lc)
    (ha : a ≤ M/75) (hω : ω ≤ M/1000) (herr : 0 ≤ err)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err) :
    919*M/1000-2*(c+b) ≤ q := by
  have hm : max (c-d) 0 ≤ c := max_le (by linarith) hc
  linarith

/-- Removing a sixth power of norm at most U^(1/250) preserves the
frequency lower bound required by the continuous allocation ledger. -/
theorem small_core_frequency_lower (M removed q qcore : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed)
    (hq : 919*M/1000-2*removed ≤ q)
    (hcore : (122/125)*q ≤ qcore) :
    1121*M/1250-2*removed ≤ qcore := by linarith

/-- Coupled radical loss and asymmetric marked moments cover every split of
the conserved width between common, frozen, and surviving slots. -/
theorem continuous_marked_ledger (M removed frozen live q δ : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed) (hf : 0 ≤ frozen) (hl : 0 ≤ live)
    (hδ : 519/4550 ≤ δ)
    (hsupply : 33*M/1000 ≤ removed+frozen+live)
    (hq : 1121*M/1250-2*removed ≤ q) :
    37*M/10000 ≤ (519/4550)*removed+δ*frozen+(224/1755)*min live (13*q/400) := by
  have hdf : (519/4550)*frozen ≤ δ*frozen := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ δ-519/4550) hf]
  by_cases hs : live ≤ 13*q/400
  · rw [min_eq_left hs]
    linarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hs))]
    linarith

/-- The large-root tail covers the same reserve in the narrow high-zero range. -/
theorem continuous_tail_ledger (M removed frozen q δ ρ : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed) (hf : 0 ≤ frozen) (hq0 : 0 ≤ q)
    (hδ : 0 ≤ δ) (hρ : 19/54 ≤ ρ)
    (hq : 1121*M/1250-2*removed ≤ q) :
    37*M/10000 ≤ (519/4550)*removed+δ*frozen+(6*ρ-1)*q/250 := by
  have hprod := mul_nonneg (by linarith : 0 ≤ 6*ρ-1-10/9) hq0
  have hdf := mul_nonneg hδ hf
  nlinarith

theorem continuous_reserve_after_losses (M E base loss : ℝ)
    (hM : 0 ≤ M) (hE : E ≤ base-37*M/10000+loss)
    (hloss : loss ≤ M/20000) : E ≤ base-73*M/20000 := by linarith

end
end MarkedAllocationReserve
#print axioms MarkedAllocationReserve.first_common_saving
#print axioms MarkedAllocationReserve.both_common_saving
#print axioms MarkedAllocationReserve.density_sum_gap
#print axioms MarkedAllocationReserve.small_allocation_geometry
#print axioms MarkedAllocationReserve.allocation_or_marked

#print axioms MarkedAllocationReserve.small_allocation_supply
#print axioms MarkedAllocationReserve.sixthpower_split_saving
#print axioms MarkedAllocationReserve.allocation_or_raw_marked

#print axioms MarkedAllocationReserve.continuous_marked_ledger
#print axioms MarkedAllocationReserve.continuous_tail_ledger
#print axioms MarkedAllocationReserve.continuous_reserve_after_losses
#print axioms MarkedAllocationReserve.raw_frequency_lower
#print axioms MarkedAllocationReserve.small_core_frequency_lower
