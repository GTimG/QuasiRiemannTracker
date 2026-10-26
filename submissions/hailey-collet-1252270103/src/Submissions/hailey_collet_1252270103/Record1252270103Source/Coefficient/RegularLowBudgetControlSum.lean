/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Sum the actual LOW cell budgets without separate radius and weight maxima.
The cellwise scalar payment is retained until after the profile/mass bound. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowBudgetControlMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowBudgetControl
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths Filter HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open OAI.SevenEighths.Record1252270103Low
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O

/-- This is the collected-cell RHS, with erasure and attained A kept paired
with this cell's M, caps and missing exponent. -/
def cellBudget (rayCount : ℕ) (a b : ℝ) (ha : 0<a) (TP : Finset (ℕ×ℕ))
    (CP DP Craw : ℝ) (degreeP : ℕ) (Φ : 𝓢(ℝ,ℂ)) (p : Profiles a b)
    (Z t height εsource loss δ Brestore εmask : ℝ) (R : Ideal O)
    (M C₁ C₂ A erasure missing : ℝ) : ℝ :=
  erasure*(128*(rayCount:ℝ)^2*
    ((holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
      eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*
      (Craw*Z^loss*A*(positiveWindow b C₁*(positiveWindow b C₂*
        globalRawBudget CP DP TP degreeP Φ
          (normPowerProfile (p.profile 0) a b ha (p.support 0) ((p.profile 0).smooth ⊤) t)
          (normPowerProfile (p.profile 1) a b ha (p.support 1) ((p.profile 1).smooth ⊤) t)
          t height Z M εsource)))))*((∏I∈CompletedGauss.primeSupport R,I).absNorm:ℝ)^εmask*
    Z^missing

/-- One constant pays every finite set of cells of the fixed cardinal bound.
The scalar premise is an actual coefficient/erasure exponent payment, not an
energy estimate. In particular M and A are never maximized independently. -/
theorem global_raw_restored_budget_sum (rayCount Kcells : ℕ)
    (a b : ℝ) (ha : 0<a) (TP : Finset (ℕ×ℕ))
    (CP DP Craw : ℝ) (hCP : 0≤CP) (hDP : 0≤DP) (hCraw : 0≤Craw)
    (degreeP : ℕ) (Φ : 𝓢(ℝ,ℂ))
    (Bscale Bmask εmask δ Brestore εwindow : ℝ)
    (hBscale : 0≤Bscale) (hεmask : 0≤εmask) (hεwindow : 0<εwindow) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(κ : Type)[DecidableEq κ](cells : Finset κ),cells.card≤Kcells →
    ∀(p : Profiles a b)(t height εsource loss factor Cslot target : ℝ)(N : ℕ),
      0≤height → 0≤factor → 0≤Cslot →
    ∀(R : Ideal O),R≠0 → (R.absNorm:ℝ)≤Z^Bmask →
    ∀(M C₁ C₂ A erasure missing : κ→ℝ),
      (∀i∈cells,C₁ i≤Z^Bscale) → (∀i∈cells,C₂ i≤Z^Bscale) →
      (∀i∈cells,0≤A i) → (∀i∈cells,0≤erasure i) →
      (∀i∈cells,A i*erasure i*Z^(M i+missing i)≤factor*Cslot^N*Z^target) →
      (∑i∈cells,cellBudget rayCount a b ha TP CP DP Craw degreeP Φ p
        Z t height εsource loss δ Brestore εmask R (M i) (C₁ i) (C₂ i) (A i) (erasure i) (missing i))≤
      C*(p.control S)^2*(1+|t|+height)^J*factor*Cslot^N*
        Z^(target+εsource+loss+2*δ+Bmask*εmask+εwindow) := by
  obtain ⟨J,S,Cm,hCm,hbudget⟩ := global_raw_restored_budget a b ha TP CP DP Craw hCP hDP hCraw
    degreeP Φ Bscale Bmask εmask δ Brestore εwindow hBscale hεmask hεwindow
  let rayCost : ℝ := 128*(rayCount:ℝ)^2
  have hray : 0≤rayCost := by dsimp only [rayCost];positivity
  have hK : 0≤(Kcells:ℝ)*rayCost*Cm := by positivity
  refine ⟨J,S,1+(Kcells:ℝ)*rayCost*Cm,by linarith only [hK],?_⟩
  filter_upwards [hbudget] with Z hz
  refine ⟨hz.1,?_⟩
  intro κ _ cells hcard p t height εsource loss factor Cslot target N hh hfactor hCslot
    R hR hRcap M C₁ C₂ A erasure missing hC₁ hC₂ hA herasure hscalar
  have hZ : 0<Z := zero_lt_one.trans hz.1
  let extra := εsource+loss+2*δ+Bmask*εmask+εwindow
  let rest := (p.control S)^2*(1+|t|+height)^J*factor*Cslot^N*Z^(target+extra)
  have hrest : 0≤rest := by dsimp only [rest];positivity
  have hcell (i : κ) (hi : i∈cells) :
      cellBudget rayCount a b ha TP CP DP Craw degreeP Φ p Z t height εsource loss δ Brestore εmask R
        (M i) (C₁ i) (C₂ i) (A i) (erasure i) (missing i)≤rayCost*Cm*rest := by
    have hb := hz.2 p t height (M i) εsource loss (C₁ i) (C₂ i) hh (hC₁ i hi) (hC₂ i hi) R hR hRcap
    have hexp : M i+εsource+loss+2*δ+Bmask*εmask+εwindow=M i+extra := by
      dsimp only [extra]
      ring
    rw [hexp] at hb
    have hweight : 0≤rayCost*A i*erasure i*Z^(missing i) := by
      have ha := hA i hi
      have he := herasure i hi
      positivity
    have hweighted := mul_le_mul_of_nonneg_left hb hweight
    have hpowers : Z^(missing i)*Z^(M i+extra)=Z^(M i+missing i)*Z^extra := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
      congr 1
      ring
    calc
      _≤(rayCost*A i*erasure i*Z^(missing i))*
          (Cm*(p.control S)^2*(1+|t|+height)^J*Z^(M i+extra)) := by
        convert hweighted using 1 <;> dsimp only [cellBudget,rayCost] <;> ring
      _=(rayCost*Cm*(p.control S)^2*(1+|t|+height)^J*Z^extra)*
          (A i*erasure i*Z^(M i+missing i)) := by
        calc
          _=(rayCost*Cm*(p.control S)^2*(1+|t|+height)^J*A i*erasure i)*
              (Z^(missing i)*Z^(M i+extra)) := by ring
          _=_ := by rw [hpowers];ring
      _≤(rayCost*Cm*(p.control S)^2*(1+|t|+height)^J*Z^extra)*
          (factor*Cslot^N*Z^target) :=
        mul_le_mul_of_nonneg_left (hscalar i hi) (by positivity)
      _=rayCost*Cm*rest := by
        dsimp only [rest]
        rw [Real.rpow_add hZ target extra]
        ring
  have hsum := Finset.sum_le_sum hcell
  have hcard' : (cells.card:ℝ)≤(Kcells:ℝ) := by exact_mod_cast hcard
  have htotal : (∑i∈cells,cellBudget rayCount a b ha TP CP DP Craw degreeP Φ p
      Z t height εsource loss δ Brestore εmask R (M i) (C₁ i) (C₂ i) (A i) (erasure i) (missing i))≤
      (Kcells:ℝ)*(rayCost*Cm*rest) := by
    apply hsum.trans
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      mul_le_mul_of_nonneg_right hcard' (mul_nonneg (mul_nonneg hray hCm.le) hrest)
  have hfinal := htotal.trans (show (Kcells:ℝ)*(rayCost*Cm*rest)≤
      (1+(Kcells:ℝ)*rayCost*Cm)*rest by nlinarith only [hrest])
  convert hfinal using 1 <;> dsimp only [rest,extra] <;> ring

end
end QRH.Record1252270103Source.RegularLowBudgetControl
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.global_raw_restored_budget_sum
