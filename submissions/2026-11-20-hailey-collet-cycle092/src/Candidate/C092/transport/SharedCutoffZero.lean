/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Choose the attaining zero before the list of cutoffs. Every supported pair
then uses that same label and zero, even when its dyads and phases change. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
set_option autoImplicit false
namespace QRH.Cycle092.SharedCutoffZero
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorZeros HeckeDetectorSupportedWitness

theorem simultaneous_cutoffs (dmin dmax τ ε mesh κ loss : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0<τ)
    (hτ₀ : τ<dmin/2) (hτH : 4*τ<dmin*loss) (hε : 0<ε)
    (hmesh : 0<mesh) (hmesh' : mesh<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hloss : 0≤loss)
    (hb : 12*mesh*(22+2)+8*κ+2*loss≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z, Z₀≤Z → ∀ d, dmin≤d → d≤dmax →
      ∀ {Label : Type*} [Fintype Label] (χ : Label → Character) (hn : ∀ l,(χ l).residue ≠ 1)
        (a : ℝ) (i : ℕ), i≤I → 51/100 < a → a≤1 →
        zeroMaximum χ hn (3*(i+1:ℕ)*Z^τ)<a+2*mesh →
        a ≤ zeroMaximum χ hn ((3*i:ℕ)*Z^τ) →
        (∀ j, ((χ j).modulus.absNorm:ℝ) ≤ Z^d) →
        ∃ j : Label, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧
          ρ.re=zeroMaximum χ hn ((3*i:ℕ)*Z^τ) ∧ |ρ.im| ≤ (3*i:ℕ)*Z^τ ∧
          ∀ cutoff : ℝ, 1≤cutoff → cutoff≤3/2 →
          ∃ w : SupportedWitness χ (Z^d) a ε cutoff (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
            w.label=j ∧ w.zero=ρ := by
  obtain ⟨Z₀,hsrc⟩ := HeckeDetectorSimultaneousSupport.from_actual_zero dmin dmax τ ε mesh κ loss I
    hdmin hdmax hτ hτ₀ hτH hε hmesh hmesh' hκ hκ' hloss hb
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Label _ χ hn a i hi ha ha' hnext hcurrent hcond
  obtain ⟨j,ρ,hzero,him,hmax⟩ := maximum_attained χ hn _ (ha.trans_le hcurrent)
  have hra : a≤ρ.re := hcurrent.trans hmax.ge
  refine ⟨j,ρ,hzero,hmax,him,?_⟩
  intro cutoff hmin hmax'
  obtain ⟨b,hb',k,hk,v,r,m,hv,hl,hr,hr₀,hr₁,hm₀,hm₁,hm,hM,hS⟩ := hsrc Z hZ d hd hd' χ hn a i hi ha.le ha' hnext
    j (hcond j) ρ hzero hra him cutoff hmin hmax'
  exact ⟨⟨⟨j,ρ,hzero,hra,him,⟨b,Finset.mem_range.mp hb'⟩,⟨k,Finset.mem_range.mp hk⟩,
    v,r,m,hv,hl,hr,hr₀,hr₁,hm₀,hm₁,hM,hS⟩,hm⟩,rfl,rfl⟩

#print axioms simultaneous_cutoffs
end
end QRH.Cycle092.SharedCutoffZero
