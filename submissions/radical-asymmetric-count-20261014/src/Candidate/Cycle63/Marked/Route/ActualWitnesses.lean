import Candidate.Cycle63.Marked.Route.ActualWeightedCount

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle63ActualWeighted
open CenteredMomentDetectorPlainFiberSource CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorFiberPartition LocalMoment Cycle63MarkedAssembly
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}
variable {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {lo hi U : ℝ}

def NaturalBatch.retracted (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (u₀ : B.rows) : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U :=
  { B with
    family := fun u=>B.family (supportedRowRetraction B.rows u₀ u).val
    idealCoefficients := by
      intro u hu j I
      simpa only [supportedRowRetraction,dite_eq_left hu] using B.idealCoefficients u hu j I
    elementCoefficients := by
      intro u hu j n
      simpa only [supportedRowRetraction,dite_eq_left hu] using B.elementCoefficients u hu j n
    plainIdentity := by
      intro u hu j s hs
      simpa only [supportedRowRetraction,dite_eq_left hu] using B.plainIdentity u hu j s hs }

theorem NaturalBatch.retracted_family (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (u₀ : B.rows) (u : FreeRow) (hu : u∈B.rows) :
    (B.retracted u₀).family u=B.family u := by
  simp only [NaturalBatch.retracted,supportedRowRetraction,dite_eq_left hu]

/-- Witnesses are required only on the actual finite row population. The
retraction gives the ambient interface without inventing zeros off that set. -/
def NaturalBatch.retracted_witnesses
    (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U) (u₀ : B.rows)
    {a ε T allowance binWidth : ℝ} {i : ℕ}
    (witness : ∀bin : BinLabel B.slots ((2*a-1)/2) binWidth,
      ∀u : B.rows,SupportedWitness (B.family u.val) U a ε
        (binCutoff B.slots B.widths a binWidth bin) T allowance i) :
    ∀bin : BinLabel (B.retracted u₀).slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness ((B.retracted u₀).family u) U a ε
        (binCutoff (B.retracted u₀).slots (B.retracted u₀).widths a binWidth bin) T allowance i :=
  fun bin u=>witness bin (supportedRowRetraction B.rows u₀ u)

/-- The adaptive detector witnesses are constructed from actual buffered zero
maxima, uniformly for every amplitude bin, including unused rounded bins. -/
theorem actual_adaptive_supported_witnesses
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤Z → ∀d : ℝ,dmin≤d → d≤dmax →
      ∀{Row : Type}(χ : Row→Label→Character)(hχ : ∀u j,(χ u j).residue≠1),
      ∀(a binWidth : ℝ)(i : ℕ),i≤I → 17/25≤2*a-1 → 2*a-1≤7/10 →
      0<binWidth → binWidth≤(2*a-1)/2 →
      (∀u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i:ℕ)*Z^τ)) →
      (∀u j,(χ u j).modulus.absNorm≤Z^d) →
      ∀(slots : Finset Slot)(widths : Slot→ℝ),(∀s∈slots,0≤widths s) →
      0<(∑s∈slots,widths s) →
      Nonempty (∀bin : BinLabel slots ((2*a-1)/2) binWidth,
        ∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hsource⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row χ hχ a binWidth i hi ha0 ha hbin hbin' hnext hcurrent hmod
    slots widths hw hL
  have hbinWitness (bin : BinLabel slots ((2*a-1)/2) binWidth) :
      Nonempty (∀u,SupportedWitness (χ u) (Z^d) a ε (binCutoff slots widths a binWidth bin)
        (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
    have hcut := binCutoff_bounds slots widths a binWidth ha0 ha hbin hbin' hw hL bin
    exact hsource Z hZ d hd hd' χ hχ a i hi (by linarith) (by linarith) hnext hcurrent hmod
      (binCutoff slots widths a binWidth bin) hcut.1 hcut.2
  exact ⟨fun bin=>Classical.choice (hbinWitness bin)⟩


theorem actual_weighted_from_buffered_maxima
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (anchor j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (anchor j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth η : ℝ)
    (dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<η)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤1/1000) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃meshmax : ℝ,0< meshmax ∧ ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi (Z^d),
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →
      17/25≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ meshmax → binWidth≤(2*a-1)/2 →
      (∀s∈B.slots,B.widths s≤ mesh) → 0<(∑s∈B.slots,B.widths s) →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈B.slots,|B.relativeHeight s|≤height) → (∀u∈B.rows,|B.commonHeight u|≤height) →
      ∀hχ : ∀u∈B.rows,∀j,(B.family u j).residue≠1,
      (∀u : B.rows,HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : B.rows,a≤HeckeDetectorZeros.zeroMaximum (B.family u.val) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈B.rows,∀j,(B.family u j).modulus.absNorm≤Z^d) →
      (∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖≤((Z^d)^(B.widths s))^((2*a-1)/2+binWidth)) →
      (∑u∈B.rows,‖∏s∈B.slots,B.Q u s‖^2)≤
        C*(1+height)^J*
        (Z^d)^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈B.slots,B.widths s)-
          (7/45)*VariableSupply.chosenWidth (∑s∈B.slots,B.widths s)+
          155*ε+mesh+εm+2*binWidth*(∑s∈B.slots,B.widths s)+η) := by
  obtain ⟨meshmax,hmeshmax,J,C,hC,hfield⟩ := actual_weighted_row_sum_uniform (Slot:=Slot) M H hH
    base anchor bad hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth η hWs hW hbΦ hrad
    hbin hη hΔ0 hΔ hεm hβ hκβ
  obtain ⟨Z₀,hwitness⟩ := actual_adaptive_supported_witnesses (Label:=Label) (Slot:=Slot)
    dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε he he' hκw hκw' hηw hbudget
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hfield
  have hlarge : ∀ᶠ Z : ℝ in atTop,U₀≤Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀)
  refine ⟨meshmax,hmeshmax,J,C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop Z₀,eventually_gt_atTop (1:ℝ)] with Z hlarge hZ₀ hZ
  refine ⟨hZ,?_⟩
  intro d hd hd' B a mesh height i hi ha0 ha hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
    hχ hnext hcurrent hmod hQ
  have hthreshold : U₀≤Z^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hd)
  have hfield := hU₀ (Z^d) hthreshold
  by_cases hne : B.rows.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    obtain ⟨w⟩ := hwitness Z hZ₀ d hd hd' (fun u:B.rows=>B.family u.val)
      (fun u=>hχ u.val u.property) a binWidth i hi ha0 ha hbin hbin' hnext hcurrent
      (fun u=>hmod u.val u.property) B.slots B.widths
      (fun s hs=>(B.widthsPositive s hs).le) hL
    let urow : B.rows := ⟨u₀,hu₀⟩
    exact hfield.2 (B.retracted urow) a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh height i
      ha0 ha hε.le hεsmall hmesh hmeshmax' hbin' hwm hL hh hf hv hchoice
      (B.retracted_witnesses urow w) hQ
  · have hempty : B.rows=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty,Finset.sum_empty]
    have hUp : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    positivity

end OAI.SevenEighths.Cycle63ActualWeighted
#print axioms OAI.SevenEighths.Cycle63ActualWeighted.actual_adaptive_supported_witnesses
#print axioms OAI.SevenEighths.Cycle63ActualWeighted.actual_weighted_from_buffered_maxima
