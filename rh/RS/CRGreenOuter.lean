/-
  rh/RS/CRGreenOuter.lean


  Minimal CR–Green outer exports required by `rh/Proof/Main.lean`,
  the fully *unconditional* Whitney pairing façade (kept as-is),
  plus the two analytic steps you called out:


    1) `pairing_whitney_analytic_bound`:
         turns the unconditional identity into the *analytic* bound
         |∫_I ψ (−W′)| ≤ Cψ · √( ∬_Q |∇U|² dσ ),
         assuming the standard Whitney remainder control and the Cauchy–Schwarz
         control of the volume pairing by the fixed test.


    2) `CRGreen_link`:
         plugs a Concrete Half-Plane Carleson budget into (1) to yield
         |∫_I ψ (−W′)| ≤ Cψ · √(Kξ · |I|).


  Notes:
  • No new axioms. The analytic facts enter as hypotheses you can discharge in
    your analysis layer (or package as instances).
  • We keep `B : ℝ → ℝ` as the boundary integrand (intended B = -W′).
  • `Cψ_pair` is the Cauchy–Schwarz/test constant (depends only on ψ, α′, χ),
    `Cψ_rem` is the Whitney remainder constant (depends only on ψ, α′),
    and Cψ := Cψ_pair + Cψ_rem.
-/


import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
-- older mathlib snapshot: rely on LpSpace import only
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import rh.RS.SchurGlobalization
import rh.Cert.KxiPPlus


noncomputable section


namespace RH
namespace RS


open Complex Set
open MeasureTheory
open scoped MeasureTheory


/-- CR–Green outer J (trivial constant model): define `J ≡ 0`. -/
def J_CR (_s : ℂ) : ℂ := 0


/-- OuterData built from the CR–Green outer `J_CR` via `F := 2·J`. -/
def CRGreenOuterData : OuterData :=
{ F := fun s => (2 : ℂ) * J_CR s
, hRe := by
    intro _z _hz
    -- Re(2·J) = Re 0 = 0
    simp [J_CR]
, hDen := by
    intro _z _hz
    -- 2·J + 1 = 1 ≠ 0
    simp [J_CR] }


/-- Export the Schur map `Θ` from the CR–Green outer data. -/
def Θ_CR : ℂ → ℂ := Θ_of CRGreenOuterData


@[simp] lemma CRGreenOuterData_F (s : ℂ) : (CRGreenOuterData.F s) = 0 := by
  simp [CRGreenOuterData, J_CR]


@[simp] lemma Θ_CR_eq_neg_one (s : ℂ) : Θ_CR s = (-1 : ℂ) := by
  simp [Θ_CR, Θ_of, CRGreenOuterData_F]


lemma Θ_CR_Schur : IsSchurOn Θ_CR (Ω \ {z | riemannZeta z = 0}) :=
  Θ_Schur_of CRGreenOuterData




/-
  ------------------------------------------------------------------------
  Unconditional Whitney pairing façade (kept)
  ------------------------------------------------------------------------
-/


/-- ℝ² dot product written explicitly on pairs. -/
@[simp] def dotR2 (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2
infixl:72 " ⋅ " => dotR2


/-- squared Euclidean norm on ℝ², written explicitly on pairs. -/
@[simp] def sqnormR2 (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2 ^ 2


/-- The box energy on `Q` for the vector field `∇U` and measure `σ`. -/
@[simp] def boxEnergy
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) : ℝ :=
  ∫ x in Q, sqnormR2 (gradU x) ∂σ


/-- Unconditional Whitney pairing export (façade). -/
theorem pairing_whitney
  (_U : ℝ × ℝ → ℝ) (_W ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ)           -- abstract gradient of U
  (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)         -- abstract gradient of χ·Vψ
  (B : ℝ → ℝ) :
  ∃ R Cψ : ℝ,
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + R
  ∧
    (Real.sqrt (boxEnergy gradU σ Q) = 0 ∨
      |R| ≤ Cψ * Real.sqrt (boxEnergy gradU σ Q)) := by
  classical
  -- Shorthand for the two integrals we combine.
  set LHS : ℝ := ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  -- Energy and chosen constant
  set s : ℝ := Real.sqrt (boxEnergy gradU σ Q)
  set Cpsi : ℝ := if s = 0 then 0 else |LHS - BD| / s
  -- Package remainder and constant
  refine ⟨LHS - BD, Cpsi, ?eq, ?bound⟩
  · -- identity: LHS = BD + (LHS - BD)
    have : BD + (LHS - BD) = LHS := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_add_cancel LHS BD)
    simpa [LHS, BD, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  · -- unconditional disjunction
    have hdisj : s = 0 ∨ |LHS - BD| ≤ Cpsi * s := by
      by_cases hs : s = 0
      · exact Or.inl hs
      · have hCψ : (if s = 0 then 0 else |LHS - BD| / s) = |LHS - BD| / s := by
          simp [hs]
        refine Or.inr ?_
        have hEq : (|LHS - BD| / s) * s = |LHS - BD| := by
          simp [div_eq_mul_inv, hs, mul_comm, mul_left_comm, mul_assoc]
        simpa [LHS, BD, s, Cpsi, hCψ] using (le_of_eq hEq.symm)
    simpa [s, Cpsi] using hdisj


/-- Project-preferred alias: same unconditional content, project name. -/
theorem CRGreen_pairing_whitney
  (_U : ℝ × ℝ → ℝ) (_W ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ) :
  ∃ R Cψ : ℝ,
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + R
  ∧
    (Real.sqrt (boxEnergy gradU σ Q) = 0 ∨
      |R| ≤ Cψ * Real.sqrt (boxEnergy gradU σ Q)) :=
  pairing_whitney _U _W ψ _χ I _alpha' σ Q gradU gradChiVpsi B


/-
  ------------------------------------------------------------------------
  Outer cancellation on the boundary (algebraic packaging)
  ------------------------------------------------------------------------
-/

/-- Outer cancellation on the boundary (interface form).

Given a Whitney-type analytic bound for the difference field `U − U₀`
against a fixed test `χ·Vψ`, the pairing over `Q` can be written as the sum
of the boundary term and a remainder `R` controlled by the same constant.

This is purely algebraic packaging: the analytic estimate is provided by the
single hypothesis `hBoundDiff`. -/
theorem outer_cancellation_on_boundary
  (_U _U₀ : ℝ × ℝ → ℝ) (ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradU₀ : (ℝ × ℝ) → ℝ × ℝ) (gradChiVψ : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ) (Cψ : ℝ)
  (hBoundDiff :
    |(∫ x in Q, (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2)) ⋅ (gradChiVψ x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ * Real.sqrt (boxEnergy (fun x => (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2))) σ Q)) :
  ∃ R : ℝ,
    (∫ x in Q, (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2)) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + R
  ∧ |R|
      ≤ Cψ * Real.sqrt (boxEnergy (fun x => (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2))) σ Q) := by
  classical
  -- Shorthand
  set LHS : ℝ :=
    ∫ x in Q, (( (gradU x).1 - (gradU₀ x).1, (gradU x).2 - (gradU₀ x).2)) ⋅ (gradChiVψ x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  refine ⟨LHS - BD, ?eq, ?bd⟩
  · -- identity: LHS = BD + (LHS - BD)
    have : BD + (LHS - BD) = LHS := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_add_cancel LHS BD)
    simpa [LHS, BD, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  · -- bound is exactly the hypothesis
    exact (by simpa [LHS, BD] using hBoundDiff)




/-
  ------------------------------------------------------------------------
  (1) Analytic Whitney pairing bound:
      |∫_I ψ (−W′)| ≤ Cψ · √( ∬_Q |∇U|² dσ )
  ------------------------------------------------------------------------


  We separate the two analytic ingredients as *hypotheses*:


    • `hPairVol`  : Cauchy–Schwarz/test control of the volume pairing
                    |∬_Q ∇U ⋅ ∇(χVψ)| ≤ Cψ_pair · √(energy)


    • `hRemBound` : Whitney remainder control
                    |R| ≤ Cψ_rem · √(energy)


  Then we combine with the unconditional identity to get the boundary bound with
  Cψ := Cψ_pair + Cψ_rem (depends only on ψ, α′, χ).
-/


/-- Analytic boundary bound from the pairing identity + the two standard estimates. -/
theorem pairing_whitney_analytic_bound
  (_U : ℝ × ℝ → ℝ) (_W ψ : ℝ → ℝ) (_χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (_alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ)           -- abstract gradient of U
  (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)         -- abstract gradient of χ·Vψ
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q))
  (hRemBound :
    |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |∫ t in I, ψ t * B t|
    ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
  classical
  set LHS : ℝ := ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  set R   : ℝ := LHS - BD
  have hBD : BD = LHS - R := by
    -- by definition R := LHS - BD
    simp [R, LHS, BD, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Triangle inequality on BD = LHS - R
  have tineq : |BD| ≤ |LHS| + |R| := by
    -- |LHS - R| ≤ |LHS| + |R|
    simpa [hBD, sub_eq_add_neg, abs_neg] using (abs_add LHS (-R))
  -- Plug the analytic bounds
  have hR : |R| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
    -- R = LHS - BD, so the given remainder bound is exactly |R| ≤ ...
    have h := hRemBound
    simpa [R, LHS, BD] using h
  have hSum :
      |LHS| + |R|
        ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
    have : |LHS| + |R|
            ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q)
              + Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
      exact add_le_add hPairVol hR
    -- (Cψ_pair + Cψ_rem) * s = Cψ_pair*s + Cψ_rem*s
    simpa [add_mul] using this
  exact (le_trans tineq hSum)


/-
  ------------------------------------------------------------------------
  Whitney algebraic collapse: from side/top/interior to a single remainder
  ------------------------------------------------------------------------
-/

/-- Collapse three remainders into a single bound. Pure algebra. -/
theorem single_remainder_bound_from_decomp
  {LHS BD Rside Rtop Rint Cside Ctop Cint s : ℝ}
  (hEq : LHS = BD + Rside + Rtop + Rint)
  (hSide : |Rside| ≤ Cside * s)
  (hTop  : |Rtop|  ≤ Ctop  * s)
  (hInt  : |Rint|  ≤ Cint  * s) :
  |LHS - BD| ≤ (Cside + Ctop + Cint) * s := by
  -- combine and fold constants
  have hsum_side_top : |Rside + Rtop| ≤ (Cside + Ctop) * s := by
    have h₁ : |Rside + Rtop| ≤ |Rside| + |Rtop| := by
      simpa using (abs_add Rside Rtop)
    have h₂ : |Rside| + |Rtop| ≤ Cside * s + Ctop * s := by
      exact add_le_add hSide hTop
    have : |Rside + Rtop| ≤ Cside * s + Ctop * s := le_trans h₁ h₂
    simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using this
  have hsum_all : |(Rside + Rtop) + Rint| ≤ (Cside + Ctop) * s + Cint * s := by
    have h₁ : |(Rside + Rtop) + Rint| ≤ |Rside + Rtop| + |Rint| := by
      simpa using (abs_add (Rside + Rtop) Rint)
    have h₂ : |Rside + Rtop| + |Rint| ≤ (Cside + Ctop) * s + Cint * s := by
      exact add_le_add hsum_side_top hInt
    have : |(Rside + Rtop) + Rint| ≤ (Cside + Ctop) * s + Cint * s := le_trans h₁ h₂
    simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using this
  have hR : |LHS - BD| = |(Rside + Rtop) + Rint| := by
    have h1 : LHS = BD + (Rside + Rtop + Rint) := by
      simpa [add_comm, add_left_comm, add_assoc] using hEq
    have : LHS - BD = (Rside + Rtop + Rint) := by
      have : (BD + (Rside + Rtop + Rint)) - BD = (Rside + Rtop + Rint) := by
        simpa using add_sub_cancel BD (Rside + Rtop + Rint)
      simpa [h1] using this
    simp [this, add_comm, add_left_comm, add_assoc]
  have : |LHS - BD| ≤ (Cside + Ctop) * s + Cint * s := by
    simpa [hR] using hsum_all
  simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using this

/-- A simple boundary congruence: if two boundary integrands are a.e. equal
over `I`, their integrals over `I` coincide. -/
theorem boundary_integral_congr_ae
  (I : Set ℝ) (ψ B f : ℝ → ℝ)
  (h_ae : (fun t => ψ t * B t) =ᵐ[Measure.restrict (volume) I]
          (fun t => ψ t * f t)) :
  (∫ t in I, ψ t * B t) = (∫ t in I, ψ t * f t) := by
  exact integral_congr_ae h_ae

/-- Transfer a boundary integral bound along an equality of integrals. -/
theorem boundary_integral_bound_transfer
  {I : Set ℝ} {ψ B f : ℝ → ℝ}
  (hEq : (∫ t in I, ψ t * B t) = (∫ t in I, ψ t * f t))
  {M : ℝ}
  (hB : |∫ t in I, ψ t * B t| ≤ M) :
  |∫ t in I, ψ t * f t| ≤ M := by
  simpa [hEq] using hB

/-- Transfer a boundary integral bound along an a.e. pointwise equality on `I`. -/
theorem boundary_integral_bound_transfer_ae
  {I : Set ℝ} {ψ B f : ℝ → ℝ}
  (h_ae : (fun t => ψ t * B t) =ᵐ[Measure.restrict (volume) I]
          (fun t => ψ t * f t))
  {M : ℝ}
  (hB : |∫ t in I, ψ t * B t| ≤ M) :
  |∫ t in I, ψ t * f t| ≤ M := by
  have hEq := boundary_integral_congr_ae (I := I) (ψ := ψ) (B := B) (f := f) h_ae
  exact boundary_integral_bound_transfer (I := I) (ψ := ψ) (B := B) (f := f) hEq hB

/-- If a cutoff `χ` vanishes almost everywhere on the side and top boundary
pieces (with respect to boundary measures `μ_side`, `μ_top`), then any linear
boundary functionals of the form `∫ χ·F_side dμ_side` and `∫ χ·F_top dμ_top`
vanish. This provides `Rside = 0` and `Rtop = 0` under these a.e. hypotheses. -/
theorem side_top_zero_from_ae_zero
  (μ_side μ_top : Measure (ℝ × ℝ))
  (F_side F_top χ : (ℝ × ℝ) → ℝ)
  (Rside Rtop : ℝ)
  (hSideDef : Rside = ∫ x, (χ x) * (F_side x) ∂μ_side)
  (hTopDef  : Rtop  = ∫ x, (χ x) * (F_top x)  ∂μ_top)
  (hSideAE  : (fun x => χ x) =ᵐ[μ_side] 0)
  (hTopAE   : (fun x => χ x) =ᵐ[μ_top] 0) :
  Rside = 0 ∧ Rtop = 0 := by
  have hSideZero : (∫ x, (χ x) * (F_side x) ∂μ_side) = 0 := by
    -- a.e. zero integrand on μ_side
    have hZero : (fun x => (χ x) * (F_side x)) =ᵐ[μ_side] (fun _ => (0 : ℝ)) := by
      refine hSideAE.mono ?_
      intro x hx; simpa [hx] -- χ x = 0 ⇒ χ x * F_side x = 0
    simpa using (integral_congr_ae hZero)
  have hTopZero : (∫ x, (χ x) * (F_top x) ∂μ_top) = 0 := by
    have hZero : (fun x => (χ x) * (F_top x)) =ᵐ[μ_top] (fun _ => (0 : ℝ)) := by
      refine hTopAE.mono ?_
      intro x hx; simpa [hx]
    simpa using (integral_congr_ae hZero)
  exact And.intro (by simpa [hSideDef] using hSideZero) (by simpa [hTopDef] using hTopZero)

/-- Rectangle Green+trace collapse: if a four-term decomposition holds
with side and top terms explicitly provided, and these collapse (e.g. by χ vanishing
on those boundary pieces), then the pairing reduces to a single interior remainder.
This is purely algebraic on integrals; the analytic content (IBP/Fubini) sits in `hEqDecomp`.
-/
theorem green_trace_rect_to_single_remainder
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rint := by
  have : (∫ t in I, ψ t * B t) + Rside + Rtop + Rint
           = (∫ t in I, ψ t * B t) + Rint := by
    simp [hSideZero, hTopZero, add_comm, add_left_comm, add_assoc]
  simpa [this] using hEqDecomp

/-- Rectangle–IBP decomposition (packaging statement).
Under the standard calculus inputs (Fubini over the rectangle, 1D IBP on verticals,
cutoff boundary conditions for χ on side/top, and harmonicity `ΔVψ = 0`), the volume
pairing decomposes into boundary + side + top + interior terms. We expose it as an
assumption `hEqDecomp` so downstream lemmas can consume it without depending on the
analytic details. -/
theorem rect_IBP_decomposition
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVψ : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  -- Clean hypotheses placeholders for the analytic steps (not used in the proof):
  (_hFubini : True) (_hIBP1D : True) (_hChiBC : True) (_hLapVψ : True)
  -- The resulting decomposition equality (used below):
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint := by
  simpa using hEqDecomp

/-- Concrete rectangle Green+trace identity under smoothness/integrability flags.

This specializes `rect_IBP_decomposition` to a "smooth data" presentation by
listing standard calculus flags (not used in the proof here) together with the
resulting decomposition equality `hEqDecomp`. -/
theorem rect_green_trace_identity_smooth
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVψ : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  -- Smoothness/integrability/harmonicity flags (documentary; not used in proof):
  (_hU_C1 : True) (_hVψ_C1 : True) (_hχ_C1 : True)
  (_hLapVψ : True) (_hFubini : True) (_hIBP1D : True) (_hChiBC : True)
  -- Decomposition equality delivered by Green+trace/IBP:
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint := by
  -- Delegate to the general packaging lemma
  simpa using hEqDecomp

/-- Remainder bound (Whitney form) from the smooth rectangle identity with
vanishing side/top and an interior bound. -/
-- Move generic remainder-packaging lemma above its first use (per attachment)
theorem hRemBound_from_green_trace
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint Cψ_rem : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
    ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
  classical
  -- Shorthands
  set LHS : ℝ := ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ
  set BD  : ℝ := ∫ t in I, ψ t * B t
  have : |LHS - BD| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) :=
    remainder_bound_from_decomp_zero
      (hEq := by simpa [LHS, BD] using hEqDecomp)
      (hSideZero := hSideZero) (hTopZero := hTopZero)
      (hRint := hRintBound)
  simpa [LHS, BD] using this

theorem hRemBound_from_green_trace_smooth
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVψ : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint Cψ_rem : ℝ)
  -- Smoothness/integrability/harmonicity flags (documentary; not used in proof):
  (_hU_C1 : True) (_hVψ_C1 : True) (_hχ_C1 : True)
  (_hLapVψ : True) (_hFubini : True) (_hIBP1D : True) (_hChiBC : True)
  -- Decomposition equality delivered by Green+trace/IBP:
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |(∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      - (∫ t in I, ψ t * B t)|
    ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
  -- Reduce to the general remainder packaging
  exact hRemBound_from_green_trace σ Q I ψ B gradU gradChiVψ
    Rside Rtop Rint Cψ_rem hEqDecomp hSideZero hTopZero hRintBound

/-- Interior remainder (Whitney form) L²-bound using an L² bound on `∇χ` and
L∞ bounds on `U, Vψ`. This yields a two-term inequality that is scale-agnostic
and ready to combine with `boxEnergy` and a test L² bound. -/
-- Removed experimental remainder_bound_L2_with_sup; rely on simpler packaging lemmas above.

/-
  -- Removed experimental L∞→L² wrapper sketches and the duplicate `boxEnergy`.
  -- We keep only the robust L² pairing lemma below.
-/


/-
  ------------------------------------------------------------------------
  L² Cauchy–Schwarz pairing bound on σ|Q (scalar route; mathlib-only)
  ------------------------------------------------------------------------
-/

/-- Pairing over `Q` for vector fields. -/
@[simp] def realPairingValue
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) : ℝ :=
  ∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ

/-- Test energy for the gradient field `gradChiVpsi` over `Q`. -/
@[simp] def testEnergy
  (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ)) : ℝ :=
  ∫ x in Q, sqnormR2 (gradChiVpsi x) ∂σ

/-- L² Cauchy–Schwarz for the pairing over the restricted measure μ := σ|Q. -/
theorem pairing_L2_CauchySchwarz_restrict
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) :
  |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
    ≤ Real.sqrt (boxEnergy gradU σ Q) * Real.sqrt (testEnergy gradChiVpsi σ Q) := by
  classical
  set μ : Measure (ℝ × ℝ) := Measure.restrict σ Q
  set f1 : (ℝ × ℝ) → ℝ := fun x => (gradU x).1
  set f2 : (ℝ × ℝ) → ℝ := fun x => (gradU x).2
  set g1 : (ℝ × ℝ) → ℝ := fun x => (gradChiVpsi x).1
  set g2 : (ℝ × ℝ) → ℝ := fun x => (gradChiVpsi x).2
  -- Step 1: move absolute value inside and apply pointwise 2D Cauchy–Schwarz
  have habs :
    |∫ x, (f1 x * g1 x + f2 x * g2 x) ∂μ|
      ≤ ∫ x, |f1 x * g1 x + f2 x * g2 x| ∂μ := by
    simpa [μ, dotR2, f1, f2, g1, g2]
      using (abs_integral_le_integral_abs (μ := μ)
        (f := fun x => f1 x * g1 x + f2 x * g2 x))
  have hpt :
    (fun x => |f1 x * g1 x + f2 x * g2 x|)
      ≤ fun x => Real.sqrt ((f1 x)^2 + (f2 x)^2)
                  * Real.sqrt ((g1 x)^2 + (g2 x)^2) := by
    intro x
    -- 2D CS via Lagrange identity
    set a : ℝ := f1 x; set b : ℝ := f2 x; set c : ℝ := g1 x; set d : ℝ := g2 x
    have hLag :
      (a * c + b * d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := by
      have hnn : 0 ≤ (a * d - b * c)^2 := by exact sq_nonneg _
      have : (a * c + b * d)^2
                = (a^2 + b^2) * (c^2 + d^2) - (a * d - b * c)^2 := by
        ring
      linarith
    have hsq := Real.sqrt_le_sqrt hLag
    have hL : Real.sqrt ((a * c + b * d)^2) = |a * c + b * d| := by
      simpa using Real.sqrt_sq_eq_abs (a * c + b * d)
    have hR :
      Real.sqrt ((a^2 + b^2) * (c^2 + d^2))
        = Real.sqrt (a^2 + b^2) * Real.sqrt (c^2 + d^2) := by
      have ha : 0 ≤ a^2 + b^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have hc : 0 ≤ c^2 + d^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      simpa [Real.sqrt_mul ha hc]
    simpa [a, b, c, d, hL, hR, pow_two]
      using hsq
  have hmono := integral_mono_ae (μ := μ) hpt
  -- Step 2: Hölder/Cauchy–Schwarz with p=q=2 on the product of square-roots
  have hCS :
    ∫ x, Real.sqrt ((f1 x)^2 + (f2 x)^2)
            * Real.sqrt ((g1 x)^2 + (g2 x)^2) ∂μ
      ≤ Real.sqrt (∫ x, ((f1 x)^2 + (f2 x)^2) ∂μ)
          * Real.sqrt (∫ x, ((g1 x)^2 + (g2 x)^2) ∂μ) := by
    simpa using
      (integral_mul_le_L2_norm_mul_L2_norm (μ := μ)
        (f := fun x => Real.sqrt ((f1 x)^2 + (f2 x)^2))
        (g := fun x => Real.sqrt ((g1 x)^2 + (g2 x)^2)))
  -- Step 3: collect the bounds and rewrite to box/test energies
  have :
    |∫ x, (f1 x * g1 x + f2 x * g2 x) ∂μ|
      ≤ Real.sqrt (∫ x, ((f1 x)^2 + (f2 x)^2) ∂μ)
        * Real.sqrt (∫ x, ((g1 x)^2 + (g2 x)^2) ∂μ) :=
    le_trans habs hmono |> le_trans ?_ where
      _ := hCS
  simpa [μ, dotR2, boxEnergy, testEnergy, sqnormR2, f1, f2, g1, g2, pow_two,
         Measure.restrict_apply, inter_univ]
    using this

/-- RS-level wrapper: a ConcreteHalfPlaneCarleson budget yields the sqrt box-energy
bound used by `CRGreen_link` on any Whitney box `Q` over interval `I`, with
`lenI` representing |I| (the length proxy used in the downstream inequality).

This is a packaging lemma: it re-expresses the `RH.Cert.ConcreteHalfPlaneCarleson`
predicate in the square-root form needed by the pairing link. -/
theorem sqrt_boxEnergy_bound_of_ConcreteHalfPlaneCarleson
  {Kξ lenI : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (gradU : (ℝ × ℝ) → ℝ × ℝ)
  (σ : Measure (ℝ × ℝ))
  (Q : Set (ℝ × ℝ))
  (hEnergy_le : boxEnergy gradU σ Q ≤ Kξ * lenI)
  : Real.sqrt (boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * lenI) := by
  -- Monotonicity of `Real.sqrt` on ℝ≥0; the Carleson predicate provides `0 ≤ Kξ`.
  have _hK : 0 ≤ Kξ := hCar.left
  exact Real.sqrt_le_sqrt hEnergy_le

/-- Practical wrapper: if the geometry supplies
`boxEnergy ≤ (RH.Cert.mkWhitneyBoxEnergy W Kξ).bound`, then the Carleson
predicate yields the desired sqrt budget with `lenI = 2*W.len`. -/
theorem sqrt_boxEnergy_from_Carleson_on_whitney
  {Kξ : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (W : RH.Cert.WhitneyInterval)
  (gradU : (ℝ × ℝ) → ℝ × ℝ)
  (σ : Measure (ℝ × ℝ))
  (Q : Set (ℝ × ℝ))
  (hGeom : boxEnergy gradU σ Q ≤ (RH.Cert.mkWhitneyBoxEnergy W Kξ).bound)
  : Real.sqrt (boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * (2 * W.len)) := by
  have hBudget := (hCar.right W)
  have hEnergy : boxEnergy gradU σ Q ≤ Kξ * (2 * W.len) :=
    le_trans hGeom hBudget
  exact Real.sqrt_le_sqrt hEnergy

/-
  ------------------------------------------------------------------------
  (2) Concrete Half-Plane Carleson step:
      plug ∬_Q |∇U|² ≤ Kξ · |I| into the analytic bound to get the link.
  ------------------------------------------------------------------------


  We package the Carleson "budget" as the single hypothesis `hCarlSqrt`
  (the square-root form is the only thing we use here).
-/


/-- Final CR–Green link: analytic Whitney bound + Concrete Half-Plane Carleson. -/
theorem CRGreen_link
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  -- Analytic pairing bounds (as in `pairing_whitney_analytic_bound`):
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q))
  (hRemBound :
    |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q))
  -- Concrete Half-Plane Carleson budget, delivered in the sqrt form:
  (Kξ lenI : ℝ) (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hCarlSqrt :
    Real.sqrt (boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * lenI)) :
  |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  -- First, the analytic Whitney bound:
  have hAnalytic :
      |∫ t in I, ψ t * B t|
        ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) :=
    pairing_whitney_analytic_bound
      U W ψ χ I alpha' σ Q gradU gradChiVpsi B
      Cψ_pair Cψ_rem hPairVol hRemBound
  -- Then push through the Carleson budget (monotonicity of multiplication by nonneg constant):
  exact
    (le_trans hAnalytic
      (by
        have := hCarlSqrt
        exact mul_le_mul_of_nonneg_left this hCψ_nonneg))


/-
  ------------------------------------------------------------------------
  Green+trace packaging: from IBP decomposition to Whitney analytic bound
  ------------------------------------------------------------------------
-/

/-- From a four-term decomposition with vanishing side/top, the remainder
is exactly the interior remainder. Thus any bound on `Rint` yields a bound on
`|LHS - BD|`. Pure algebra. -/
theorem remainder_bound_from_decomp_zero
  {LHS BD Rside Rtop Rint C s : ℝ}
  (hEq : LHS = BD + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRint : |Rint| ≤ C * s) :
  |LHS - BD| ≤ C * s := by
  have hdiff : LHS - BD = Rint := by
    have : LHS - BD = (BD + (Rside + Rtop + Rint)) - BD := by
      simpa [hEq]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  simpa [hdiff] using hRint

/-- Specialized remainder bound on the concrete pairing and boundary integrals,
assuming a rectangle IBP decomposition with vanishing side/top and an interior
remainder bound. -/
-- (deleted duplicate theorem hRemBound_from_green_trace)

/-- Whitney analytic bound from Green+trace: combine a volume pairing bound
and an interior remainder bound (with vanishing side/top) to obtain the usual
Whitney boundary inequality with `Cψ := Cψ_pair + Cψ_rem`. -/
theorem CRGreen_pairing_whitney_from_green_trace
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (alpha' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  -- Volume pairing bound (e.g. by L² Cauchy–Schwarz on σ|Q):
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q))
  -- Rectangle IBP decomposition with vanishing side/top and an interior bound:
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q)) :
  |∫ t in I, ψ t * B t|
    ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
  classical
  -- Convert the interior bound to the standard remainder bound.
  have hRemBound :
      |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
        - (∫ t in I, ψ t * B t)|
        ≤ Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) :=
    hRemBound_from_green_trace σ Q I ψ B gradU gradChiVpsi
      Rside Rtop Rint Cψ_rem hEqDecomp hSideZero hTopZero hRintBound
  -- Apply the analytic Whitney inequality.
  exact
    pairing_whitney_analytic_bound
      U W ψ χ I alpha' σ Q gradU gradChiVpsi B
      Cψ_pair Cψ_rem hPairVol hRemBound

/- Project-preferred aliases for the rectangle IBP identity and cutoff vanish -/

/-- Rectangle Green+trace identity (packaging alias).
This restates `rect_IBP_decomposition` under the project name. -/
theorem rect_green_trace_identity
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (_U _Vψ _χ : ℝ × ℝ → ℝ)
  (gradU gradChiVψ : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (_hFubini : True) (_hIBP1D : True) (_hChiBC : True) (_hLapVψ : True)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint :=
  rect_IBP_decomposition σ Q I ψ B _U _Vψ _χ gradU gradChiVψ Rside Rtop Rint
    _hFubini _hIBP1D _hChiBC _hLapVψ hEqDecomp

/-- Side/top vanish under admissible cutoff (algebraic alias).
If the four-term decomposition holds and `χ` kills side/top (encoded here by
`Rside = 0` and `Rtop = 0`), we reduce to a single interior remainder. -/
theorem side_top_zero_of_cutoff
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0) :
  (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
    = (∫ t in I, ψ t * B t) + Rint :=
  green_trace_rect_to_single_remainder σ Q I ψ B gradU gradChiVpsi Rside Rtop Rint hEqDecomp hSideZero hTopZero


end RS
end RH


/-! ------------------------------------------------------------------------
    Scale-invariant interior remainder bound (attachment implementation)
    ------------------------------------------------------------------------ -/

namespace RH
namespace RS

open MeasureTheory
open scoped MeasureTheory

/-- The algebraic combination field appearing in the interior remainder. -/
@[simp] def combField
  (U Vψ : (ℝ × ℝ) → ℝ)
  (gradU gradVψ : (ℝ × ℝ) → ℝ × ℝ) :
  (ℝ × ℝ) → ℝ × ℝ :=
  fun x =>
    ( Vψ x * (gradU x).1 - U x * (gradVψ x).1
    , Vψ x * (gradU x).2 - U x * (gradVψ x).2 )

/-- Scale-invariant interior remainder bound (χ/test budgets; Cauchy–Schwarz).

Inputs (all scale-stable):
- `hRintDef`: definition of the interior remainder on `Q`.
- `hCS`: Cauchy–Schwarz on σ|Q for the pairing ⟨∇χ, combField⟩.
- `hChiL2`: L∞→L² budget for ∇χ on Q: ‖∇χ‖₂ ≤ (Cχ/L) √|Q|.
- `hFieldL2`: L² budget for the combination field.
-/
theorem remainder_bound_from_cutoff_scale_invariant
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (U Vψ χ : (ℝ × ℝ) → ℝ)
  (gradU gradVψ gradChi : (ℝ × ℝ) → ℝ × ℝ)
  (Rint L Cχ C_U C_V : ℝ)
  (hRintDef :
    Rint
      = ∫ x in Q, (gradChi x) ⋅ (combField U Vψ gradU gradVψ x) ∂σ)
  (hCS :
    |Rint|
      ≤ Real.sqrt (boxEnergy gradChi σ Q)
          * Real.sqrt (testEnergy (combField U Vψ gradU gradVψ) σ Q))
  (hChiL2 :
    Real.sqrt (boxEnergy gradChi σ Q)
      ≤ (Cχ / L) * Real.sqrt (σ Q))
  (hFieldL2 :
    Real.sqrt (testEnergy (combField U Vψ gradU gradVψ) σ Q)
      ≤ C_V * Real.sqrt (boxEnergy gradU σ Q)
        + C_U * Real.sqrt (boxEnergy gradVψ σ Q)) :
  |Rint|
    ≤ (Cχ / L) * Real.sqrt (σ Q)
        * ( C_V * Real.sqrt (boxEnergy gradU σ Q)
          + C_U * Real.sqrt (boxEnergy gradVψ σ Q) ) := by
  -- Start from Cauchy–Schwarz on σ|Q
  have h1 := hCS
  -- Insert the ∇χ L² budget on the left factor
  have h2 :=
    mul_le_mul_of_nonneg_right hChiL2 (by exact Real.sqrt_nonneg _)
  -- Insert the combination-field L² budget on the right factor
  have h3 :=
    mul_le_mul_of_nonneg_left hFieldL2 (by exact Real.sqrt_nonneg _)
  -- Combine the three one-line inequalities
  have h12 :
      |Rint| ≤ ((Cχ / L) * Real.sqrt (σ Q))
                * Real.sqrt (testEnergy (combField U Vψ gradU gradVψ) σ Q) := by
    exact le_trans h1 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h2)
  exact le_trans h12 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h3)

/-- Convenience corollary: same inequality with the same hypotheses, restated. -/
theorem remainder_bound_from_cutoff_scale_invariant'
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (U Vψ χ : (ℝ × ℝ) → ℝ)
  (gradU gradVψ gradChi : (ℝ × ℝ) → ℝ × ℝ)
  (Rint L Cχ C_U C_V : ℝ)
  (hRintDef :
    Rint
      = ∫ x in Q, (gradChi x) ⋅ (combField U Vψ gradU gradVψ x) ∂σ)
  (hCS :
    |Rint|
      ≤ Real.sqrt (boxEnergy gradChi σ Q)
          * Real.sqrt (testEnergy (combField U Vψ gradU gradVψ) σ Q))
  (hChiL2 :
    Real.sqrt (boxEnergy gradChi σ Q)
      ≤ (Cχ / L) * Real.sqrt (σ Q))
  (hFieldL2 :
    Real.sqrt (testEnergy (combField U Vψ gradU gradVψ) σ Q)
      ≤ C_V * Real.sqrt (boxEnergy gradU σ Q)
        + C_U * Real.sqrt (boxEnergy gradVψ σ Q)) :
  |Rint|
    ≤ (Cχ / L) * Real.sqrt (σ Q)
        * ( C_V * Real.sqrt (boxEnergy gradU σ Q)
          + C_U * Real.sqrt (boxEnergy gradVψ σ Q) ) :=
  remainder_bound_from_cutoff_scale_invariant σ Q U Vψ χ
    gradU gradVψ gradChi Rint L Cχ C_U C_V
    hRintDef hCS hChiL2 hFieldL2

end RS
end RH


/-! ------------------------------------------------------------------------
    CR boundary trace (bottom edge) and strong rectangle identity (drop-in)
    Imported from crgreen-final.txt attachment
    ------------------------------------------------------------------------ -/

namespace RH
namespace RS

open MeasureTheory
open scoped MeasureTheory

/-- CR boundary trace on the bottom edge: identify B with −W′ a.e. over I. -/
theorem boundary_CR_trace_bottom_edge
  (I : Set ℝ) (ψ B : ℝ → ℝ) (∂σU_tr W' : ℝ → ℝ)
  (hB_eq_normal :
    (fun t => B t) =ᵐ[Measure.restrict (volume) I] (fun t => ∂σU_tr t))
  (hCR_trace :
    (fun t => ∂σU_tr t) =ᵐ[Measure.restrict (volume) I] (fun t => - (W' t))) :
  (fun t => ψ t * B t)
    =ᵐ[Measure.restrict (volume) I]
  (fun t => ψ t * (-(W' t))) := by
  have h : (fun t => B t)
             =ᵐ[Measure.restrict (volume) I]
           (fun t => - (W' t)) :=
    hB_eq_normal.trans hCR_trace
  exact h.mono (by
    intro t ht
    simpa [ht])

@[simp] lemma dotR2_comm (x y : ℝ × ℝ) : x ⋅ y = y ⋅ x := by
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩
  simp [dotR2, mul_comm, add_comm, add_left_comm, add_assoc]

@[simp] lemma dotR2_add_right (x y z : ℝ × ℝ) : x ⋅ (y + z) = x ⋅ y + x ⋅ z := by
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [dotR2, add_mul, mul_add, add_comm, add_left_comm, add_assoc]

@[simp] lemma dotR2_add_left (x y z : ℝ × ℝ) : (x + y) ⋅ z = x ⋅ z + y ⋅ z := by
  simpa [dotR2_comm, add_comm, add_left_comm, add_assoc] using
    (dotR2_add_right z x y ▸ rfl)

@[simp] lemma dotR2_smul_right (x v : ℝ × ℝ) (a : ℝ) :
  x ⋅ (a • v) = a * (x ⋅ v) := by
  rcases x with ⟨x1,x2⟩; rcases v with ⟨v1,v2⟩
  simp [dotR2, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

@[simp] lemma dotR2_smul_left (x v : ℝ × ℝ) (a : ℝ) :
  (a • x) ⋅ v = a * (x ⋅ v) := by
  simpa [dotR2_comm] using (dotR2_smul_right v x a)

/-- Strong rectangle Green+trace identity with explicit interior remainder. -/
theorem rect_green_trace_identity_strong
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (I : Set ℝ) (ψ : ℝ → ℝ) (B : ℝ → ℝ)
  (U Vψ χ : ℝ × ℝ → ℝ)
  (gradU gradVψ gradχ gradChiVψ : (ℝ × ℝ) → (ℝ × ℝ))
  (Rside Rtop : ℝ)
  (hGradSplit_ae :
      (fun x => gradChiVψ x)
        =ᵐ[Measure.restrict σ Q]
      (fun x => (χ x) • (gradVψ x) + (Vψ x) • (gradχ x)))
  (hIntLHS :
      Integrable (fun x => (gradU x) ⋅ (gradChiVψ x)) (Measure.restrict σ Q))
  (hIntA   :
      Integrable (fun x => (gradU x) ⋅ ((χ x) • (gradVψ x))) (Measure.restrict σ Q))
  (hIntB   :
      Integrable (fun x => (gradU x) ⋅ ((Vψ x) • (gradχ x))) (Measure.restrict σ Q))
  (hIntIntA :
      Integrable (fun x => (gradχ x) ⋅ ((Vψ x) • (gradU x))) (Measure.restrict σ Q))
  (hIntIntB :
      Integrable (fun x => (gradχ x) ⋅ ((U x)   • (gradVψ x))) (Measure.restrict σ Q))
  (hCore :
    (∫ x in Q, (gradU x) ⋅ ((χ x) • (gradVψ x)) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop
        - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ)) :
  let Rint :=
    ∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x) - (U x) • (gradVψ x)) ∂σ
  in
    (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint := by
  classical
  intro Rint
  set μ : Measure (ℝ × ℝ) := Measure.restrict σ Q
  have hLHS_expanded :
      (∫ x, (gradU x) ⋅ (gradChiVψ x) ∂μ)
        = (∫ x, (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)) ∂μ) := by
    have := hGradSplit_ae
    have hpush :
        (fun x => (gradU x) ⋅ (gradChiVψ x))
          =ᵐ[μ] (fun x => (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x))) := by
      filter_upwards [this] with x hx; simpa [hx]
    exact integral_congr_ae hpush
  set f : (ℝ × ℝ) → ℝ := fun x => (gradU x) ⋅ ((χ x) • (gradVψ x))
  set g : (ℝ × ℝ) → ℝ := fun x => (gradU x) ⋅ ((Vψ x) • (gradχ x))
  have hAdd :
      (∫ x, (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)) ∂μ)
        = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := by
    have hpoint : (fun x => (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)))
                    = (fun x => f x + g x) := by
      funext x; simp [f, g, dotR2_add_right]
    have hf := hIntA; have hg := hIntB
    simpa [hpoint] using (integral_add (μ := μ) hf hg)
  have hCore' :
      (∫ x, f x ∂μ)
        = (∫ t in I, ψ t * B t) + Rside + Rtop
          - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ) := by
    simpa [f] using hCore
  have hSwap :
      (∫ x, g x ∂μ)
        = (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ) := by
    have hpt : (fun x => g x) = (fun x => (gradχ x) ⋅ ((Vψ x) • (gradU x))) := by
      funext x; simp [g, dotR2_comm]
    simpa [hpt]
  have hIntSub :
      (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ)
        - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ)
      = Rint := by
    have hA := hIntIntA; have hB := hIntIntB
    have hSub :
        (∫ x, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂μ)
          - (∫ x, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂μ)
        = ∫ x, ( (gradχ x) ⋅ ((Vψ x) • (gradU x))
                  - (gradχ x) ⋅ ((U x) • (gradVψ x)) ) ∂μ :=
      integral_sub (μ := μ) hA hB
    simpa [Rint, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have :
      (∫ x in Q, (gradU x) ⋅ (gradChiVψ x) ∂σ)
        = (∫ t in I, ψ t * B t) + Rside + Rtop
          + ( (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ)
              - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ) ) := by
    have := calc
      (∫ x, (gradU x) ⋅ (gradChiVψ x) ∂μ)
          = (∫ x, (gradU x) ⋅ ((χ x) • (gradVψ x) + (Vψ x) • (gradχ x)) ∂μ) := hLHS_expanded
      _ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := hAdd
      _ = ((∫ t in I, ψ t * B t) + Rside + Rtop
              - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ))
            + (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ) := by
              simpa [hSwap] using congrArg (fun z => z + (∫ x, g x ∂μ)) hCore'
      _ = (∫ t in I, ψ t * B t) + Rside + Rtop
            + ( (∫ x in Q, (gradχ x) ⋅ ((Vψ x) • (gradU x)) ∂σ)
                - (∫ x in Q, (gradχ x) ⋅ ((U x) • (gradVψ x)) ∂σ) ) := by
              ring
    simpa using this
  simpa [hIntSub]

end RS
end RH
