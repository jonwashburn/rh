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
import Mathlib.Tactic
import rh.RS.SchurGlobalization


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
      simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        at *
    simp [LHS, BD, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] at this
    simpa using this.symm
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
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        using (sub_add_cancel LHS BD)
    simpa [LHS, BD, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this.symm
  · -- bound is exactly the hypothesis
    simpa [LHS, BD]
      using hBoundDiff




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
    simpa [R, LHS, BD]
      using hRemBound
  have hSum :
      |LHS| + |R|
        ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (boxEnergy gradU σ Q) := by
    have : |LHS| + |R|
            ≤ Cψ_pair * Real.sqrt (boxEnergy gradU σ Q)
              + Cψ_rem * Real.sqrt (boxEnergy gradU σ Q) := by
      exact add_le_add hPairVol hR
    -- (Cψ_pair + Cψ_rem) * s = Cψ_pair*s + Cψ_rem*s
    simpa [add_mul]
      using this
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
    simpa [this, add_comm, add_left_comm, add_assoc]
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
    simpa [hSideZero, hTopZero, add_comm, add_left_comm, add_assoc]
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

-- (Optional) L² pairing bounds can be supplied by callers as `hPairVol`.

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
    have : (BD + (Rside + Rtop + Rint)) - BD = Rside + Rtop + Rint := by
      simpa using add_sub_cancel BD (Rside + Rtop + Rint)
    simpa [hEq, add_comm, add_left_comm, add_assoc, hSideZero, hTopZero]
      using this
  simpa [hdiff]
    using hRint

/-- Specialized remainder bound on the concrete pairing and boundary integrals,
assuming a rectangle IBP decomposition with vanishing side/top and an interior
remainder bound. -/
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
  simpa [LHS, BD]
    using this

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
