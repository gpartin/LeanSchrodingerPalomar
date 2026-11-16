module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

public section

namespace LeanSchrodingerPalomar

noncomputable section

def relativisticEnergy (mass momentum : ℝ) : ℝ :=
  Real.sqrt (mass ^ 2 + momentum ^ 2)

def restPhaseRemovedEnergy (mass momentum : ℝ) : ℝ :=
  relativisticEnergy mass momentum - mass

def schrodingerEnergy (mass momentum : ℝ) : ℝ :=
  momentum ^ 2 / (2 * mass)

def schrodingerRemainder (mass momentum : ℝ) : ℝ :=
  -(momentum ^ 4) /
    (2 * mass * (relativisticEnergy mass momentum + mass) ^ 2)

theorem relativisticEnergy_plus_mass_ne_zero
    (mass momentum : ℝ) (hMass : 0 < mass) :
    relativisticEnergy mass momentum + mass ≠ 0 := by
  have hEnergy : 0 ≤ relativisticEnergy mass momentum := by
    unfold relativisticEnergy
    exact Real.sqrt_nonneg _
  nlinarith

theorem restPhaseRemovedEnergy_rationalized
    (mass momentum : ℝ) (hMass : 0 < mass) :
    restPhaseRemovedEnergy mass momentum =
      momentum ^ 2 / (relativisticEnergy mass momentum + mass) := by
  unfold restPhaseRemovedEnergy relativisticEnergy
  have hArgument : 0 ≤ mass ^ 2 + momentum ^ 2 := by positivity
  have hRootSquare : (Real.sqrt (mass ^ 2 + momentum ^ 2)) ^ 2 =
      mass ^ 2 + momentum ^ 2 := Real.sq_sqrt hArgument
  have hDenom : Real.sqrt (mass ^ 2 + momentum ^ 2) + mass ≠ 0 := by
    have hRoot : 0 ≤ Real.sqrt (mass ^ 2 + momentum ^ 2) := Real.sqrt_nonneg _
    nlinarith
  field_simp [hDenom]
  nlinarith

theorem relativisticEnergy_ge_mass
    (mass momentum : ℝ) :
    mass ≤ relativisticEnergy mass momentum := by
  unfold relativisticEnergy
  have hArgument : 0 ≤ mass ^ 2 + momentum ^ 2 := by positivity
  have hRootSquare : (Real.sqrt (mass ^ 2 + momentum ^ 2)) ^ 2 =
      mass ^ 2 + momentum ^ 2 := Real.sq_sqrt hArgument
  have hRootNonnegative : 0 ≤ Real.sqrt (mass ^ 2 + momentum ^ 2) :=
    Real.sqrt_nonneg _
  by_cases hMass : 0 ≤ mass
  · nlinarith [hMass, sq_nonneg momentum]
  · nlinarith [hRootNonnegative]

theorem exactSchrodingerKineticSplit
    (mass momentum : ℝ) (hMass : 0 < mass) :
    restPhaseRemovedEnergy mass momentum =
      schrodingerEnergy mass momentum + schrodingerRemainder mass momentum := by
  rw [restPhaseRemovedEnergy_rationalized mass momentum hMass]
  unfold schrodingerEnergy schrodingerRemainder
  have hDenom : relativisticEnergy mass momentum + mass ≠ 0 :=
    relativisticEnergy_plus_mass_ne_zero mass momentum hMass
  have hRootSquare : relativisticEnergy mass momentum ^ 2 =
      mass ^ 2 + momentum ^ 2 := by
    unfold relativisticEnergy
    exact Real.sq_sqrt (by positivity)
  field_simp [hDenom, ne_of_gt hMass]
  nlinarith

theorem absSchrodingerRemainder_eq_positiveFraction
    (mass momentum : ℝ) (hMass : 0 < mass) :
    |schrodingerRemainder mass momentum| =
      momentum ^ 4 /
        (2 * mass * (relativisticEnergy mass momentum + mass) ^ 2) := by
  unfold schrodingerRemainder
  have hDenom : 0 < 2 * mass * (relativisticEnergy mass momentum + mass) ^ 2 := by
    have hPlus : 0 < relativisticEnergy mass momentum + mass := by
      have hEnergy : 0 ≤ relativisticEnergy mass momentum := by
        unfold relativisticEnergy
        exact Real.sqrt_nonneg _
      nlinarith
    positivity
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos hDenom]

theorem schrodingerRemainderBound
    (mass momentum : ℝ) (hMass : 0 < mass) :
    |schrodingerRemainder mass momentum| ≤ momentum ^ 4 / (8 * mass ^ 3) := by
  rw [absSchrodingerRemainder_eq_positiveFraction mass momentum hMass]
  have hEnergyGe : mass ≤ relativisticEnergy mass momentum :=
    relativisticEnergy_ge_mass mass momentum
  have hPlus : 0 < relativisticEnergy mass momentum + mass := by nlinarith
  have hSquare : (2 * mass) ^ 2 ≤
      (relativisticEnergy mass momentum + mass) ^ 2 := by
    nlinarith [sq_nonneg (relativisticEnergy mass momentum - mass)]
  have hMultiply := mul_le_mul_of_nonneg_left hSquare (le_of_lt hMass)
  have hDenomOrder : 8 * mass ^ 3 ≤
      2 * mass * (relativisticEnergy mass momentum + mass) ^ 2 := by
    nlinarith
  have hNumerator : 0 ≤ momentum ^ 4 := by positivity
  have hLeftDenom : 0 < 2 * mass *
      (relativisticEnergy mass momentum + mass) ^ 2 := by positivity
  have hRightDenom : 0 < 8 * mass ^ 3 := by positivity
  apply (div_le_div_iff₀ hLeftDenom hRightDenom).2
  exact mul_le_mul_of_nonneg_left hDenomOrder hNumerator

end
end LeanSchrodingerPalomar
