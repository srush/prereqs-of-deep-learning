import Std

namespace Speedrun

-- The starting properties of the real numbers, rather than a construction
-- of them. All results in the article are universally quantified over a
-- number system satisfying these properties. No analytic function or
-- differentiation rule is part of this interface.
class RealNumbers (R : Type) extends Lean.Grind.Field R, LE R, LT R where
  [linearOrder : Std.IsLinearOrder R]
  [lawfulLT : Std.LawfulOrderLT R]
  [orderedArithmetic : Lean.Grind.OrderedRing R]
  leastUpperBound : ∀ E : R → Prop,
    (∃ x, E x) → (∃ b, ∀ x, E x → x ≤ b) →
    ∃ s, (∀ x, E x → x ≤ s) ∧ (∀ b, (∀ x, E x → x ≤ b) → s ≤ b)

attribute [instance] RealNumbers.linearOrder RealNumbers.lawfulLT
  RealNumbers.orderedArithmetic
attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

variable {R : Type} [RealNumbers R]

example : (0 : R) < 1 := by grind
example (a b c : R) : a*(b+c)=a*b+a*c := by grind

noncomputable def abs (x : R) : R := @ite _ (0 ≤ x) (Classical.propDecidable _) x (-x)
noncomputable def smaller (x y : R) : R := @ite _ (x ≤ y) (Classical.propDecidable _) x y

theorem abs_nonneg (x : R) : 0 ≤ abs x := by
  unfold abs; split <;> grind

theorem abs_zero : abs (0 : R) = 0 := by unfold abs; grind

theorem abs_eq_zero (x : R) : abs x = 0 ↔ x = 0 := by
  unfold abs; split <;> grind

theorem abs_neg (x : R) : abs (-x) = abs x := by
  unfold abs; split <;> split <;> grind

theorem abs_triangle (x y : R) : abs (x + y) ≤ abs x + abs y := by
  unfold abs; split <;> split <;> split <;> grind

theorem abs_mul (x y : R) : abs (x * y) = abs x * abs y := by
  have h₁ := @Lean.Grind.OrderedRing.mul_nonneg R _ _ _ _ _ _ x y
  have h₂ := @Lean.Grind.OrderedRing.mul_nonneg R _ _ _ _ _ _ (-x) y
  have h₃ := @Lean.Grind.OrderedRing.mul_nonneg R _ _ _ _ _ _ x (-y)
  have h₄ := @Lean.Grind.OrderedRing.mul_nonneg R _ _ _ _ _ _ (-x) (-y)
  unfold abs; split <;> split <;> split <;> grind

theorem abs_lt (x ε : R) : abs x < ε ↔ -ε < x ∧ x < ε := by
  unfold abs; split <;> grind

namespace Scalar
-- Compatibility names keep elementary proof steps readable in the article.
theorem mul_nonneg {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a*b :=
  Lean.Grind.OrderedRing.mul_nonneg ha hb

theorem mul_pos {a b : R} (ha : 0<a) (hb : 0<b) : 0<a*b :=
  Lean.Grind.OrderedRing.mul_pos ha hb

theorem le_of_lt {a b : R} (h : a<b) : a≤b := Std.le_of_lt h

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a≤b) (hc : 0≤c) : c*a≤c*b :=
  Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left h hc

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a≤b) (hc : 0≤c) : a*c≤b*c :=
  Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right h hc

theorem mul_lt_mul_of_pos_left {a b c : R} (h : a<b) (hc : 0<c) : c*a<c*b :=
  Lean.Grind.OrderedRing.mul_lt_mul_of_pos_left h hc

theorem mul_lt_mul_of_pos_right {a b c : R} (h : a<b) (hc : 0<c) : a*c<b*c :=
  Lean.Grind.OrderedRing.mul_lt_mul_of_pos_right h hc

theorem mul_lt_mul_right {a b c : R} (hc : 0<c) : a*c<b*c ↔ a<b :=
  Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_right hc

theorem inv_pos {a : R} : 0<a⁻¹ ↔ 0<a := Lean.Grind.Field.IsOrdered.inv_pos_iff

theorem div_lt_iff {a b c : R} (hb : 0<b) : a/b<c ↔ a<c*b := by
  rw [Lean.Grind.Field.div_eq_mul_inv]
  exact Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hb

theorem div_mul_cancel {a b : R} (hb : b≠0) : a/b*b=a := by grind

theorem div_def (a b : R) : a/b=a*b⁻¹ := Lean.Grind.Field.div_eq_mul_inv a b

theorem sub_self {a : R} : a-a=0 := by grind

theorem inv_zero : (0:R)⁻¹=0 := Lean.Grind.Field.inv_zero

theorem one_mul (a : R) : 1*a=a := by grind

theorem inv_mul_rev (a b : R) : (a*b)⁻¹=b⁻¹*a⁻¹ := by grind

theorem natCast_mul (a b : Nat) : ((a*b : Nat) : R)=(a:R)*(b:R) :=
  Lean.Grind.Semiring.natCast_mul a b

theorem natCast_le_natCast {a b : Nat} : (a:R)≤(b:R) ↔ a≤b := by
  constructor
  · exact Lean.Grind.OrderedRing.le_of_natCast_le_natCast a b
  · exact Lean.Grind.OrderedRing.natCast_le_natCast_of_le a b

theorem natCast_pos {a : Nat} : 0<(a:R) ↔ 0<a := by
  have hz : ((0:Nat):R)=0 := by grind
  constructor
  · intro h
    exact Lean.Grind.OrderedRing.lt_of_natCast_lt_natCast (R := R) 0 a (by grind)
  · intro h
    have := Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt (R:=R) 0 a h
    simpa only [hz] using this

theorem lt_iff_sub_pos (a b : R) : a<b ↔ 0<b-a := by grind
end Scalar
end Speedrun
