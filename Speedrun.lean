import Speedrun.Foundations

set_option doc.verso true

namespace Speedrun

noncomputable section

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast
variable {R : Type} [RealNumbers R]

/-!
# The Prerequisites of Deep Learning

When [asked](https://www.youtube.com/watch?v=iOzi9_YakyE&t=2s) about the mathematics of LLMs, Terence Tao noted that "any
undergraduate Math major would have all the prerequisites." It's a funny quote,
like saying any Biologist has all the prerequisites to be a
sprinter. That being said, the idea of the prerequisites of Deep Learning is
kind of interesting. What if you took seriously the idea that there was a
minimal formal curriculum between Peano and LeCun that you had to follow
(I'm picturing this being taught in a French university). For instance, my
controversial take is that I see no reason you need anything at all
from Linear Algebra.

So what are the prerequisites for speedrunning Deep Learning? I think the
answer is 1/2 of one freshman semester -- if you are already really smart.
This estimate comes from taking the textbook from a really hard math class,
Harvard Math 55, and removing all the parts that are not useful (who needs
integrals). I'm not sure what to make of this. On the one hand, it's pretty
nice that you can formally derive MNIST from first principles. On the other
hand, it is about 3,000 lines of Lean, which seems like a lot of machinery just
to get to "move towards the downwards direction". Would be quite curious if
someone can do this much faster.

Caveat: This blog is AI slop. The math is aligned to "Baby Rudin" --
[*Principles of Mathematical Analysis*](https://david92jackson.neocities.org/images/Principles_of_Mathematical_Analysis-Rudin.pdf) with pointers to the relevant theorems.
Hug your local mathematician, they are having a hard year.

![Metric spaces, limits, series, and derivatives lead to exp and neural networks.](site/diagrams/rudin-tech-tree.svg)
-/

/-!
# Basic Topology

## Metric Spaces

![Three points form a triangle inside an open Euclidean ball; smaller balls show neighborhoods.](site/diagrams/rudin-metric-spaces.svg)

*The blue segment is the direct route; amber goes via a third point. Dashed circles mark open neighborhoods.*
-/

structure Metric (X : Type) where
  dist : X → X → R
  nonneg : ∀ x y, 0 ≤ dist x y
  zero_iff : ∀ x y, dist x y = 0 ↔ x = y
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

def realMetric : Metric (R := R) R where
  dist x y := abs (x - y)
  nonneg x y := abs_nonneg _
  zero_iff x y := by rw [abs_eq_zero]; grind [smaller]
  symm x y := by
    have h : x - y = -(y - x) := by grind [smaller]
    rw [h, abs_neg]
  triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by grind [smaller]
    rw [h]
    exact abs_triangle _ _

/-!
## Open and Closed Sets

![Left: an open disk with neighborhoods inside it. Right: a closed disk contains a boundary limit point, whose neighborhoods extend outside the disk. Dashed boundaries are excluded; solid boundaries are included.](site/diagrams/rudin-open-closed.svg)

*Left: small neighborhoods stay inside the open disk. Right: the closed disk includes its boundary limit point, although its neighborhood extends outside.*
-/

abbrev PointSet (X : Type) := X → Prop

-- Points less than r away from x; the boundary is excluded.
def Neighborhood (M : Metric (R := R) X) (x : X) (r : R) : PointSet X :=
  fun y => M.dist x y < r

-- Every point has a small neighborhood entirely inside the set.
def IsOpen (M : Metric (R := R) X) (E : PointSet X) : Prop :=
  ∀ x, E x → ∃ r, 0 < r ∧ ∀ y, Neighborhood M x r y → E y

-- Every neighborhood of p contains a different point of E.
def LimitPoint (M : Metric (R := R) X) (E : PointSet X) (p : X) : Prop :=
  ∀ r, 0<r → ∃ q, E q ∧ q≠p ∧ Neighborhood M p r q

-- The set contains all of its limit points.
def IsClosed (M : Metric (R := R) X) (E : PointSet X) : Prop :=
  ∀ p, LimitPoint M E p → E p

-- Rudin Theorem 2.19: every neighborhood is open.
theorem neighborhood_open (M : Metric (R := R) X) (x : X) (r : R) :
    IsOpen M (Neighborhood M x r) := by
  intro y hy
  refine ⟨r - M.dist x y, by exact (Scalar.lt_iff_sub_pos _ _).mp hy, ?_⟩
  intro z hz
  have ht := M.triangle x y z
  dsimp [Neighborhood] at *
  grind [smaller]

-- Rudin Theorem 2.23: a set is open iff its complement is closed.
theorem open_iff_complement_closed (M : Metric (R := R) X) (E : PointSet X) :
    IsOpen M E ↔ IsClosed M (fun p => ¬E p) := by
  constructor
  · intro hopen p hlimit hp
    obtain ⟨r,hr,hinside⟩ := hopen p hp
    obtain ⟨q,houtside,_,hq⟩ := hlimit r hr
    exact houtside (hinside q hq)
  · intro hclosed p hp
    apply Classical.byContradiction
    intro hno
    have hlimit : LimitPoint M (fun q => ¬E q) p := by
      intro r hr
      have witness : ∃ q, Neighborhood M p r q ∧ ¬E q := by
        apply Classical.byContradiction
        intro hn
        apply hno
        refine ⟨r,hr,?_⟩
        intro q hq
        exact Classical.byContradiction (fun he => hn ⟨q,hq,he⟩)
      obtain ⟨q,hq,he⟩ := witness
      exact ⟨q,he,fun hqp => he (hqp ▸ hp),hq⟩
    exact hclosed p hlimit hp

-- Rudin Theorem 2.24(c), two-set case of finite intersections of open
-- sets.
theorem open_inter (M : Metric (R := R) X) (E F : PointSet X)
    (hE : IsOpen M E) (hF : IsOpen M F) :
    IsOpen M (fun x => E x ∧ F x) := by
  intro x ⟨hx, hy⟩
  obtain ⟨r, hr, hEr⟩ := hE x hx
  obtain ⟨s, hs, hFs⟩ := hF x hy
  refine ⟨smaller r s, by grind [smaller], ?_⟩
  intro y h
  exact ⟨hEr y (by dsimp [Neighborhood] at *; grind [smaller]),
    hFs y (by dsimp [Neighborhood] at *; grind [smaller])⟩

-- Rudin Theorem 2.24(a): arbitrary unions of open sets are open.
theorem open_union (M : Metric (R := R) X) (E : ι → PointSet X)
    (h : ∀ i, IsOpen M (E i)) : IsOpen M (fun x => ∃ i, E i x) := by
  intro x ⟨i, hi⟩
  obtain ⟨r, hr, hEr⟩ := h i x hi
  exact ⟨r, hr, fun y hy => ⟨i, hEr y hy⟩⟩

/-!
## Closures

![Closing a punctured open disk adds its boundary and its missing center point, highlighted in amber.](site/diagrams/rudin-closures.svg)

*Closing the punctured disk fills its missing center and adds its outer boundary, shown in amber.*
-/

-- The points of E together with all of its limit points.
def Closure (M : Metric (R := R) X) (E : PointSet X) : PointSet X :=
  fun p => E p ∨ LimitPoint M E p

-- Rudin Definition 2.26 and the proof of Theorem 2.27(a): neighborhood
-- characterization of closure; extracted helper.
theorem closure_neighborhood (M : Metric (R := R) X) (E : PointSet X) (p : X) :
    Closure M E p ↔ ∀ r, 0<r → ∃ q, E q ∧ M.dist p q<r := by
  constructor
  · intro hp r hr
    rcases hp with hp | hp
    · exact ⟨p,hp,by simpa [(M.zero_iff p p).mpr rfl] using hr⟩
    · obtain ⟨q,hq,_,hd⟩ := hp r hr
      exact ⟨q,hq,hd⟩
  · intro h
    by_cases hp : E p
    · exact Or.inl hp
    · right
      intro r hr
      obtain ⟨q,hq,hd⟩ := h r hr
      exact ⟨q,hq,fun he => hp (he ▸ hq),hd⟩

-- Rudin, corollary to Theorem 2.23, closed-to-open direction.
theorem closed_complement_open (M : Metric (R := R) X) (E : PointSet X)
    (hE : IsClosed M E) : IsOpen M (fun p => ¬E p) := by
  intro p hp
  apply Classical.byContradiction
  intro hno
  apply hp
  apply hE p
  intro r hr
  have hex : ∃ q, Neighborhood M p r q ∧ E q := by
    apply Classical.byContradiction
    intro hn
    apply hno
    exact ⟨r,hr,fun q hq he => hn ⟨q,hq,he⟩⟩
  obtain ⟨q,hq,he⟩ := hex
  exact ⟨q,he,fun hqp => hp (hqp ▸ he),hq⟩

-- Rudin Theorem 2.27(a): the closure is closed.
theorem closure_closed (M : Metric (R := R) X) (E : PointSet X) :
    IsClosed M (Closure M E) := by
  have hopen : IsOpen M (fun p => ¬Closure M E p) := by
    intro p hp
    have hn : ¬∀ r, 0<r → ∃ q, E q ∧ M.dist p q<r :=
      fun h => hp ((closure_neighborhood M E p).mpr h)
    obtain ⟨r,hr⟩ := Classical.not_forall.mp hn
    have hrpos : 0<r := Classical.byContradiction
      (fun h => hr (fun hpos => False.elim (h hpos)))
    refine ⟨r/2,by grind,?_⟩
    intro q hpq hq
    obtain ⟨z,hz,hqz⟩ := (closure_neighborhood M E q).mp hq (r/2) (by grind)
    have ht := M.triangle p q z
    apply hr
    intro _
    exact ⟨z,hz,by dsimp [Neighborhood] at hpq; grind (ematch := 0)⟩
  intro p hp
  apply Classical.byContradiction
  intro hn
  obtain ⟨r,hr,houtside⟩ := hopen p hn
  obtain ⟨q,hq,_,hd⟩ := hp r hr
  exact houtside q hd hq

-- Rudin Theorem 2.27(c): every closed superset contains the closure.
theorem closure_minimal (M : Metric (R := R) X) (E F : PointSet X)
    (hF : IsClosed M F) (hEF : ∀ p, E p → F p) :
    ∀ p, Closure M E p → F p := by
  intro p hp
  rcases hp with hp | hp
  · exact hEF p hp
  · apply hF p
    intro r hr
    obtain ⟨q,hq,hne,hd⟩ := hp r hr
    exact ⟨q,hEF q hq,hne,hd⟩

-- Consequence of Rudin Theorem 2.27(c): closure preserves inclusion;
-- not a separately numbered theorem.
theorem closure_mono (M : Metric (R := R) X) (E F : PointSet X)
    (hEF : ∀ p, E p → F p) : ∀ p, Closure M E p → Closure M F p :=
  closure_minimal M E (Closure M F) (closure_closed M F) (fun p hp => Or.inl (hEF p hp))

/-!
## Compact Sets

![A closed disk covered by open balls. The right-hand picture retains a finite subcover and discards redundant balls.](site/diagrams/rudin-compact-sets.svg)

*The dashed balls cover the solid disk. Removing redundant balls leaves a finite subcover on the right. Compactness requires this for every open cover.*
-/

-- Every open cover has a finite subcover drawn from that same cover.
def IsCompact (M : Metric (R := R) X) (K : PointSet X) : Prop :=
  ∀ (I : Type) (U : I → PointSet X),
    (∀ i, IsOpen M (U i)) →
    (∀ x, K x → ∃ i, U i x) →
    ∃ selected : List I, ∀ x, K x → ∃ i, i ∈ selected ∧ U i x

-- Helper for Rudin Theorem 2.34: choose a common positive radius for
-- finitely many neighborhoods.
theorem finite_positive_radius (rs : I → R) (selected : List I)
    (positive : ∀ i, i∈selected → 0<rs i) :
    ∃ r, 0<r ∧ ∀ i, i∈selected → r≤rs i := by
  induction selected with
  | nil => exact ⟨1,by grind,by simp⟩
  | cons i selected ih =>
    obtain ⟨r,hr,hsmall⟩ := ih (fun j hj => positive j (List.mem_cons_of_mem i hj))
    have hi := positive i (by simp)
    refine ⟨smaller r (rs i),by grind [smaller],?_⟩
    intro j hj
    simp only [List.mem_cons] at hj
    rcases hj with hj | hj
    · subst j; grind [smaller]
    · have := hsmall j hj; grind [smaller]

-- Rudin Theorem 2.34: compact subsets of metric spaces are closed.
theorem compact_closed (M : Metric (R := R) X) (K : PointSet X)
    (compact : IsCompact M K) : IsClosed M K := by
  have hopen : IsOpen M (fun p => ¬K p) := by
    intro p hp
    let Q := {q : X // K q}
    let radius (q : Q) := M.dist p q.val/3
    have positive : ∀ q, 0<radius q := by
      intro q
      have hne : p≠q.val := fun he => hp (he ▸ q.property)
      have hz := M.zero_iff p q.val
      have hn := M.nonneg p q.val
      dsimp [radius]
      grind (ematch := 0)
    obtain ⟨selected,cover⟩ := compact Q (fun q => Neighborhood M q.val (radius q))
      (fun q => neighborhood_open M q.val (radius q))
      (fun q hq => ⟨⟨q,hq⟩,by
        change M.dist q q<radius ⟨q,hq⟩
        simpa [(M.zero_iff q q).mpr rfl] using positive ⟨q,hq⟩⟩)
    obtain ⟨r,hr,hsmall⟩ := finite_positive_radius radius selected (fun q _ => positive q)
    refine ⟨r,hr,?_⟩
    intro z hpz hz
    obtain ⟨q,hq,hqz⟩ := cover z hz
    have h₁ := hsmall q hq
    have h₂ := M.triangle p z q.val
    rw [M.symm z q.val] at h₂
    have h₃ := positive q
    dsimp [Neighborhood,radius] at *
    grind (ematch := 0)
  intro p hp
  apply Classical.byContradiction
  intro hn
  obtain ⟨r,hr,houtside⟩ := hopen p hn
  obtain ⟨q,hq,_,hd⟩ := hp r hr
  exact houtside q hd hq

-- Rudin Theorem 2.35: a closed subset of a compact set is compact.
theorem compact_closed_subset (M : Metric (R := R) X) (K F : PointSet X)
    (hK : IsCompact M K) (hF : IsClosed M F) (hFK : ∀ p, F p → K p) :
    IsCompact M F := by
  intro I U hopen cover
  let V : Option I → PointSet X
    | none => fun p => ¬F p
    | some i => U i
  have hv : ∀ i, IsOpen M (V i) := by
    intro i
    cases i with
    | none => exact closed_complement_open M F hF
    | some i => exact hopen i
  have hc : ∀ p, K p → ∃ i, V i p := by
    intro p _
    by_cases hp : F p
    · obtain ⟨i,hi⟩ := cover p hp
      exact ⟨some i,hi⟩
    · exact ⟨none,hp⟩
  obtain ⟨selected,hs⟩ := hK (Option I) V hv hc
  refine ⟨selected.filterMap id,?_⟩
  intro p hp
  obtain ⟨i,hi,hv⟩ := hs p (hFK p hp)
  cases i with
  | none => exact False.elim (hv hp)
  | some i => exact ⟨i,List.mem_filterMap.mpr ⟨some i,hi,rfl⟩,hv⟩

-- Finite-index helper for the corollary to Rudin Theorem 2.36; no
-- separate Rudin theorem.
theorem list_le_max (ns : List Nat) : ∀ n, n∈ns → n≤ns.foldr max 0 := by
  induction ns with
  | nil => simp
  | cons a ns ih =>
    intro n hn
    simp only [List.mem_cons] at hn
    simp only [List.foldr]
    rcases hn with hn | hn
    · subst n; omega
    · have := ih n hn; omega

-- Rudin, corollary to Theorem 2.36: a nested sequence of nonempty
-- compact sets has nonempty intersection.
theorem nested_compact_intersection (M : Metric (R := R) X) (K : Nat → PointSet X)
    (compact : ∀ n, IsCompact M (K n))
    (nonempty : ∀ n, ∃ p, K n p)
    (nested : ∀ m n, m≤n → ∀ p, K n p → K m p) :
    ∃ p, ∀ n, K n p := by
  apply Classical.byContradiction
  intro hnone
  have cover : ∀ p, K 0 p → ∃ n, ¬K n p := by
    intro p _
    apply Classical.byContradiction
    intro hn
    apply hnone
    exact ⟨p,fun n => Classical.byContradiction (fun h => hn ⟨n,h⟩)⟩
  obtain ⟨ns,hns⟩ := compact 0 Nat (fun n p => ¬K n p)
    (fun n => closed_complement_open M (K n) (compact_closed M (K n) (compact n))) cover
  obtain ⟨p,hp⟩ := nonempty (ns.foldr max 0)
  obtain ⟨n,hn,hnot⟩ := hns p (nested 0 _ (by omega) p hp)
  exact hnot (nested n _ (list_le_max ns n hn) p hp)

/-!
### Nested Intervals
-/

-- Rudin Theorem 2.38: nested nonempty closed intervals have nonempty
-- intersection.
theorem nested_intervals (a b : Nat → R) (nonempty : ∀ n, a n≤b n)
    (nested : ∀ m n, m≤n → a m≤a n ∧ b n≤b m) :
    ∃ x, ∀ n, a n≤x ∧ x≤b n := by
  have cross : ∀ m n, a n≤b m := by
    intro m n
    have h₁ := (nested n (m+n) (by omega)).1
    have h₂ := nonempty (m+n)
    have h₃ := (nested m (m+n) (by omega)).2
    grind (ematch := 0)
  obtain ⟨x,upper,least⟩ := RealNumbers.leastUpperBound
    (fun y => ∃ n, a n=y) ⟨a 0,0,rfl⟩
    ⟨b 0,fun y ⟨n,hn⟩ => hn ▸ cross 0 n⟩
  refine ⟨x,?_⟩
  intro m
  exact ⟨upper (a m) ⟨m,rfl⟩,least (b m) (fun y ⟨n,hn⟩ => hn ▸ cross m n)⟩

-- Rudin Theorem 1.20(a), Archimedean property with unit step.
theorem exists_nat_gt (x : R) : ∃ n : Nat, x < (n : R) := by
  apply Classical.byContradiction
  intro h
  have bound : ∀ n : Nat, (n:R) ≤ x := by intro n; have : ¬x<(n:R) := fun hn => h ⟨n,hn⟩; grind
  obtain ⟨s, upper, least⟩ := RealNumbers.leastUpperBound
    (fun y : R => ∃ n : Nat, (n:R)=y) ⟨0,0,by grind⟩
    ⟨x, fun y ⟨n,hn⟩ => hn ▸ bound n⟩
  have smallerBound : ∀ y : R, (∃ n : Nat, (n:R)=y) → y≤s-1 := by
    intro y ⟨n,hn⟩
    have hu := upper ((n+1:Nat):R) ⟨n+1,rfl⟩
    grind
  have := least (s-1) smallerBound
  grind

/-!
## Compactness of an Interval

![Planar illustration of Rudin's nested-cell argument: nested squares share a point and eventually fit inside an open ball around it.](site/diagrams/rudin-compact-interval.svg)

*Nested squares shrink around a common point until they fit inside its amber neighborhood. This is the planar analogue of nested intervals.*
-/

-- Finitely many of the given sets cover the whole closed interval.
def FiniteSubcover (U : I → PointSet R) (a b : R) : Prop :=
  ∃ selected : List I, ∀ x, a≤x → x≤b → ∃ i, i∈selected ∧ U i x

-- Proof step in Rudin Theorem 2.40, real interval case: join finite
-- subcovers of the two halves.
theorem finiteSubcover_join (U : I → PointSet R) (a c b : R)
    (left : FiniteSubcover U a c) (right : FiniteSubcover U c b) :
    FiniteSubcover U a b := by
  obtain ⟨ls,hl⟩ := left
  obtain ⟨rs,hr⟩ := right
  refine ⟨ls++rs,?_⟩
  intro x hax hxb
  by_cases hxc : x≤c
  · obtain ⟨i,hi,hu⟩ := hl x hax hxc
    exact ⟨i,List.mem_append_left _ hi,hu⟩
  · obtain ⟨i,hi,hu⟩ := hr x (by grind) hxb
    exact ⟨i,List.mem_append_right _ hi,hu⟩

-- Proof step in Rudin Theorem 2.40, real interval case: one half still
-- has no finite subcover.
theorem interval_bad_half (U : I → PointSet R) (a b : R) (hab : a≤b)
    (bad : ¬FiniteSubcover U a b) :
    ∃ q : R×R, a≤q.1 ∧ q.2≤b ∧ q.2-q.1=(b-a)/2 ∧
      q.1≤q.2 ∧ ¬FiniteSubcover U q.1 q.2 := by
  by_cases hl : FiniteSubcover U a ((a+b)/2)
  · refine ⟨((a+b)/2,b),by grind,by grind,by grind,by grind,?_⟩
    exact fun hr => bad (finiteSubcover_join U a ((a+b)/2) b hl hr)
  · exact ⟨(a,(a+b)/2),by grind,by grind,by grind,by grind,hl⟩

-- Helper for the final step of Rudin Theorem 2.40, using the
-- Archimedean property, Theorem 1.20(a).
theorem powers_two_unbounded (B : R) : ∃ n : Nat, B<(2:R)^n := by
  have lower : ∀ n : Nat, (n:R)+1≤(2:R)^n := by
    intro n
    induction n with
    | zero => simp only [Lean.Grind.Semiring.pow_zero]; grind
    | succ n ih =>
      have hn : (0:R)≤(n:R) := by
        have := Scalar.natCast_le_natCast (R:=R) |>.mpr (Nat.zero_le n)
        grind
      rw [Lean.Grind.Semiring.pow_succ]
      grind
  obtain ⟨n,hn⟩ := exists_nat_gt B
  exact ⟨n,by have := lower n; grind⟩

-- Arithmetic helper for Rudin Theorem 2.40; positivity of powers of two
-- is not a separate theorem there.
theorem powers_two_pos (n : Nat) : 0<(2:R)^n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero]; grind
  | succ n ih => rw [Lean.Grind.Semiring.pow_succ]; exact Scalar.mul_pos ih (by grind)

-- Rudin Theorem 2.40, k = 1: every closed bounded interval is compact
-- (including an empty interval here).
theorem interval_compact (a b : R) : IsCompact realMetric (fun x => a≤x ∧ x≤b) := by
  intro I U hopen cover
  suffices h : FiniteSubcover U a b by
    obtain ⟨selected,hselected⟩ := h
    exact ⟨selected,fun x hx => hselected x hx.1 hx.2⟩
  by_cases hab : a≤b
  · apply Classical.byContradiction
    intro bad
    let Bad := {q : R×R // q.1≤q.2 ∧ ¬FiniteSubcover U q.1 q.2}
    let next (q : Bad) : Bad :=
      ⟨Classical.choose (interval_bad_half U q.val.1 q.val.2 q.property.1 q.property.2),
        (Classical.choose_spec (interval_bad_half U q.val.1 q.val.2 q.property.1 q.property.2)).2.2.2⟩
    let intervals : Nat → Bad := fun n => Nat.rec ⟨(a,b),hab,bad⟩ (fun _ q => next q) n
    let lo (n : Nat) := (intervals n).val.1
    let hi (n : Nat) := (intervals n).val.2
    have step (n : Nat) : lo n≤lo (n+1) ∧ hi (n+1)≤hi n ∧
        hi (n+1)-lo (n+1)=(hi n-lo n)/2 := by
      have h := Classical.choose_spec (interval_bad_half U (lo n) (hi n)
        (intervals n).property.1 (intervals n).property.2)
      exact ⟨h.1,h.2.1,h.2.2.1⟩
    have nest : ∀ m n, m≤n → lo m≤lo n ∧ hi n≤hi m := by
      intro m n hmn
      induction n with
      | zero =>
        have : m=0 := by omega
        subst m
        exact ⟨Std.le_refl _,Std.le_refl _⟩
      | succ n ih =>
        by_cases he : m=n+1
        · subst m; exact ⟨Std.le_refl _,Std.le_refl _⟩
        have h := ih (by omega)
        have hstep := step n
        constructor <;> grind (ematch := 0)
    have length : ∀ n, (hi n-lo n)*(2:R)^n=b-a := by
      intro n
      induction n with
      | zero =>
        rw [Lean.Grind.Semiring.pow_zero]
        change (b-a)*1=b-a
        grind (ematch := 0)
      | succ n ih =>
        rw [(step n).2.2,Lean.Grind.Semiring.pow_succ]
        grind (ematch := 0)
    obtain ⟨x,hx⟩ := nested_intervals lo hi (fun n => (intervals n).property.1) nest
    obtain ⟨i,hix⟩ := cover x (hx 0)
    obtain ⟨r,hr,hinside⟩ := hopen i x hix
    obtain ⟨n,hn⟩ := powers_two_unbounded ((b-a)/r)
    have narrow : hi n-lo n<r := by
      have positive := powers_two_pos (R:=R) n
      apply (Scalar.mul_lt_mul_right positive).mp
      calc
        (hi n-lo n)*(2:R)^n = b-a := length n
        _ < (2:R)^n*r := (Scalar.div_lt_iff hr).mp hn
        _ = r*(2:R)^n := by grind (ematch := 0)
    apply (intervals n).property.2
    refine ⟨[i],?_⟩
    intro y hay hyb
    refine ⟨i,by simp,?_⟩
    apply hinside y
    change abs (x-y)<r
    rw [abs_lt]
    have hxn := hx n
    constructor <;> grind (ematch := 0)
  · exact ⟨[],fun x hax hxb => False.elim (hab (by grind))⟩

-- Interval case of Rudin Theorem 2.34 combined with Theorem 2.40;
-- proved directly here.
theorem interval_closed (a b : R) : IsClosed realMetric (fun x => a≤x ∧ x≤b) := by
  intro p hp
  constructor
  · apply Classical.byContradiction
    intro h
    obtain ⟨q,hq,_,hd⟩ := hp (a-p) (by grind)
    change abs (p-q)<a-p at hd
    have := (abs_lt _ _).mp hd
    grind (ematch := 0)
  · apply Classical.byContradiction
    intro h
    obtain ⟨q,hq,_,hd⟩ := hp (p-b) (by grind)
    change abs (p-q)<p-b at hd
    have := (abs_lt _ _).mp hd
    grind (ematch := 0)

-- Consequence of Rudin Theorem 2.41, (a) implies (b), for k = 1; used
-- explicitly in the proof of Theorem 3.11(c).
theorem bounded_closure_compact (E : PointSet R) (a b : R)
    (bounded : ∀ p, E p → a≤p ∧ p≤b) : IsCompact realMetric (Closure realMetric E) :=
  compact_closed_subset realMetric (fun x => a≤x ∧ x≤b) (Closure realMetric E)
    (interval_compact a b) (closure_closed realMetric E)
    (closure_minimal realMetric E _ (interval_closed a b) bounded)

/-!
# Numerical Sequences and Series
-/

/-!
## Convergent Sequences

![A sequence approaches a fixed limit inside successively smaller balls.](site/diagrams/rudin-convergent-sequences.svg)

*The sequence eventually stays inside each smaller ball around the dark limit point.*
-/

-- Eventually every term is as close as desired to the fixed limit x.
def ConvergesTo (M : Metric (R := R) X) (s : Nat → X) (x : X) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → M.dist (s n) x < ε

-- Rudin Theorem 3.2(b): uniqueness of a sequence limit.
theorem limit_unique (M : Metric (R := R) X) (s : Nat → X) (x y : X)
    (hx : ConvergesTo M s x) (hy : ConvergesTo M s y) : x = y := by
  apply Classical.byContradiction
  intro h
  have hd : 0 < M.dist x y := by
    have := M.nonneg x y
    have := M.zero_iff x y
    grind [smaller]
  obtain ⟨N, hN⟩ := hx (M.dist x y / 2) (by grind [smaller])
  obtain ⟨K, hK⟩ := hy (M.dist x y / 2) (by grind [smaller])
  have hn := hN (max N K) (by omega)
  have hk := hK (max N K) (by omega)
  have ht := M.triangle x (s (max N K)) y
  rw [M.symm x (s (max N K))] at ht
  grind [smaller]

/-!
### The Arithmetic of Limits
-/

-- Rudin Definition 3.1, constant-sequence example (e), generalized to
-- any real constant.
theorem seq_const (a : R) : ConvergesTo realMetric (fun _ => a) a := by
  intro ε hε
  refine ⟨0,?_⟩
  intro n _
  change abs (a-a)<ε
  simpa only [Scalar.sub_self,abs_zero] using hε

-- Rudin Theorem 3.3(a), real case: limit of a sum.
theorem seq_add (s t : Nat → R) (a b : R)
    (hs : ConvergesTo realMetric s a) (ht : ConvergesTo realMetric t b) :
    ConvergesTo realMetric (fun n => s n+t n) (a+b) := by
  intro ε hε
  obtain ⟨N,hN⟩ := hs (ε/2) (by grind)
  obtain ⟨K,hK⟩ := ht (ε/2) (by grind)
  refine ⟨max N K,?_⟩
  intro n hn
  have h₁ := hN n (by omega)
  have h₂ := hK n (by omega)
  change abs (s n-a)<ε/2 at h₁
  change abs (t n-b)<ε/2 at h₂
  have hh := abs_triangle (s n-a) (t n-b)
  have heq : (s n-a)+(t n-b)=s n+t n-(a+b) := by grind
  rw [heq] at hh
  change abs (s n+t n-(a+b))<ε
  grind

-- Consequence of Rudin Theorem 1.33(e), real triangle inequality; an
-- auxiliary estimate.
theorem abs_bound_of_error (a b : R) : abs a ≤ abs (a-b)+abs b := by
  have ht := abs_triangle (a-b) b
  have heq : a-b+b=a := by grind [smaller]
  simpa only [heq] using ht

-- Rudin Theorem 3.3(c), real case: limit of a product.
theorem seq_mul (s t : Nat → R) (a b : R)
    (hs : ConvergesTo realMetric s a) (ht : ConvergesTo realMetric t b) :
    ConvergesTo realMetric (fun n => s n*t n) (a*b) := by
  intro ε hε
  let K := abs a+abs b+1
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hK : 0<K := by dsimp [K]; grind
  let η := ε/(2*K)
  have hη : 0<η := by
    dsimp [η]; rw [Scalar.div_def]
    exact Scalar.mul_pos hε (Scalar.inv_pos.mpr (by grind))
  have hηK : 2*η*K=ε := by dsimp [η]; grind
  obtain ⟨N,hN⟩ := hs η hη
  obtain ⟨M,hM⟩ := ht (smaller η 1) (by grind [smaller])
  refine ⟨max N M,?_⟩
  intro n hn
  have h₁ := hN n (by omega)
  have h₂ := hM n (by omega)
  change abs (s n-a)<η at h₁
  change abs (t n-b)<smaller η 1 at h₂
  have htb : abs (t n)≤K := by
    have := abs_bound_of_error (t n) b
    dsimp [K]; grind [smaller]
  have hab : abs a≤K := by dsimp [K]; grind
  have p₁ := Scalar.mul_le_mul_of_nonneg_left htb (abs_nonneg (s n-a))
  have p₂ := Scalar.mul_lt_mul_of_pos_right h₁ hK
  have p₃ := Scalar.mul_le_mul_of_nonneg_right hab (abs_nonneg (t n-b))
  have p₄ := Scalar.mul_lt_mul_of_pos_left (show abs (t n-b)<η from by grind [smaller]) hK
  have hh := abs_triangle ((s n-a)*t n) (a*(t n-b))
  rw [abs_mul,abs_mul] at hh
  have heq : (s n-a)*t n+a*(t n-b)=s n*t n-a*b := by grind
  rw [heq] at hh
  change abs (s n*t n-a*b)<ε
  grind

-- Rudin Theorem 1.33(a), real case: a nonzero number has positive
-- absolute value.
theorem abs_pos (a : R) (ha : a ≠ 0) : 0 < abs a := by
  have := abs_nonneg a
  have := abs_eq_zero a
  grind [smaller]

-- Consequence of Rudin Theorem 1.33(c), real case: absolute value of a
-- quotient. Lean's total division also covers a zero denominator here.
theorem abs_div (a b : R) : abs (a/b)=abs a/abs b := by
  by_cases hb : b=0
  · subst b
    have heq : a*0=0 := by grind
    simp only [Scalar.div_def, Scalar.inv_zero, heq, abs_zero]
    grind
  · have hab : abs b≠0 := by intro h; exact hb ((abs_eq_zero b).mp h)
    have heq : a/b*b=a := by grind [smaller]
    have h := congrArg abs heq
    rw [abs_mul] at h
    grind [smaller]

-- Rudin Theorem 3.3(d), real case; this version permits finitely many
-- zero terms since convergence to a nonzero limit makes the tail
-- nonzero.
theorem seq_inv (s : Nat → R) (a : R) (ha : a≠0)
    (hs : ConvergesTo realMetric s a) :
    ConvergesTo realMetric (fun n => 1/s n) (1/a) := by
  intro ε hε
  have hp := abs_pos a ha
  have hsq := Scalar.mul_pos hp hp
  have hη : 0<ε*(abs a*abs a)/2 := by
    have := Scalar.mul_pos hε hsq
    grind
  obtain ⟨N,hN⟩ := hs (smaller (abs a/2) (ε*(abs a*abs a)/2)) (by grind [smaller])
  refine ⟨N,?_⟩
  intro n hn
  have ht := hN n hn
  change abs (s n-a)<smaller (abs a/2) (ε*(abs a*abs a)/2) at ht
  have hab : abs (s n-a)=abs (a-s n) := by
    have heq : s n-a=-(a-s n) := by grind
    rw [heq,abs_neg]
  have hlo : abs a/2<abs (s n) := by
    have hb := abs_bound_of_error a (s n)
    rw [←hab] at hb
    grind [smaller]
  have hsp : 0<abs (s n) := by grind
  have hsn : s n≠0 := by intro hz; rw [hz,abs_zero] at hsp; grind
  have hden := Scalar.mul_pos hsp hp
  have hmul := Scalar.mul_lt_mul_of_pos_right hlo hp
  have hmulε := Scalar.mul_lt_mul_of_pos_left hmul hε
  have heq : 1/s n-1/a=(a-s n)/(s n*a) := by grind
  change abs (1/s n-1/a)<ε
  rw [heq,abs_div,abs_mul,←hab]
  apply (Scalar.div_lt_iff hden).mpr
  grind [smaller]

-- Consequence of Rudin Theorem 3.19 for convergent sequences, comparing
-- with a constant upper bound.
theorem seq_le (s : Nat → R) (a B : R) (hs : ConvergesTo realMetric s a)
    (hb : ∀ n, s n≤B) : a≤B := by
  apply Classical.byContradiction
  intro h
  have hp : 0<a-B := by grind
  obtain ⟨N,hN⟩ := hs (a-B) hp
  have ht := hN N (by omega)
  change abs (s N-a)<a-B at ht
  have := (abs_lt _ _).mp ht
  have := hb N
  grind

/-!
## Cauchy Sequences

![Two late terms lie in a ball around the limit; the triangle inequality bounds their distance.](site/diagrams/rudin-cauchy-sequences.svg)

*Late terms cluster together. The amber distance between two terms is bounded by the two blue distances through the limit.*
-/

-- Any two sufficiently late terms are as close as desired.
def IsCauchy (M : Metric (R := R) X) (s : Nat → X) : Prop :=
  ∀ ε : R, 0 < ε → ∃ N : Nat,
    ∀ m n, N ≤ m → N ≤ n → M.dist (s m) (s n) < ε

/-!
### Diameter

![Nested disks and successively shorter diameter segments.](site/diagrams/rudin-shrinking-diameter.svg)

*Nested closed disks shrink to one point; their diameters tend to zero.*
-/

-- The least upper bound of all distances between points of E.
def IsDiameter (M : Metric (R := R) X) (E : PointSet X) (d : R) : Prop :=
  (∀ p q, E p → E q → M.dist p q≤d) ∧
  ∀ b, (∀ p q, E p → E q → M.dist p q≤b) → d≤b

-- Rudin Definition 3.9 with the least-upper-bound property: existence
-- of a finite diameter for a nonempty bounded set.
theorem diameter_exists (M : Metric (R := R) X) (E : PointSet X)
    (nonempty : ∃ p, E p) (bounded : ∃ b, ∀ p q, E p → E q → M.dist p q≤b) :
    ∃ d, IsDiameter M E d := by
  obtain ⟨p,hp⟩ := nonempty
  obtain ⟨b,hb⟩ := bounded
  obtain ⟨d,upper,least⟩ := RealNumbers.leastUpperBound
    (fun r => ∃ p q, E p ∧ E q ∧ M.dist p q=r)
    ⟨M.dist p p,p,p,hp,hp,rfl⟩
    ⟨b,fun r ⟨p,q,hp,hq,he⟩ => he ▸ hb p q hp hq⟩
  exact ⟨d,(fun p q hp hq => upper _ ⟨p,q,hp,hq,rfl⟩),
    fun c hc => least c (fun r ⟨p,q,hp,hq,he⟩ => he ▸ hc p q hp hq)⟩

-- Estimate in the proof of Rudin Theorem 3.10(a): a pairwise distance
-- bound also holds on the closure.
theorem closure_distance_bound (M : Metric (R := R) X) (E : PointSet X) (d : R)
    (bound : ∀ p q, E p → E q → M.dist p q≤d) :
    ∀ p q, Closure M E p → Closure M E q → M.dist p q≤d := by
  intro p q hp hq
  apply Classical.byContradiction
  intro h
  let ε := (M.dist p q-d)/3
  have hε : 0<ε := by dsimp [ε]; grind
  obtain ⟨p',hp',hpp'⟩ := (closure_neighborhood M E p).mp hp ε hε
  obtain ⟨q',hq',hqq'⟩ := (closure_neighborhood M E q).mp hq ε hε
  have h₁ := M.triangle p p' q
  have h₂ := M.triangle p' q' q
  have h₃ := bound p' q' hp' hq'
  rw [M.symm q' q] at h₂
  dsimp [ε] at *
  grind (ematch := 0)

-- Rudin Theorem 3.10(a): taking the closure preserves diameter,
-- expressed through the IsDiameter predicate.
theorem diameter_closure (M : Metric (R := R) X) (E : PointSet X) (d : R)
    (hd : IsDiameter M E d) : IsDiameter M (Closure M E) d := by
  refine ⟨closure_distance_bound M E d hd.1,?_⟩
  intro b hb
  exact hd.2 b (fun p q hp hq => hb p q (Or.inl hp) (Or.inl hq))

-- Rudin Theorem 3.10(b): nonempty nested compact sets with diameters
-- tending to zero have a unique common point.
theorem nested_compact_shrinking (M : Metric (R := R) X) (K : Nat → PointSet X)
    (compact : ∀ n, IsCompact M (K n))
    (nonempty : ∀ n, ∃ p, K n p)
    (nested : ∀ m n, m≤n → ∀ p, K n p → K m p)
    (d : Nat → R) (diameters : ∀ n, IsDiameter M (K n) (d n))
    (shrinking : ConvergesTo realMetric d 0) :
    ∃ p, (∀ n, K n p) ∧ ∀ q, (∀ n, K n q) → q=p := by
  obtain ⟨p,hp⟩ := nested_compact_intersection M K compact nonempty nested
  refine ⟨p,hp,?_⟩
  intro q hq
  apply Classical.byContradiction
  intro hne
  have hdist : 0<M.dist q p := by
    have := M.nonneg q p
    have := M.zero_iff q p
    grind (ematch := 0)
  obtain ⟨N,hN⟩ := shrinking (M.dist q p) hdist
  have h₁ := hN N (by omega)
  change abs (d N-0)<M.dist q p at h₁
  have h₂ := (diameters N).1 q p (hq N) (hp N)
  have := (abs_lt _ _).mp h₁
  grind (ematch := 0)

-- Rudin Theorem 3.11(a): every convergent sequence is Cauchy.
theorem convergent_cauchy (M : Metric (R := R) X) (s : Nat → X) (x : X)
    (h : ConvergesTo M s x) : IsCauchy M s := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by grind [smaller])
  refine ⟨N, ?_⟩
  intro m n hm hn
  have h₁ := hN m hm
  have h₂ := hN n hn
  have ht := M.triangle (s m) x (s n)
  rw [M.symm x (s n)] at ht
  grind [smaller]

/-!
### Cauchy Sequences in a Compact Set
-/

def Tail (s : Nat → X) (N : Nat) : PointSet X := fun p => ∃ n, N≤n ∧ s n=p

-- Finite-maximum helper for the boundedness argument in Rudin Theorem
-- 3.11(c); no separate theorem.
theorem finite_upper_bound (f : Nat → R) (N : Nat) : ∃ B, ∀ n, n≤N → f n≤B := by
  classical
  induction N with
  | zero =>
    refine ⟨f 0,?_⟩
    intro n hn
    have : n=0 := by omega
    subst n
    exact Std.le_refl _
  | succ N ih =>
    obtain ⟨B,hB⟩ := ih
    refine ⟨if B≤f (N+1) then f (N+1) else B,?_⟩
    intro n hn
    by_cases he : n=N+1
    · subst n; split <;> grind
    · have := hB n (by omega)
      split <;> grind

-- Boundedness step in the proof of Rudin Theorem 3.11(c), formulated
-- for any metric space.
theorem cauchy_bounded (M : Metric (R := R) X) (s : Nat → X) (hs : IsCauchy M s) :
    ∃ B, ∀ m n, M.dist (s m) (s n)≤B := by
  classical
  obtain ⟨N,hN⟩ := hs 1 (by grind)
  obtain ⟨B,hB⟩ := finite_upper_bound (fun n => M.dist (s n) (s N)) N
  let C := if B≤1 then 1 else B
  have bound : ∀ n, M.dist (s n) (s N)≤C := by
    intro n
    by_cases hn : n≤N
    · have := hB n hn
      dsimp [C]; split <;> grind (ematch := 0)
    · have := hN n N (by omega) (by omega)
      dsimp [C]; split <;> grind (ematch := 0)
  refine ⟨2*C,?_⟩
  intro m n
  have h₁ := bound m
  have h₂ := bound n
  have ht := M.triangle (s m) (s N) (s n)
  rw [M.symm (s N) (s n)] at ht
  grind (ematch := 0)

-- Rudin Theorem 3.11(b): a Cauchy sequence in a compact set converges
-- to a point of that set.
theorem compact_cauchy_converges (M : Metric (R := R) X) (K : PointSet X)
    (compact : IsCompact M K)
    (s : Nat → X) (inside : ∀ n, K (s n)) (hs : IsCauchy M s) :
    ∃ p, ConvergesTo M s p := by
  obtain ⟨B,hB⟩ := cauchy_bounded M s hs
  have hex : ∀ N, ∃ d, IsDiameter M (Tail s N) d := by
    intro N
    apply diameter_exists M (Tail s N) ⟨s N,N,by omega,rfl⟩
    refine ⟨B,?_⟩
    rintro p q ⟨m,_,rfl⟩ ⟨n,_,rfl⟩
    exact hB m n
  let d (N : Nat) := Classical.choose (hex N)
  have hd (N : Nat) := Classical.choose_spec (hex N)
  let F (N : Nat) := Closure M (Tail s N)
  have hF : ∀ N, IsClosed M (F N) := fun N => closure_closed M (Tail s N)
  have hFK : ∀ N p, F N p → K p := fun N =>
    closure_minimal M (Tail s N) K (compact_closed M K compact) (fun p ⟨n,_,hn⟩ => hn ▸ inside n)
  have hcompact : ∀ N, IsCompact M (F N) := fun N =>
    compact_closed_subset M K (F N) compact (hF N) (hFK N)
  have hnonempty : ∀ N, ∃ p, F N p := fun N => ⟨s N,Or.inl ⟨N,by omega,rfl⟩⟩
  have hnested : ∀ m n, m≤n → ∀ p, F n p → F m p := by
    intro m n hmn
    apply closure_mono M (Tail s n) (Tail s m)
    rintro p ⟨k,hk,he⟩
    exact ⟨k,by omega,he⟩
  have hdiam : ∀ N, IsDiameter M (F N) (d N) := fun N => diameter_closure M (Tail s N) (d N) (hd N)
  have hzero : ConvergesTo realMetric d 0 := by
    intro ε hε
    obtain ⟨N,hN⟩ := hs (ε/2) (by grind)
    refine ⟨N,?_⟩
    intro n hn
    have hlo := (hd n).1 (s n) (s n) ⟨n,by omega,rfl⟩ ⟨n,by omega,rfl⟩
    rw [(M.zero_iff (s n) (s n)).mpr rfl] at hlo
    have hhi : d n≤ε/2 := by
      apply (hd n).2
      rintro p q ⟨i,hi,rfl⟩ ⟨j,hj,rfl⟩
      exact Scalar.le_of_lt (hN i j (by omega) (by omega))
    change abs (d n-0)<ε
    rw [abs_lt]
    change 0≤d n at hlo
    grind (ematch := 0)
  obtain ⟨p,hp,_⟩ := nested_compact_shrinking M F hcompact hnonempty hnested d hdiam hzero
  refine ⟨p,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := hzero ε hε
  refine ⟨N,?_⟩
  intro n hn
  have h₁ := (hdiam N).1 (s n) p (Or.inl ⟨n,hn,rfl⟩) (hp N)
  have h₂ := hN N (by omega)
  change abs (d N-0)<ε at h₂
  have := (abs_lt _ _).mp h₂
  grind (ematch := 0)

/-!
### Completeness of the Real Line
-/

-- Every Cauchy sequence has a limit in the space.
def IsComplete (M : Metric (R := R) X) : Prop :=
  ∀ s, IsCauchy M s → ∃ x, ConvergesTo M s x

-- Rudin Theorem 3.11(c), k = 1, expressed using completeness from
-- Definition 3.12.
theorem real_complete : IsComplete (realMetric (R:=R)) := by
  intro s hs
  obtain ⟨B,hB⟩ := cauchy_bounded realMetric s hs
  let E : PointSet R := fun p => ∃ n, s n=p
  have bounded : ∀ p, E p → s 0-B≤p ∧ p≤s 0+B := by
    rintro p ⟨n,rfl⟩
    have hd := hB n 0
    change abs (s n-s 0)≤B at hd
    unfold abs at hd
    split at hd <;> constructor <;> grind (ematch := 0)
  exact compact_cauchy_converges realMetric (Closure realMetric E)
    (bounded_closure_compact E (s 0-B) (s 0+B) bounded)
    s (fun n => Or.inl ⟨n,rfl⟩) hs

/-!
### Monotonic Sequences
-/

def Increasing (s : Nat → R) : Prop := ∀ m n, m ≤ n → s m ≤ s n

-- Rudin Theorem 3.14, bounded-to-convergent direction for increasing
-- real sequences.
theorem increasing_bounded_converges (s : Nat → R)
    (hs : Increasing s) (bounded : ∃ b, ∀ n, s n ≤ b) :
    ∃ l, ConvergesTo realMetric s l := by
  obtain ⟨l, upper, least⟩ := RealNumbers.leastUpperBound
    (fun x => ∃ n, s n=x) ⟨s 0, 0, rfl⟩
    (by obtain ⟨b, hb⟩ := bounded; exact ⟨b, fun x ⟨n, hn⟩ => hn ▸ hb n⟩)
  refine ⟨l, ?_⟩
  intro ε hε
  have near : ∃ N, l-ε<s N := by
    apply Classical.byContradiction
    intro h
    have hb : ∀ x, (∃ n, s n=x) → x≤l-ε := by
      intro x ⟨n, hn⟩
      have : ¬ l-ε<s n := fun ht => h ⟨n, ht⟩
      grind [smaller]
    have := least (l-ε) hb
    grind [smaller]
  obtain ⟨N, hN⟩ := near
  refine ⟨N, ?_⟩
  intro n hn
  have h₁ := hs N n hn
  have h₂ := upper (s n) ⟨n, rfl⟩
  change abs (s n-l)<ε
  rw [abs_lt]
  grind [smaller]

/-!
## Series

![Shrinking terms add to partial sums that approach a finite limit.](site/diagrams/rudin-series.svg)

*The blocks are successive terms. Their cumulative lengths give the dots below, approaching the dashed limit.*
-/

def partialSum (a : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => partialSum a n + a n

-- Finite-sum identity underlying Rudin Theorem 3.47; this is not yet
-- the infinite-series limit statement.
theorem partialSum_scale (c : R) (a : Nat → R) (n : Nat) :
    partialSum (fun k => c * a k) n = c * partialSum a n := by
  induction n with
  | zero => simp only [partialSum]; grind
  | succ n ih => simp only [partialSum, ih]; grind [smaller]

-- The partial sums are Cauchy: far-out finite blocks have small sums.
def CauchySeries (a : Nat → R) : Prop :=
  IsCauchy realMetric (partialSum a)

-- Rudin Theorem 3.22: the Cauchy criterion for series, expressed as the
-- Cauchy property of partial sums (Definition 3.21).
theorem series_cauchy_iff_converges (a : Nat → R) :
    CauchySeries a ↔ ∃ l, ConvergesTo realMetric (partialSum a) l := by
  constructor
  · exact real_complete (partialSum a)
  · rintro ⟨l,hl⟩
    exact convergent_cauchy _ _ _ hl

-- Proof step for Rudin Theorem 3.24: partial sums of nonnegative terms
-- are increasing.
theorem partialSum_increasing (a : Nat → R) (ha : ∀ n, 0≤a n) :
    Increasing (partialSum a) := by
  intro m n hmn
  induction n with
  | zero =>
    have : m=0 := by omega
    subst m; grind
  | succ n ih =>
    by_cases he : m=n+1
    · subst m; grind
    have ih := ih (by omega)
    have := ha n
    simp only [partialSum]
    grind

-- Rudin Theorem 3.24, bounded-partial-sums implies convergence
-- direction.
theorem nonnegative_series_converges (a : Nat → R) (ha : ∀ n, 0≤a n)
    (bounded : ∃ B, ∀ n, partialSum a n≤B) :
    ∃ l, ConvergesTo realMetric (partialSum a) l :=
  increasing_bounded_converges _ (partialSum_increasing a ha) bounded

-- Finite-tail comparison used in Rudin Theorem 3.25(a); extracted
-- helper.
theorem partialSum_tail_le (a c : Nat → R) (N : Nat)
    (h : ∀ n, N≤n → a n≤c n) (k : Nat) :
    partialSum a (N+k)-partialSum a N ≤ partialSum c (N+k)-partialSum c N := by
  induction k with
  | zero => simp only [Nat.add_zero]; grind
  | succ k ih =>
    have := h (N+k) (by omega)
    simp only [partialSum]
    grind

-- Finite triangle inequality used in Rudin Theorems 3.25(a) and 3.45;
-- extracted helper.
theorem partialSum_abs_tail (a : Nat → R) (n k : Nat) :
    abs (partialSum a (n+k)-partialSum a n) ≤
      partialSum (fun j => abs (a j)) (n+k)-partialSum (fun j => abs (a j)) n := by
  induction k with
  | zero => simp only [Nat.add_zero,Scalar.sub_self,abs_zero]; grind
  | succ k ih =>
    have ht := abs_triangle (partialSum a (n+k)-partialSum a n) (a (n+k))
    have heq : partialSum a (n+k)-partialSum a n+a (n+k)=partialSum a (n+k)+a (n+k)-partialSum a n := by grind
    rw [heq] at ht
    simp only [partialSum]
    grind

-- Rudin Theorem 3.25(a): convergence by comparison with an eventually
-- dominating series.
theorem series_comparison (a c : Nat → R) (N₀ : Nat)
    (h : ∀ n, N₀≤n → abs (a n)≤c n)
    (hc : ∃ l, ConvergesTo realMetric (partialSum c) l) :
    ∃ l, ConvergesTo realMetric (partialSum a) l := by
  apply (series_cauchy_iff_converges a).mp
  have hc := (series_cauchy_iff_converges c).mpr hc
  intro ε hε
  obtain ⟨N,hN⟩ := hc ε hε
  refine ⟨max N₀ N,?_⟩
  intro m n hm hn
  have ordered : ∀ m n, max N₀ N≤m → m≤n → abs (partialSum a n-partialSum a m)<ε := by
    intro m n hm hmn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h₁ := partialSum_abs_tail a m k
    have h₂ := partialSum_tail_le (fun j => abs (a j)) c m
      (fun j hj => h j (by omega)) k
    have h₃ := hN (m+k) m (by omega) (by omega)
    change abs (partialSum c (m+k)-partialSum c m)<ε at h₃
    have := (abs_lt _ _).mp h₃
    grind (ematch := 0)
  change abs (partialSum a m-partialSum a n)<ε
  by_cases hmn : n≤m
  · exact ordered n m hn hmn
  · have ht := ordered m n hm (by omega)
    have heq : partialSum a m-partialSum a n=-(partialSum a n-partialSum a m) := by grind
    simpa only [heq,abs_neg] using ht

-- Consequence of Rudin Theorem 1.33(c), real case, by induction on the
-- exponent.
theorem abs_pow (x : R) (n : Nat) : abs (x^n)=(abs x)^n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero]; unfold abs; grind
  | succ n ih => simp only [Lean.Grind.Semiring.pow_succ,abs_mul,ih]

-- Elementary ordered-arithmetic helper; no separate Rudin theorem is
-- claimed.
theorem pow_nonneg (x : R) (hx : 0≤x) (n : Nat) : 0≤x^n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero]; grind
  | succ n ih => simpa only [Lean.Grind.Semiring.pow_succ] using Scalar.mul_nonneg ih hx

/-!
## Series of Nonnegative Terms

![Increasing partial sums stay below a fixed upper bound.](site/diagrams/rudin-nonnegative-series.svg)

*Nonnegative terms make the partial sums rise. Here they remain below the dashed upper bound and settle toward a limit.*
-/

-- Finite geometric-sum identity in the proof of Rudin Theorem 3.26,
-- multiplied by 1 - q.
theorem geometric_sum_mul (q : R) (n : Nat) :
    (1-q)*partialSum (fun k => q^k) n=1-q^n := by
  induction n with
  | zero => simp only [partialSum,Lean.Grind.Semiring.pow_zero]; grind
  | succ n ih =>
    simp only [partialSum,Lean.Grind.Semiring.pow_succ]
    grind

-- Partial-sum estimate from Rudin Theorem 3.26; this lemma does not
-- assert the infinite sum's value.
theorem geometric_partial_bound (q : R) (hq : 0≤q) (hqlt : q<1) (n : Nat) :
    partialSum (fun k => q^k) n≤1/(1-q) := by
  have hp := pow_nonneg q hq n
  have hi := geometric_sum_mul q n
  apply (Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right
    (show 0<1-q from by grind)).mp
  grind

/-!
## Factorial Coefficients
-/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def reciprocalFactorial : Nat → R
  | 0 => 1
  | n + 1 => reciprocalFactorial n / (n + 1 : Nat)

-- Representation helper for Rudin Definition 3.30: the recursively
-- defined coefficient equals 1/n!.
theorem reciprocalFactorial_eq (n : Nat) :
    (reciprocalFactorial n : R)=1/(factorial n : R) := by
  induction n with
  | zero => simp only [reciprocalFactorial,factorial]; grind
  | succ n ih =>
    simp only [reciprocalFactorial,factorial,Scalar.natCast_mul,ih]
    grind

-- Arithmetic helper for Rudin Definition 3.30: the terms 1/n! are
-- positive.
theorem reciprocalFactorial_pos (n : Nat) : 0 < (reciprocalFactorial n : R) := by
  induction n with
  | zero => simp only [reciprocalFactorial]; grind [smaller]
  | succ n ih =>
    have hp : (0:R)<(n+1:Nat) := Scalar.natCast_pos.mpr (by omega)
    simpa only [reciprocalFactorial, Scalar.div_def] using Scalar.mul_pos ih (Scalar.inv_pos.mpr hp)

-- Factorial identity used after Rudin Definition 3.30; extracted
-- arithmetic helper.
theorem reciprocalFactorial_step (n : Nat) :
    reciprocalFactorial (n + 1) * (n + 1 : Nat) = (reciprocalFactorial n : R) := by
  simp only [reciprocalFactorial]
  exact Scalar.div_mul_cancel (by have := Scalar.natCast_pos (R:=R) (a:=n+1) |>.mpr (Nat.zero_lt_succ n); grind)

/-!
## The Ratio Test

![A row of disks whose radii shrink by a fixed factor.](site/diagrams/rudin-ratio-test.svg)

*A fixed ratio below one gives a geometric bound on the tail.*
-/

-- Geometric-tail estimate in the proof of Rudin Theorem 3.34(a).
theorem ratio_geometric_bound (a : Nat → R) (N : Nat) (q : R) (hq : 0≤q)
    (ratio : ∀ n, N≤n → a (n+1)≤q*a n) (k : Nat) :
    a (N+k)≤a N*q^k := by
  induction k with
  | zero => simp only [Nat.add_zero,Lean.Grind.Semiring.pow_zero]; grind
  | succ k ih =>
    have h₁ := ratio (N+k) (by omega)
    have h₂ := Scalar.mul_le_mul_of_nonneg_left ih hq
    simp only [Nat.add_succ,Lean.Grind.Semiring.pow_succ]
    grind

-- Finite-sum indexing helper for Rudin Theorem 3.34(a); no separate
-- numbered theorem.
theorem partialSum_shift (a : Nat → R) (N k : Nat) :
    partialSum a (N+k)=partialSum a N+partialSum (fun j => a (N+j)) k := by
  induction k with
  | zero => simp only [Nat.add_zero,partialSum]; grind
  | succ k ih => simp only [partialSum]; grind

-- Partial-sum bound extracted from the proof of Rudin Theorem 3.34(a),
-- for nonnegative terms and a fixed eventual ratio bound.
theorem series_bounded_of_ratio (a : Nat → R) (ha : ∀ n, 0≤a n)
    (N : Nat) (q : R) (hq : 0≤q) (hqlt : q<1)
    (ratio : ∀ n, N≤n → a (n+1)≤q*a n) :
    ∃ B, ∀ n, partialSum a n≤B := by
  refine ⟨partialSum a N+a N/(1-q),?_⟩
  intro n
  have hden : 0<1-q := by grind
  have hrem : 0≤a N/(1-q) := by
    rw [Scalar.div_def]
    exact Scalar.mul_nonneg (ha N) (Scalar.le_of_lt (Scalar.inv_pos.mpr hden))
  by_cases hn : N≤n
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    have h₁ := partialSum_tail_le (fun j => a (N+j)) (fun j => a N*q^j) 0
      (fun j _ => ratio_geometric_bound a N q hq ratio j) k
    simp only [Nat.zero_add,partialSum] at h₁
    rw [partialSum_scale] at h₁
    have h₂ := Scalar.mul_le_mul_of_nonneg_left (geometric_partial_bound q hq hqlt k) (ha N)
    rw [partialSum_shift]
    grind
  · have h₁ := partialSum_increasing a ha n N (by omega)
    grind

-- Rudin Theorem 3.34(a), sufficient fixed-ratio form for nonnegative
-- terms; the limsup formulation and divergence clause are not
-- formalized here.
theorem ratio_test (a : Nat → R) (ha : ∀ n, 0≤a n)
    (N : Nat) (q : R) (hq : 0≤q) (hqlt : q<1)
    (ratio : ∀ n, N≤n → a (n+1)≤q*a n) :
    ∃ l, ConvergesTo realMetric (partialSum a) l :=
  nonnegative_series_converges a ha (series_bounded_of_ratio a ha N q hq hqlt ratio)

-- Special case of the estimate for Rudin Theorem 3.34(a), with eventual
-- ratio at most 1/2.
theorem series_bounded_of_half (a : Nat → R) (ha : ∀ n, 0≤a n)
    (N : Nat) (half : ∀ n, N≤n → 2*a (n+1)≤a n) :
    ∃ B, ∀ n, partialSum a n≤B := by
  apply series_bounded_of_ratio a ha N (1/2) (by grind) (by grind)
  intro n hn
  have := half n hn
  grind

/-!
## Power Series

![Exponential partial sums approaching the exponential curve.](site/diagrams/rudin-power-series.svg)

*Adding more terms brings the amber partial sums toward the blue exponential curve.*
-/

def expPartial (x : R) (n : Nat) : R :=
  partialSum (fun k => x ^ k * reciprocalFactorial k) n

/-!
## Absolute Convergence

![Alternating signed terms above, and their absolute values below.](site/diagrams/rudin-absolute-series.svg)

*Taking absolute values removes cancellation. If the lower series converges, so does the upper one.*
-/

-- Rudin Theorem 3.45, real case: absolute convergence implies
-- convergence.
theorem absolute_convergence (a : Nat → R)
    (ha : ∃ l, ConvergesTo realMetric (partialSum (fun n => abs (a n))) l) :
    ∃ l, ConvergesTo realMetric (partialSum a) l :=
  series_comparison a (fun n => abs (a n)) 0 (fun _ _ => Std.le_refl _) ha

/-!
### Convergence of the Exponential Series
-/

-- Helper for the convergence assertion after Rudin Chapter 8, (25), p.
-- 178: ratio-test bounds for nonnegative x.
theorem exp_terms_bounded (x : R) (hx : 0≤x) :
    ∃ B, ∀ n, expPartial x n≤B := by
  let a := fun n => x^n*reciprocalFactorial n
  have ha : ∀ n, 0≤a n := fun n => Scalar.mul_nonneg (pow_nonneg x hx n)
    (Scalar.le_of_lt (reciprocalFactorial_pos n))
  obtain ⟨N,hN⟩ := exists_nat_gt (2*x)
  apply series_bounded_of_half a ha N
  intro n hn
  have hc := Scalar.natCast_le_natCast (R:=R) |>.mpr hn
  have hnpos : (0:R)<((n+1:Nat):R) := Scalar.natCast_pos.mpr (by omega)
  have hstep : a (n+1)*((n+1:Nat):R)=a n*x := by
    have h := reciprocalFactorial_step (R:=R) n
    dsimp [a]
    rw [Lean.Grind.Semiring.pow_succ]
    grind
  have hmul := Scalar.mul_le_mul_of_nonneg_left
    (show 2*x≤((n+1:Nat):R) from by grind) (ha n)
  apply (Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right hnpos).mp
  grind

-- Rudin Chapter 8, convergence assertion after (25), p. 178, restricted
-- to real x; uses Theorems 3.34(a) and 3.45.
theorem exp_series_exists (x : R) : ∃ l, ConvergesTo realMetric (expPartial x) l := by
  have habs : ∀ n, abs (x^n*reciprocalFactorial n)=(abs x)^n*reciprocalFactorial n := by
    intro n
    rw [abs_mul,abs_pow]
    have hpos := reciprocalFactorial_pos (R:=R) n
    have heq : abs (reciprocalFactorial n : R)=reciprocalFactorial n := by
      unfold abs; rw [if_pos (by grind)]
    rw [heq]
  apply absolute_convergence (fun n => x^n*reciprocalFactorial n)
  have hc := nonnegative_series_converges (fun n => (abs x)^n*reciprocalFactorial n)
    (fun n => Scalar.mul_nonneg (pow_nonneg _ (abs_nonneg x) n)
      (Scalar.le_of_lt (reciprocalFactorial_pos n)))
    (exp_terms_bounded _ (abs_nonneg x))
  simpa only [habs] using hc

def expSeries (x : R) : R := Classical.choose (exp_series_exists x)

-- Rudin Chapter 8, (25), p. 178: the exponential series defines E(x);
-- Lean choice records its established limit.
theorem expSeries_limit (x : R) : ConvergesTo realMetric (expPartial x) (expSeries x) :=
  Classical.choose_spec (exp_series_exists x)

-- Special case of the observation after Rudin Definition 3.5: a
-- subsequence of a convergent sequence has the same limit.
theorem seq_succ (s : Nat → R) (a : R) (hs : ConvergesTo realMetric s a) :
    ConvergesTo realMetric (fun n => s (n+1)) a := by
  intro ε hε
  obtain ⟨N,hN⟩ := hs ε hε
  exact ⟨N,fun n hn => hN (n+1) (by omega)⟩

-- Consequence of Rudin Theorem 3.19 for convergent sequences, comparing
-- with a constant lower bound.
theorem seq_ge (s : Nat → R) (a B : R) (hs : ConvergesTo realMetric s a)
    (hb : ∀ n, B≤s n) : B≤a := by
  apply Classical.byContradiction
  intro h
  have hp : 0<B-a := by grind
  obtain ⟨N,hN⟩ := hs (B-a) hp
  have ht := hN N (by omega)
  change abs (s N-a)<B-a at ht
  have := (abs_lt _ _).mp ht
  have := hb N
  grind

-- Consequence of Rudin Chapter 8, (25), for nonnegative x: the constant
-- term is 1 and the other terms are nonnegative.
theorem expSeries_ge_one (x : R) (hx : 0≤x) : 1≤expSeries x := by
  apply seq_ge (fun n => expPartial x (n+1)) _ _ (seq_succ _ _ (expSeries_limit x))
  intro n
  have hi := partialSum_increasing (fun k => x^k*reciprocalFactorial k)
    (fun k => Scalar.mul_nonneg (pow_nonneg x hx k) (Scalar.le_of_lt (reciprocalFactorial_pos k))) 1 (n+1) (by omega)
  have hstart : expPartial x 1=1 := by
    simp only [expPartial,partialSum,reciprocalFactorial,Lean.Grind.Semiring.pow_zero]
    grind
  change expPartial x 1≤expPartial x (n+1) at hi
  rwa [hstart] at hi

/-!
# Continuity

## Limits of Functions

![A punctured input neighborhood maps inside a prescribed ball around the output limit.](site/diagrams/rudin-function-limits.svg)

*A small punctured input neighborhood maps inside the requested output ball. The hollow input point is excluded.*
-/

-- Near p, but excluding p, the outputs approach q.
def HasLimit (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) (q : Y) : Prop :=
  ∀ ε, 0<ε → ∃ δ, 0<δ ∧ ∀ x, E x → 0<M.dist x p → M.dist x p<δ → N.dist (f x) q<ε

-- Rudin Theorem 1.20(a), reciprocal form used in the proofs of Theorems
-- 3.2(d) and 4.2.
theorem reciprocal_nat_small (ε : R) (hε : 0<ε) :
    ∃ N : Nat, ∀ n, N≤n → 1/((n+1:Nat):R)<ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  refine ⟨N,?_⟩
  intro n hn
  have hcast := Scalar.natCast_le_natCast (R:=R) |>.mpr hn
  have hpos : (0:R)<((n+1:Nat):R) := Scalar.natCast_pos.mpr (by omega)
  apply (Scalar.div_lt_iff hpos).mpr
  have h := Scalar.mul_lt_mul_of_pos_right hN hε
  have hc := Scalar.mul_le_mul_of_nonneg_right hcast (Scalar.le_of_lt hε)
  grind (ematch := 0)

-- Rudin Theorem 4.2: sequential characterization of a function limit.
-- Here HasLimit is the punctured epsilon-delta predicate even without a
-- limit-point hypothesis.
theorem limit_iff_sequences (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) (q : Y) :
    HasLimit M N E f p q ↔
      ∀ s : Nat → X, (∀ n, E (s n)) → (∀ n, s n≠p) →
        ConvergesTo M s p → ConvergesTo N (fun n => f (s n)) q := by
  constructor
  · intro hf s hin hne hs ε hε
    obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
    obtain ⟨K,hK⟩ := hs δ hδ
    refine ⟨K,?_⟩
    intro n hn
    apply hfδ (s n) (hin n) ?_ (hK n hn)
    have := M.nonneg (s n) p
    have := M.zero_iff (s n) p
    have := hne n
    grind (ematch := 0)
  · intro hseq
    apply Classical.byContradiction
    intro hnot
    obtain ⟨ε,hbad⟩ := Classical.not_forall.mp hnot
    have hε : 0<ε := Classical.byContradiction
      (fun h => hbad (fun hpos => False.elim (h hpos)))
    have bad : ∀ δ, 0<δ → ∃ x, E x ∧ 0<M.dist x p ∧ M.dist x p<δ ∧ ¬N.dist (f x) q<ε := by
      intro δ hδ
      apply Classical.byContradiction
      intro hn
      apply hbad
      intro _
      refine ⟨δ,hδ,?_⟩
      intro x hx hp hd
      exact Classical.byContradiction (fun h => hn ⟨x,hx,hp,hd,h⟩)
    have radii : ∀ n : Nat, (0:R)<1/((n+1:Nat):R) := by
      intro n
      have hp : (0:R)<((n+1:Nat):R) := Scalar.natCast_pos.mpr (by omega)
      rw [Scalar.div_def]
      exact Scalar.mul_pos (by grind) (Scalar.inv_pos.mpr hp)
    let s (n : Nat) := Classical.choose (bad (1/((n+1:Nat):R)) (radii n))
    have spec (n : Nat) := Classical.choose_spec (bad (1/((n+1:Nat):R)) (radii n))
    have hs : ConvergesTo M s p := by
      intro η hη
      obtain ⟨K,hK⟩ := reciprocal_nat_small η hη
      refine ⟨K,?_⟩
      intro n hn
      have h₁ := (spec n).2.2.1
      have h₂ := hK n hn
      change M.dist (s n) p<η
      grind (ematch := 0)
    have hne : ∀ n, s n≠p := by
      intro n he
      have h := (spec n).2.1
      change 0<M.dist (s n) p at h
      rw [he,(M.zero_iff p p).mpr rfl] at h
      grind (ematch := 0)
    obtain ⟨K,hK⟩ := hseq s (fun n => (spec n).1) hne hs ε hε
    exact (spec K).2.2.2 (hK K (by omega))

-- Rudin Theorem 3.2(d), with the proof's stronger choice of terms
-- distinct from the limit point.
theorem limitPoint_sequence (M : Metric (R:=R) X) (E : PointSet X) (p : X)
    (hp : LimitPoint M E p) :
    ∃ s : Nat → X, (∀ n, E (s n)) ∧ (∀ n, s n≠p) ∧ ConvergesTo M s p := by
  have radii : ∀ n : Nat, (0:R)<1/((n+1:Nat):R) := by
    intro n
    rw [Scalar.div_def]
    exact Scalar.mul_pos (by grind) (Scalar.inv_pos.mpr (Scalar.natCast_pos.mpr (by omega)))
  let s (n : Nat) := Classical.choose (hp (1/((n+1:Nat):R)) (radii n))
  have spec (n : Nat) := Classical.choose_spec (hp (1/((n+1:Nat):R)) (radii n))
  refine ⟨s,(fun n => (spec n).1),(fun n => (spec n).2.1),?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := reciprocal_nat_small ε hε
  refine ⟨N,?_⟩
  intro n hn
  have h₁ := (spec n).2.2
  change M.dist p (s n)<1/((n+1:Nat):R) at h₁
  rw [M.symm] at h₁
  have h₂ := hN n hn
  grind (ematch := 0)

-- Rudin, corollary to Theorem 4.2: uniqueness of a function limit at a
-- limit point of its domain.
theorem function_limit_unique (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) (q r : Y) (hp : LimitPoint M E p)
    (hq : HasLimit M N E f p q) (hr : HasLimit M N E f p r) : q=r := by
  obtain ⟨s,hin,hne,hs⟩ := limitPoint_sequence M E p hp
  exact limit_unique N (fun n => f (s n)) q r
    ((limit_iff_sequences M N E f p q).mp hq s hin hne hs)
    ((limit_iff_sequences M N E f p r).mp hr s hin hne hs)

/-!
### Arithmetic of Limits
-/

-- Immediate consequence of Rudin Definition 4.1 for a constant
-- function; no separate theorem.
theorem hasLimit_const (M : Metric (R:=R) X) (E : PointSet X) (p : X) (a : R) :
    HasLimit M realMetric E (fun _ => a) p a := by
  intro ε hε
  exact ⟨1,by grind,fun _ _ _ _ => by change abs (a-a)<ε; simpa [Scalar.sub_self,abs_zero] using hε⟩

-- Rudin Theorem 4.4(a), real case, expressed with the punctured
-- HasLimit predicate.
theorem hasLimit_add (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X) (a b : R)
    (hf : HasLimit M realMetric E f p a) (hg : HasLimit M realMetric E g p b) :
    HasLimit M realMetric E (fun x => f x+g x) p (a+b) := by
  apply (limit_iff_sequences M realMetric E _ p _).mpr
  intro s hin hne hs
  exact seq_add _ _ _ _ ((limit_iff_sequences M realMetric E f p a).mp hf s hin hne hs)
    ((limit_iff_sequences M realMetric E g p b).mp hg s hin hne hs)

-- Rudin Theorem 4.4(b), real case, expressed with the punctured
-- HasLimit predicate.
theorem hasLimit_mul (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X) (a b : R)
    (hf : HasLimit M realMetric E f p a) (hg : HasLimit M realMetric E g p b) :
    HasLimit M realMetric E (fun x => f x*g x) p (a*b) := by
  apply (limit_iff_sequences M realMetric E _ p _).mpr
  intro s hin hne hs
  exact seq_mul _ _ _ _ ((limit_iff_sequences M realMetric E f p a).mp hf s hin hne hs)
    ((limit_iff_sequences M realMetric E g p b).mp hg s hin hne hs)

-- Rudin Theorem 4.4(c), real case with numerator 1; eventual
-- nonvanishing suffices for Lean's total reciprocal.
theorem hasLimit_inv (M : Metric (R:=R) X) (E : PointSet X) (f : X → R) (p : X) (a : R)
    (hf : HasLimit M realMetric E f p a) (ha : a≠0) :
    HasLimit M realMetric E (fun x => 1/f x) p (1/a) := by
  apply (limit_iff_sequences M realMetric E _ p _).mpr
  intro s hin hne hs
  exact seq_inv _ _ ha ((limit_iff_sequences M realMetric E f p a).mp hf s hin hne hs)

-- Rudin Theorem 4.4(c), real case; the nonzero limiting denominator
-- ensures nonvanishing sufficiently near the limit point.
theorem hasLimit_div (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X) (a b : R)
    (hf : HasLimit M realMetric E f p a) (hg : HasLimit M realMetric E g p b) (hb : b≠0) :
    HasLimit M realMetric E (fun x => f x/g x) p (a/b) := by
  have h := hasLimit_mul M E f (fun x => 1/g x) p a (1/b) hf (hasLimit_inv M E g p b hg hb)
  have heq : ∀ u v : R, u*(1/v)=u/v := by intro u v; grind
  simpa only [heq] using h

-- Consequence of Rudin Theorem 4.4(a),(b), real case: subtraction of
-- limits.
theorem hasLimit_sub (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X) (a b : R)
    (hf : HasLimit M realMetric E f p a) (hg : HasLimit M realMetric E g p b) :
    HasLimit M realMetric E (fun x => f x-g x) p (a-b) := by
  have h := hasLimit_add M E f (fun x => -1*g x) p a (-1*b) hf
    (hasLimit_mul M E (fun _ => -1) g p (-1) b (hasLimit_const M E p (-1)) hg)
  have heq : ∀ u v : R, u+ -1*v=u-v := by intro u v; grind
  simpa only [heq] using h

/-!
## Continuous Functions

![Three neighborhoods illustrate the composition of two continuous functions.](site/diagrams/rudin-continuous-composition.svg)

*Each map sends a small neighborhood into the next. Passing through both maps keeps the final outputs close together.*
-/

-- Inputs close to p have outputs close to f(p).
def ContinuousAt (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) : Prop :=
  ∀ ε, 0<ε → ∃ δ, 0<δ ∧ ∀ x, E x → M.dist x p<δ → N.dist (f x) (f p)<ε

-- Forward direction of Rudin Theorem 4.6, expressed with the punctured
-- HasLimit predicate.
theorem continuous_to_limit (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) (hf : ContinuousAt M N E f p) :
    HasLimit M N E f p (f p) := by
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
  exact ⟨δ,hδ,fun x hx _ hd => hfδ x hx hd⟩

-- Reverse direction of Rudin Theorem 4.6, expressed with the punctured
-- HasLimit predicate.
theorem continuous_of_limit (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) (hf : HasLimit M N E f p (f p)) :
    ContinuousAt M N E f p := by
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx hd
  by_cases he : x=p
  · subst x; simpa [(N.zero_iff (f p) (f p)).mpr rfl] using hε
  · apply hfδ x hx ?_ hd
    have := M.nonneg x p
    have := M.zero_iff x p
    grind (ematch := 0)

-- Rudin Theorem 4.6: at a limit point, continuity is equivalent to the
-- function limit equaling the value.
theorem continuous_iff_limit (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (E : PointSet X) (f : X → Y) (p : X) (_hp : LimitPoint M E p) :
    ContinuousAt M N E f p ↔ HasLimit M N E f p (f p) :=
  ⟨continuous_to_limit M N E f p,continuous_of_limit M N E f p⟩

-- Rudin Theorem 4.7: composition of continuous functions, with the
-- outer function continuous on the inner function's image.
theorem continuous_comp (M : Metric (R:=R) X) (N : Metric (R:=R) Y) (P : Metric (R:=R) Z)
    (E : PointSet X) (f : X → Y) (g : Y → Z) (p : X)
    (hf : ContinuousAt M N E f p)
    (hg : ContinuousAt N P (fun y => ∃ x, E x ∧ f x=y) g (f p)) :
    ContinuousAt M P E (fun x => g (f x)) p := by
  intro ε hε
  obtain ⟨η,hη,hgη⟩ := hg ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf η hη
  exact ⟨δ,hδ,fun x hx hd => hgη (f x) ⟨x,hx,rfl⟩ (hfδ x hx hd)⟩

-- Rudin Theorem 4.8: continuity iff every open set has open inverse
-- image.
theorem continuous_iff_open_preimage (M : Metric (R:=R) X) (N : Metric (R:=R) Y) (f : X → Y) :
    (∀ p, ContinuousAt M N (fun _ => True) f p) ↔
      ∀ V, IsOpen N V → IsOpen M (fun x => V (f x)) := by
  constructor
  · intro hf V hV p hp
    obtain ⟨ε,hε,hinside⟩ := hV (f p) hp
    obtain ⟨δ,hδ,hfδ⟩ := hf p ε hε
    refine ⟨δ,hδ,?_⟩
    intro x hx
    apply hinside (f x)
    change N.dist (f p) (f x)<ε
    rw [N.symm]
    apply hfδ x trivial
    change M.dist p x<δ at hx
    rwa [M.symm]
  · intro hopen p ε hε
    obtain ⟨δ,hδ,hinside⟩ := hopen (Neighborhood N (f p) ε) (neighborhood_open N (f p) ε)
      p (by change N.dist (f p) (f p)<ε; simpa [(N.zero_iff (f p) (f p)).mpr rfl] using hε)
    refine ⟨δ,hδ,?_⟩
    intro x _ hx
    have h := hinside x (by change M.dist p x<δ; rwa [M.symm])
    change N.dist (f x) (f p)<ε
    change N.dist (f p) (f x)<ε at h
    rwa [N.symm]

-- Rudin Theorem 4.9, sum clause, in pointwise real form.
theorem continuous_add (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X)
    (hf : ContinuousAt M realMetric E f p) (hg : ContinuousAt M realMetric E g p) :
    ContinuousAt M realMetric E (fun x => f x+g x) p :=
  continuous_of_limit M realMetric E _ p (hasLimit_add M E f g p (f p) (g p)
    (continuous_to_limit M realMetric E f p hf) (continuous_to_limit M realMetric E g p hg))

-- Rudin Theorem 4.9, product clause, in pointwise real form.
theorem continuous_mul (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X)
    (hf : ContinuousAt M realMetric E f p) (hg : ContinuousAt M realMetric E g p) :
    ContinuousAt M realMetric E (fun x => f x*g x) p :=
  continuous_of_limit M realMetric E _ p (hasLimit_mul M E f g p (f p) (g p)
    (continuous_to_limit M realMetric E f p hf) (continuous_to_limit M realMetric E g p hg))

-- Rudin Theorem 4.9, quotient clause, in pointwise real form with a
-- nonzero denominator at the point.
theorem continuous_div (M : Metric (R:=R) X) (E : PointSet X) (f g : X → R) (p : X)
    (hf : ContinuousAt M realMetric E f p) (hg : ContinuousAt M realMetric E g p) (hgp : g p≠0) :
    ContinuousAt M realMetric E (fun x => f x/g x) p :=
  continuous_of_limit M realMetric E _ p (hasLimit_div M E f g p (f p) (g p)
    (continuous_to_limit M realMetric E f p hf) (continuous_to_limit M realMetric E g p hg) hgp)

/-!
## Continuity and Compactness

![A closed disk maps continuously to a closed oval.](site/diagrams/rudin-compact-image.svg)

*A continuous map carries a compact set to a compact image.*
-/

-- Rudin Theorem 4.14: the continuous image of a compact space is
-- compact.
theorem continuous_image_compact (M : Metric (R:=R) X) (N : Metric (R:=R) Y)
    (f : X → Y) (hf : ∀ p, ContinuousAt M N (fun _ => True) f p)
    (compact : IsCompact M (fun _ => True)) : IsCompact N (fun y => ∃ x, f x=y) := by
  intro I U hopen cover
  obtain ⟨selected,hselected⟩ := compact I (fun i x => U i (f x))
    (fun i => (continuous_iff_open_preimage M N f).mp hf (U i) (hopen i))
    (fun x _ => cover (f x) ⟨x,rfl⟩)
  refine ⟨selected,?_⟩
  rintro y ⟨x,rfl⟩
  exact hselected x trivial

-- The outputs approach a as h approaches zero, including f(0) = a.
def LimitAtZero (f : R → R) (a : R) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ h, abs h < δ → abs (f h - a) < ε

-- Representation helper for Rudin Definitions 4.1 and 4.5: LimitAtZero
-- includes h = 0, so it also requires f(0) = a.
theorem limitAtZero_iff (f : R → R) (a : R) :
    LimitAtZero f a ↔ HasLimit realMetric realMetric (fun _ => True) f 0 a ∧ f 0=a := by
  constructor
  · intro hf
    constructor
    · intro ε hε
      obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
      refine ⟨δ,hδ,?_⟩
      intro h _ _ hh
      change abs (h-0)<δ at hh
      have hz : h-0=h := by grind
      rw [hz] at hh
      exact hfδ h hh
    · apply Classical.byContradiction
      intro hn
      have hp := abs_pos (f 0-a) (by grind)
      obtain ⟨δ,hδ,hfδ⟩ := hf (abs (f 0-a)) hp
      have := hfδ 0 (by simpa [abs_zero] using hδ)
      grind (ematch := 0)
  · rintro ⟨hf,hzero⟩ ε hε
    obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
    refine ⟨δ,hδ,?_⟩
    intro h hh
    by_cases hz : h=0
    · subst h; simpa [hzero,Scalar.sub_self,abs_zero] using hε
    · apply hfδ h trivial
      · change 0<abs (h-0)
        apply abs_pos
        grind
      · change abs (h-0)<δ
        have heq : h-0=h := by grind
        simpa only [heq] using hh

-- Constant-function case of Rudin Definition 4.5, expressed using
-- LimitAtZero; no separate theorem.
theorem limit_const (a : R) : LimitAtZero (fun _ => a) a :=
  (limitAtZero_iff _ _).mpr ⟨hasLimit_const realMetric (fun _ => True) 0 a,rfl⟩

-- Identity-function case of Rudin Examples 4.11, expressed using
-- LimitAtZero.
theorem limit_id : LimitAtZero (fun h : R => h) 0 := by
  intro ε hε
  refine ⟨ε,hε,?_⟩
  intro h hh
  have heq : h-0=h := by grind
  simpa only [heq] using hh

-- Rudin Theorem 4.9, sum clause, expressed using LimitAtZero (which
-- includes the value at zero).
theorem limit_add (f g : R → R) (a b : R)
    (hf : LimitAtZero f a) (hg : LimitAtZero g b) :
    LimitAtZero (fun h => f h+g h) (a+b) := by
  obtain ⟨hf,hf0⟩ := (limitAtZero_iff f a).mp hf
  obtain ⟨hg,hg0⟩ := (limitAtZero_iff g b).mp hg
  exact (limitAtZero_iff _ _).mpr
    ⟨hasLimit_add realMetric (fun _ => True) f g 0 a b hf hg,by rw [hf0,hg0]⟩

-- Rudin Theorem 4.9, product clause, expressed using LimitAtZero (which
-- includes the value at zero).
theorem limit_mul (f g : R → R) (a b : R)
    (hf : LimitAtZero f a) (hg : LimitAtZero g b) :
    LimitAtZero (fun h => f h*g h) (a*b) := by
  obtain ⟨hf,hf0⟩ := (limitAtZero_iff f a).mp hf
  obtain ⟨hg,hg0⟩ := (limitAtZero_iff g b).mp hg
  exact (limitAtZero_iff _ _).mpr
    ⟨hasLimit_mul realMetric (fun _ => True) f g 0 a b hf hg,by rw [hf0,hg0]⟩

-- Consequence of Rudin Theorem 4.9, expressed using LimitAtZero.
theorem limit_sub (f g : R → R) (a b : R)
    (hf : LimitAtZero f a) (hg : LimitAtZero g b) :
    LimitAtZero (fun h => f h-g h) (a-b) := by
  obtain ⟨hf,hf0⟩ := (limitAtZero_iff f a).mp hf
  obtain ⟨hg,hg0⟩ := (limitAtZero_iff g b).mp hg
  exact (limitAtZero_iff _ _).mpr
    ⟨hasLimit_sub realMetric (fun _ => True) f g 0 a b hf hg,by rw [hf0,hg0]⟩

-- Rudin Theorem 4.9, quotient clause, expressed using LimitAtZero.
theorem limit_div (f g : R → R) (a b : R) (hb : b≠0)
    (hf : LimitAtZero f a) (hg : LimitAtZero g b) :
    LimitAtZero (fun h => f h/g h) (a/b) := by
  obtain ⟨hf,hf0⟩ := (limitAtZero_iff f a).mp hf
  obtain ⟨hg,hg0⟩ := (limitAtZero_iff g b).mp hg
  exact (limitAtZero_iff _ _).mpr
    ⟨hasLimit_div realMetric (fun _ => True) f g 0 a b hf hg hb,by rw [hf0,hg0]⟩

-- Rudin Theorem 4.7 specialized to continuity at zero, expressed using
-- LimitAtZero.
theorem limit_comp (f g : R → R) (a : R)
    (hf : LimitAtZero f a) (hg : LimitAtZero g 0) :
    LimitAtZero (fun h => f (g h)) a := by
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
  obtain ⟨ρ,hρ,hgρ⟩ := hg δ hδ
  refine ⟨ρ,hρ,fun h hh => hfδ (g h) ?_⟩
  have ht := hgρ h hh
  have heq : g h-0=g h := by grind
  simpa only [heq] using ht

/-!
# Differentiation

## The Derivative of a Real Function

![Secant lines through nearby curve points approach a tangent.](site/diagrams/rudin-derivative.svg)

*As the second point approaches the amber point, the pale secant lines approach the amber tangent.*
-/

-- The slope between nearby points approaches the fixed value d.
def HasDerivative (f : R → R) (x d : R) : Prop :=
  HasLimit realMetric realMetric (fun _ => True) (fun t => (f t-f x)/(t-x)) x d

-- Equivalent form of Rudin Definition 5.1; the first-order remainder is
-- used in the proof of Theorem 5.5, (4)-(5).
theorem derivative_iff_remainder (f : R → R) (x d : R) :
    HasDerivative f x d ↔
      ∀ ε : R, 0<ε → ∃ δ : R, 0<δ ∧ ∀ h : R, 0<abs h → abs h<δ →
        abs (f (x+h)-f x-d*h)<ε*abs h := by
  constructor
  · intro hf ε hε
    obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
    refine ⟨δ,hδ,?_⟩
    intro h hp hh
    have heq : x+h-x=h := by grind
    have ht := hfδ (x+h) trivial (by change 0<abs (x+h-x); simpa only [heq] using hp)
      (by change abs (x+h-x)<δ; simpa only [heq] using hh)
    have hn : h≠0 := by intro hz; rw [hz,abs_zero] at hp; grind
    change abs ((f (x+h)-f x)/(x+h-x)-d)<ε at ht
    rw [heq] at ht
    have hid : (f (x+h)-f x)/h-d=(f (x+h)-f x-d*h)/h := by grind
    rw [hid,abs_div] at ht
    exact (Scalar.div_lt_iff hp).mp ht
  · intro hf ε hε
    obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
    refine ⟨δ,hδ,?_⟩
    intro t _ hp hh
    change 0<abs (t-x) at hp
    change abs (t-x)<δ at hh
    have ht := hfδ (t-x) hp hh
    have heq : x+(t-x)=t := by grind
    rw [heq] at ht
    have hn : t-x≠0 := by intro hz; rw [hz,abs_zero] at hp; grind
    change abs ((f t-f x)/(t-x)-d)<ε
    have hid : (f t-f x)/(t-x)-d=(f t-f x-d*(t-x))/(t-x) := by grind
    rw [hid,abs_div]
    exact (Scalar.div_lt_iff hp).mpr ht

def Secant (f : R → R) (x d h : R) : R := by
  classical
  exact if h=0 then d else (f (x+h)-f x)/h

-- Algebraic helper for the increment factorization in Rudin Theorem
-- 5.5, (4)-(5); the secant is filled in at zero.
theorem secant_increment (f : R → R) (x d h : R) :
    f (x+h)-f x=h*Secant f x d h := by
  unfold Secant
  split <;> grind [smaller]

-- Reparameterization of Rudin Definition 5.1 by t = x + h, with the
-- secant value at h = 0 filled in by d.
theorem derivative_iff_secant_limit (f : R → R) (x d : R) :
    HasDerivative f x d ↔ LimitAtZero (Secant f x d) d := by
  rw [derivative_iff_remainder]
  constructor
  · intro hf ε hε
    obtain ⟨δ, hδ, hf'⟩ := hf ε hε
    refine ⟨δ, hδ, ?_⟩
    intro h hh
    by_cases hz : h=0
    · subst h; rw [Secant, if_pos rfl, Scalar.sub_self, abs_zero]; exact hε
    · have hp : 0<abs h := by have := abs_nonneg h; have := abs_eq_zero h; grind [smaller]
      have hr := hf' h hp hh
      have heq : Secant f x d h-d=(f (x+h)-f x-d*h)/h := by
        unfold Secant; rw [if_neg hz]; grind [smaller]
      rw [heq, abs_div]
      exact (Scalar.div_lt_iff hp).mpr hr
  · intro hf ε hε
    obtain ⟨δ, hδ, hf'⟩ := hf ε hε
    refine ⟨δ, hδ, ?_⟩
    intro h hp hh
    have ht := Scalar.mul_lt_mul_of_pos_left (hf' h hh) hp
    have heq : f (x+h)-f x-d*h=h*(Secant f x d h-d) := by
      have := secant_increment f x d h
      grind [smaller]
    rw [heq, abs_mul]
    grind [smaller]

-- Helper derived from Rudin Definition 5.1: a convergent factorization
-- of the increment gives the derivative.
theorem derivative_of_slope (f s : R → R) (x d : R)
    (hs : LimitAtZero s d) (he : ∀ h, f (x+h)-f x=h*s h) :
    HasDerivative f x d := by
  apply (derivative_iff_remainder f x d).mpr
  intro ε hε
  obtain ⟨δ, hδ, hs'⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hp hh
  have heq : f (x+h)-f x-d*h=h*(s h-d) := by rw [he h]; grind [smaller]
  rw [heq, abs_mul]
  have := Scalar.mul_lt_mul_of_pos_left (hs' h hh) hp
  grind [smaller]

-- Local version of the increment-factorization helper for Rudin
-- Definition 5.1; no separate theorem.
theorem derivative_of_local_slope (f s : R → R) (x d ρ : R)
    (hρ : 0 < ρ) (hs : LimitAtZero s d)
    (he : ∀ h, abs h < ρ → f (x+h)-f x=h*s h) : HasDerivative f x d := by
  apply (derivative_iff_remainder f x d).mpr
  intro ε hε
  obtain ⟨δ, hδ, hs'⟩ := hs ε hε
  refine ⟨smaller δ ρ, by grind [smaller], ?_⟩
  intro h hp hh
  have hhρ : abs h < ρ := by grind [smaller]
  have heq : f (x+h)-f x-d*h=h*(s h-d) := by rw [he h hhρ]; grind [smaller]
  rw [heq, abs_mul]
  have := Scalar.mul_lt_mul_of_pos_left (hs' h (by grind [smaller])) hp
  grind [smaller]

-- Rudin Theorem 5.2: differentiability implies continuity; here for
-- functions on the whole real line.
theorem derivative_continuous (f : R → R) (x d : R) (hf : HasDerivative f x d) :
    ContinuousAt realMetric realMetric (fun _ => True) f x := by
  have hs := (derivative_iff_secant_limit f x d).mp hf
  have hv := limit_add (fun _ => f x) (fun h => h*Secant f x d h) (f x) (0*d)
    (limit_const _) (limit_mul _ _ _ _ limit_id hs)
  have hval : ∀ h, f x+h*Secant f x d h=f (x+h) := by
    intro h
    have := secant_increment f x d h
    grind
  have heq : f x+0*d=f x := by grind
  rw [heq] at hv
  simp only [hval] at hv
  intro ε hε
  obtain ⟨δ,hδ,hvδ⟩ := hv ε hε
  refine ⟨δ,hδ,?_⟩
  intro t _ ht
  change abs (t-x)<δ at ht
  have h := hvδ (t-x) ht
  have hid : x+(t-x)=t := by grind
  change abs (f t-f x)<ε
  simpa only [hid] using h

-- Reparameterization of Rudin Definition 4.5 by t = x + h; helper for
-- Theorem 5.5.
theorem continuous_increment_limit (f : R → R) (x : R)
    (hf : ContinuousAt realMetric realMetric (fun _ => True) f x) :
    LimitAtZero (fun h => f (x+h)) (f x) := by
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf ε hε
  refine ⟨δ,hδ,?_⟩
  intro h hh
  apply hfδ (x+h) trivial
  change abs (x+h-x)<δ
  have heq : x+h-x=h := by grind
  simpa only [heq] using hh

/-!
## The Arithmetic of Derivatives

![A rectangle grows by two thin strips and a small corner.](site/diagrams/rudin-product-rule.svg)

*The product changes by two thin strips; the corner is second-order.*
-/

-- Rudin Theorem 5.3(a): derivative of a sum, for functions on the real
-- line.
theorem derivative_add (f g : R → R) (x a b : R)
    (hf : HasDerivative f x a) (hg : HasDerivative g x b) :
    HasDerivative (fun t => f t+g t) x (a+b) := by
  apply derivative_of_slope _ (fun h => Secant f x a h+Secant g x b h)
  · exact limit_add _ _ _ _ ((derivative_iff_secant_limit f x a).mp hf)
      ((derivative_iff_secant_limit g x b).mp hg)
  · intro h
    have := secant_increment f x a h
    have := secant_increment g x b h
    grind

-- Rudin Theorem 5.3(b): product rule, for functions on the real line.
theorem derivative_mul (f g : R → R) (x a b : R)
    (hf : HasDerivative f x a) (hg : HasDerivative g x b) :
    HasDerivative (fun t => f t*g t) x (a*g x+f x*b) := by
  let sf := Secant f x a
  let sg := Secant g x b
  have hsf := (derivative_iff_secant_limit f x a).mp hf
  have hsg := (derivative_iff_secant_limit g x b).mp hg
  have hfval := continuous_increment_limit f x (derivative_continuous f x a hf)
  apply derivative_of_slope _ (fun h => f (x+h)*sg h+g x*sf h)
  · have ht := limit_add _ _ _ _ (limit_mul _ _ _ _ hfval hsg)
      (limit_mul _ _ _ _ (limit_const (g x)) hsf)
    have heq : f x*b+g x*a=a*g x+f x*b := by grind
    simpa only [heq] using ht
  · intro h
    have := secant_increment f x a h
    have := secant_increment g x b h
    dsimp [sf,sg]
    grind

-- Rudin Theorem 5.3(c): quotient rule with nonzero denominator at the
-- point.
theorem derivative_div (f g : R → R) (x a b : R)
    (hf : HasDerivative f x a) (hg : HasDerivative g x b) (hgx : g x≠0) :
    HasDerivative (fun t => f t/g t) x ((a*g x-f x*b)/(g x*g x)) := by
  let sf := Secant f x a
  let sg := Secant g x b
  have hsf := (derivative_iff_secant_limit f x a).mp hf
  have hsg := (derivative_iff_secant_limit g x b).mp hg
  have hgval := continuous_increment_limit g x (derivative_continuous g x b hg)
  have hnum := limit_sub _ _ _ _ (limit_mul _ _ _ _ (limit_const (g x)) hsf)
    (limit_mul _ _ _ _ (limit_const (f x)) hsg)
  have hden := limit_mul _ _ _ _ (limit_const (g x)) hgval
  have hlim := limit_div _ _ _ _ (show g x*g x≠0 from by grind) hnum hden
  have hp := abs_pos (g x) hgx
  obtain ⟨ρ,hρ,hnear⟩ := hgval (abs (g x)/2) (by grind)
  apply derivative_of_local_slope _
    (fun h => (g x*sf h-f x*sg h)/(g x*g (x+h))) _ _ ρ hρ
  · have heq : g x*a-f x*b=a*g x-f x*b := by grind
    simpa only [heq] using hlim
  · intro h hh
    have err := hnear h hh
    change abs (g (x+h)-g x)<abs (g x)/2 at err
    have hn : g (x+h)≠0 := by
      intro hz
      rw [hz] at err
      have heq : (0:R)-g x= -(g x) := by grind
      rw [heq,abs_neg] at err
      grind
    have := secant_increment f x a h
    have := secant_increment g x b h
    dsimp [sf,sg]
    grind

/-!
## Elementary Examples

![A line, parabola, and reciprocal curve with tangent segments.](site/diagrams/rudin-elementary-derivatives.svg)

*A line keeps the same slope; the parabola and reciprocal curve have changing slopes.*
-/

-- Helper from Rudin Definition 5.1 for the constant and linear cases in
-- Examples 5.4.
theorem derivative_of_exact_increment (f : R → R) (x d : R)
    (hf : ∀ h, f (x + h) - f x = d * h) : HasDerivative f x d := by
  apply (derivative_iff_remainder f x d).mpr
  intro ε hε
  refine ⟨1, by grind [smaller], ?_⟩
  intro h hp _
  rw [hf h]
  simpa [Scalar.sub_self, abs_zero] using Scalar.mul_pos hε hp

-- Rudin Examples 5.4: derivative of a constant.
theorem derivative_const (c x : R) : HasDerivative (fun _ => c) x 0 := by
  apply derivative_of_exact_increment
  intro h; grind [smaller]

-- Rudin Examples 5.4: derivative of the identity function.
theorem derivative_id (x : R) : HasDerivative (fun t => t) x 1 := by
  apply derivative_of_exact_increment
  intro h; grind [smaller]

-- Affine-polynomial case of Rudin Examples 5.4, using Theorem
-- 5.3(a),(b).
theorem derivative_affine (w b x : R) :
    HasDerivative (fun t => w * t + b) x w := by
  apply derivative_of_exact_increment
  intro h; grind [smaller]

-- Rudin Examples 5.4, integer-power rule with exponent 2.
theorem derivative_square (x : R) :
    HasDerivative (fun t => t*t) x (2*x) := by
  have h := derivative_mul (fun t => t) (fun t => t) x 1 1 (derivative_id x) (derivative_id x)
  have heq : 1*x+x*1=2*x := by grind
  simpa only [heq] using h

-- Rudin Examples 5.4, integer-power rule with exponent -1, away from
-- zero.
theorem derivative_reciprocal (x : R) (hx : x≠0) :
    HasDerivative (fun t => 1/t) x (-1/(x*x)) := by
  have h := derivative_div (fun _ => 1) (fun t => t) x 0 1 (derivative_const 1 x) (derivative_id x) hx
  have heq : 0*x-1*1= -1 := by grind
  simpa only [heq] using h

-- Rudin Theorem 5.3(c), with constant numerator 1.
theorem derivative_inv (f : R → R) (x a : R)
    (hf : HasDerivative f x a) (hx : f x≠0) :
    HasDerivative (fun t => 1/f t) x (-a/(f x*f x)) := by
  have h := derivative_div (fun _ => 1) f x 0 a (derivative_const 1 x) hf hx
  have heq : 0*f x-1*a= -a := by grind
  simpa only [heq] using h

/-!
## The Chain Rule

![A small displacement is rescaled by two successive maps.](site/diagrams/rudin-chain-rule.svg)

*A small displacement is stretched at each stage. The two local scale factors multiply.*
-/

-- Rudin Theorem 5.5: chain rule, following the increment factorization
-- in its proof.
theorem derivative_comp (f g : R → R) (x a b : R)
    (hf : HasDerivative f (g x) a) (hg : HasDerivative g x b) :
    HasDerivative (fun t => f (g t)) x (a*b) := by
  let sf := Secant f (g x) a
  let sg := Secant g x b
  have hsf : LimitAtZero sf a := (derivative_iff_secant_limit f (g x) a).mp hf
  have hsg : LimitAtZero sg b := (derivative_iff_secant_limit g x b).mp hg
  have hin : LimitAtZero (fun h => h*sg h) 0 := by
    have ht := limit_mul _ _ _ _ limit_id hsg
    have heq : (0:R)*b=0 := by grind [smaller]
    simpa only [heq] using ht
  apply derivative_of_slope _ (fun h => sf (h*sg h)*sg h)
  · exact limit_mul _ _ _ _ (limit_comp _ _ _ hsf hin) hsg
  · intro h
    have h₁ := secant_increment f (g x) a (h*sg h)
    have h₂ := secant_increment g x b h
    have heq : g (x+h)=g x+h*sg h := by dsimp [sg]; grind [smaller]
    rw [heq]
    dsimp [sf] at *
    grind [smaller]

/-!
# Some Special Functions

## Differentiation of the Exponential Series

![An exponential curve and tangent, beside the remainder and a quadratic upper bound.](site/diagrams/rudin-exponential-remainder.svg)

*The curve meets its tangent on the left. On the right, the blue error stays below an amber quadratic bound.*
-/

-- Rudin, real absolute-value formula after Definition 1.32, nonnegative
-- case.
theorem abs_of_nonneg (x : R) (hx : 0≤x) : abs x=x := by unfold abs; rw [if_pos hx]

-- Ordered-arithmetic helper for the exponential estimates; no separate
-- Rudin theorem is claimed.
theorem pow_le_pow (x y : R) (hx : 0≤x) (hxy : x≤y) (n : Nat) : x^n≤y^n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero]; grind
  | succ n ih =>
    have hy : 0≤y := by grind
    have h₁ := Scalar.mul_le_mul_of_nonneg_right ih hx
    have h₂ := Scalar.mul_le_mul_of_nonneg_left hxy (pow_nonneg y hy n)
    simp only [Lean.Grind.Semiring.pow_succ]
    grind

-- Additional finite-power remainder estimate; not Rudin's proof of
-- Theorem 8.1 or Theorem 8.6(b).
theorem power_taylor_bound (x h M : R) (hM : 0≤M)
    (hx : abs x≤M) (hxh : abs (x+h)≤M) (n : Nat) :
    abs ((x+h)^(n+2)-x^(n+2)-((n+2:Nat):R)*x^(n+1)*h) ≤
      (((n+2:Nat):R)*((n+1:Nat):R)/2)*M^n*(abs h*abs h) := by
  induction n with
  | zero =>
    have heq : (x+h)^(0+2)-x^(0+2)-((0+2:Nat):R)*x^(0+1)*h=h*h := by grind
    rw [heq,abs_mul]
    simp only [Lean.Grind.Semiring.pow_zero]
    grind
  | succ n ih =>
    let rem := (x+h)^(n+2)-x^(n+2)-((n+2:Nat):R)*x^(n+1)*h
    have heq : (x+h)^(n+1+2)-x^(n+1+2)-((n+1+2:Nat):R)*x^(n+1+1)*h =
        (x+h)*rem+((n+2:Nat):R)*x^(n+1)*(h*h) := by
      dsimp [rem]
      have hp₁ : (x+h)^(n+1+2)=(x+h)^(n+2)*(x+h) := by
        have he : n+1+2=(n+2)+1 := by omega
        rw [he,Lean.Grind.Semiring.pow_succ]
      have hp₂ : x^(n+1+2)=x^(n+2)*x := by
        have he : n+1+2=(n+2)+1 := by omega
        rw [he,Lean.Grind.Semiring.pow_succ]
      have hp₃ : x^(n+2)=x^(n+1)*x := by
        rw [Lean.Grind.Semiring.pow_succ]
      rw [hp₁,hp₂]
      grind
    rw [heq]
    have ht := abs_triangle ((x+h)*rem) (((n+2:Nat):R)*x^(n+1)*(h*h))
    rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_pow] at ht
    have hn : (0:R)≤((n+2:Nat):R) := Lean.Grind.OrderedRing.natCast_nonneg
    rw [abs_of_nonneg _ hn] at ht
    have h₁ := Scalar.mul_le_mul_of_nonneg_right hxh (abs_nonneg rem)
    have h₂ := Scalar.mul_le_mul_of_nonneg_left ih hM
    have hpow := pow_le_pow (abs x) M (abs_nonneg x) hx (n+1)
    have h₃ := Scalar.mul_le_mul_of_nonneg_left hpow hn
    have hah : 0≤abs h*abs h := Scalar.mul_nonneg (abs_nonneg h) (abs_nonneg h)
    have h₄ := Scalar.mul_le_mul_of_nonneg_right h₃ hah
    have hpowM := Lean.Grind.Semiring.pow_succ M n
    change abs rem≤_ at ih
    have hb := Std.le_trans ht
      (Lean.Grind.OrderedAdd.add_le_add (Std.le_trans h₁ h₂) h₄)
    have hc : M * (((n+2:Nat):R)*((n+1:Nat):R)/2*M^n*(abs h*abs h)) +
        ((n+2:Nat):R)*M^(n+1)*(abs h*abs h) =
        (((n+1+2:Nat):R)*((n+1+1:Nat):R)/2)*M^(n+1)*(abs h*abs h) := by
      clear ih heq ht hn h₁ h₂ hpow h₃ hah h₄ hb rem
      rw [hpowM]
      grind
    rw [hc] at hb
    exact hb

-- Additional finite-sum remainder estimate for the exponential; no
-- direct numbered Rudin counterpart.
theorem expPartial_taylor_bound (x h M : R) (hM : 0≤M)
    (hx : abs x≤M) (hxh : abs (x+h)≤M) (n : Nat) :
    abs (expPartial (x+h) (n+2)-expPartial x (n+2)-h*expPartial x (n+1)) ≤
      (abs h*abs h/2)*expPartial M n := by
  induction n with
  | zero =>
    have heq : expPartial (x+h) 2-expPartial x 2-h*expPartial x 1=0 := by
      simp only [expPartial,partialSum,reciprocalFactorial,Lean.Grind.Semiring.pow_succ,
        Lean.Grind.Semiring.pow_zero]
      grind
    change abs (expPartial (x+h) 2-expPartial x 2-h*expPartial x 1)≤_
    rw [heq,abs_zero]
    simp only [expPartial,partialSum]
    grind
  | succ n ih =>
    let rem := expPartial (x+h) (n+2)-expPartial x (n+2)-h*expPartial x (n+1)
    let powrem := (x+h)^(n+2)-x^(n+2)-((n+2:Nat):R)*x^(n+1)*h
    have hstep := reciprocalFactorial_step (R:=R) (n+1)
    have hstep' := reciprocalFactorial_step (R:=R) n
    have heq : expPartial (x+h) (n+1+2)-expPartial x (n+1+2)-h*expPartial x (n+1+1) =
        rem+reciprocalFactorial (n+2)*powrem := by
      dsimp [rem,powrem,expPartial]
      have he : n+1+2=(n+2)+1 := by omega
      rw [he]
      simp only [partialSum]
      grind
    rw [heq]
    have ht := abs_triangle rem (reciprocalFactorial (n+2)*powrem)
    rw [abs_mul,abs_of_nonneg _ (Scalar.le_of_lt (reciprocalFactorial_pos (R:=R) (n+2)))] at ht
    have hp := power_taylor_bound x h M hM hx hxh n
    have hm := Scalar.mul_le_mul_of_nonneg_left hp
      (Scalar.le_of_lt (reciprocalFactorial_pos (R:=R) (n+2)))
    change abs rem≤_ at ih
    change abs powrem≤_ at hp
    change reciprocalFactorial (n+2)*abs powrem≤_ at hm
    change _≤(abs h*abs h/2)*(partialSum (fun k => M^k*reciprocalFactorial k) (n+1))
    rw [partialSum]
    change _≤(abs h*abs h/2)*(expPartial M n+M^n*reciprocalFactorial n)
    have hc : reciprocalFactorial (n+2)*(((n+2:Nat):R)*((n+1:Nat):R)/2*M^n*(abs h*abs h)) =
        (abs h*abs h/2)*(M^n*reciprocalFactorial n) := by
      clear ih heq ht hp hm rem powrem
      grind
    rw [hc] at hm
    have hb := Std.le_trans ht (Lean.Grind.OrderedAdd.add_le_add ih hm)
    have he : (abs h*abs h/2)*expPartial M n+(abs h*abs h/2)*(M^n*reciprocalFactorial n) =
        (abs h*abs h/2)*(expPartial M n+M^n*reciprocalFactorial n) := by
      exact (Lean.Grind.Semiring.left_distrib _ _ _).symm
    rw [he] at hb
    exact hb

-- Rudin Theorem 3.3(b), real case with scalar -1.
theorem seq_neg (s : Nat → R) (a : R) (hs : ConvergesTo realMetric s a) :
    ConvergesTo realMetric (fun n => -s n) (-a) := by
  intro ε hε
  obtain ⟨N,hN⟩ := hs ε hε
  refine ⟨N,?_⟩
  intro n hn
  change abs (-s n - -a)<ε
  have heq : -s n - -a=-(s n-a) := by grind
  rw [heq,abs_neg]
  exact hN n hn

-- Consequence of Rudin Theorem 3.3(a),(b), real case: subtraction of
-- sequence limits.
theorem seq_sub (s t : Nat → R) (a b : R)
    (hs : ConvergesTo realMetric s a) (ht : ConvergesTo realMetric t b) :
    ConvergesTo realMetric (fun n => s n-t n) (a-b) := by
  simpa only [Lean.Grind.Ring.sub_eq_add_neg] using
    seq_add s (fun n => -t n) a (-b) hs (seq_neg t b ht)

-- Consequence of the real absolute-value formula after Rudin Definition
-- 1.32; no separate numbered theorem.
theorem abs_le (x ε : R) : abs x≤ε ↔ -ε≤x ∧ x≤ε := by
  unfold abs; split <;> grind

-- Rudin Examples 4.11, inequality (11), real case: reverse triangle
-- inequality.
theorem abs_sub_abs_le (a b : R) : abs (abs a-abs b)≤abs (a-b) := by
  have h₁ := abs_bound_of_error a b
  have h₂ := abs_bound_of_error b a
  have heq : b-a=-(a-b) := by grind
  rw [heq,abs_neg] at h₂
  rw [abs_le]
  grind

-- Consequence of Rudin Examples 4.11, inequality (11): absolute value
-- preserves sequential limits.
theorem seq_abs (s : Nat → R) (a : R) (hs : ConvergesTo realMetric s a) :
    ConvergesTo realMetric (fun n => abs (s n)) (abs a) := by
  intro ε hε
  obtain ⟨N,hN⟩ := hs ε hε
  refine ⟨N,?_⟩
  intro n hn
  have ht := abs_sub_abs_le (s n) a
  have hh := hN n hn
  change abs (s n-a)<ε at hh
  change abs (abs (s n)-abs a)<ε
  grind

-- Additional quadratic remainder estimate for the exponential series;
-- this proof does not follow Rudin's argument for Theorem 8.6(b).
theorem expSeries_remainder_bound (x : R) : ∃ B : R, 0≤B ∧
    ∀ h, abs h<1 → abs (expSeries (x+h)-expSeries x-h*expSeries x)≤B/2*(abs h*abs h) := by
  let M := abs x+1
  have hx := abs_nonneg x
  have hM : 0≤M := by dsimp [M]; grind
  obtain ⟨B,hB⟩ := exp_terms_bounded M hM
  have hBp : 0≤B := by
    have h := hB 0
    change (0:R)≤B at h
    exact h
  refine ⟨B,hBp,?_⟩
  intro h hh
  have hMx : abs x≤M := by dsimp [M]; grind
  have hMh : abs (x+h)≤M := by
    have := abs_triangle x h
    dsimp [M]; grind
  let errors := fun n => expPartial (x+h) (n+2)-expPartial x (n+2)-h*expPartial x (n+1)
  have hlim : ConvergesTo realMetric errors (expSeries (x+h)-expSeries x-h*expSeries x) := by
    exact seq_sub _ _ _ _
      (seq_sub _ _ _ _
        (seq_succ _ _ (seq_succ _ _ (expSeries_limit (x+h))))
        (seq_succ _ _ (seq_succ _ _ (expSeries_limit x))))
      (seq_mul _ _ _ _ (seq_const h) (seq_succ _ _ (expSeries_limit x)))
  apply seq_le _ _ _ (seq_abs errors _ hlim)
  intro n
  have ht := expPartial_taylor_bound x h M hM hMx hMh n
  have hp := Scalar.mul_nonneg (abs_nonneg h) (abs_nonneg h)
  have hm := Scalar.mul_le_mul_of_nonneg_left (hB n)
    (show 0≤abs h*abs h/2 from by grind)
  change abs (errors n)≤_ at ht
  grind

-- Rudin Theorem 8.6(b), with existence from (a), for the series-defined
-- exponential. The current remainder-estimate proof differs from
-- Rudin's proof, Chapter 8, (28).
theorem derivative_expSeries (x : R) : HasDerivative expSeries x (expSeries x) := by
  apply (derivative_iff_remainder _ _ _).mpr
  obtain ⟨B,hB,hbound⟩ := expSeries_remainder_bound x
  intro ε hε
  have hBp : 0<B+1 := by grind
  have hδ : 0<ε/(B+1) := by
    rw [Scalar.div_def]
    exact Scalar.mul_pos hε (Scalar.inv_pos.mpr hBp)
  refine ⟨smaller 1 (ε/(B+1)),by grind [smaller],?_⟩
  intro h hp hh
  have ht := hbound h (by grind [smaller])
  have hmul := Scalar.mul_lt_mul_of_pos_right
    (show abs h<ε/(B+1) from by grind [smaller]) hBp
  have hc := Scalar.div_mul_cancel (a:=ε) (b:=B+1) (by grind)
  have hb := Scalar.mul_le_mul_of_nonneg_right (show B/2≤B+1 from by grind)
    (Scalar.le_of_lt hp)
  have hi : B/2*abs h<ε := by grind
  have hf := Scalar.mul_lt_mul_of_pos_right hi hp
  have heq : expSeries (x+h)-expSeries x-expSeries x*h =
      expSeries (x+h)-expSeries x-h*expSeries x := by grind
  rw [heq]
  grind

-- Rudin Chapter 8, (25) and (27), p. 178: E(0) = 1.
theorem expSeries_zero : expSeries (0 : R)=1 := by
  have hp : ∀ n : Nat, expPartial (0:R) (n+1)=1 := by
    intro n
    induction n with
    | zero =>
      simp only [expPartial,partialSum,reciprocalFactorial,Lean.Grind.Semiring.pow_zero]
      grind
    | succ n ih =>
      have hz : (0:R)^(n+1)=0 := by rw [Lean.Grind.Semiring.pow_succ]; grind
      change expPartial 0 (n+1)+(0:R)^(n+1)*reciprocalFactorial (n+1)=1
      rw [hz,ih]
      grind
  have heq : (fun n => expPartial (0:R) (n+1))=(fun _ => (1:R)) := funext hp
  have hlim := seq_succ _ _ (expSeries_limit (0:R))
  rw [heq] at hlim
  exact limit_unique _ _ _ _ hlim (seq_const 1)

/-!
## A Positive Exponential
-/

def exp (x : R) : R := by
  classical
  exact if 0≤x then expSeries x else 1/expSeries (-x)

-- Positivity clause of Rudin Theorem 8.6(c), here for the separately
-- defined piecewise exp; Rudin uses the single series E and identity
-- (27).
theorem exp_pos (x : R) : 0<exp x := by
  unfold exp
  split
  · rename_i hx
    have := expSeries_ge_one x hx
    grind
  · rename_i hx
    have hn : 0≤-x := by grind
    have hp := expSeries_ge_one (-x) hn
    rw [Scalar.div_def,Scalar.one_mul,Scalar.inv_pos]
    grind

-- Rudin Chapter 8, E(0) = 1 in (27); here specialized to the article's
-- piecewise exp definition.
theorem exp_zero : exp (0:R)=1 := by
  rw [exp,if_pos (by grind),expSeries_zero]

-- Locality helper from Rudin Definition 5.1: locally equal functions
-- have the same derivative; no separate theorem.
theorem derivative_local_congr (f g : R → R) (x d ρ : R)
    (hρ : 0<ρ) (hbase : f x=g x) (hsame : ∀ h, abs h<ρ → f (x+h)=g (x+h))
    (hg : HasDerivative g x d) : HasDerivative f x d := by
  rw [derivative_iff_remainder] at hg ⊢
  intro ε hε
  obtain ⟨δ,hδ,hg'⟩ := hg ε hε
  refine ⟨smaller δ ρ,by grind [smaller],?_⟩
  intro h hp hh
  rw [hbase,hsame h (by grind [smaller])]
  exact hg' h hp (by grind [smaller])

-- Additional gluing lemma from Rudin Definition 5.1: branches with the
-- same value and derivative at the point; no direct numbered
-- counterpart.
theorem derivative_piecewise (f g : R → R) (p : R → Prop) (x d : R)
    (hbase : f x=g x) (hf : HasDerivative f x d) (hg : HasDerivative g x d) :
    HasDerivative (fun t => @ite _ (p t) (Classical.propDecidable _) (f t) (g t)) x d := by
  rw [derivative_iff_remainder] at hf hg ⊢
  intro ε hε
  obtain ⟨δf,hδf,hf'⟩ := hf ε hε
  obtain ⟨δg,hδg,hg'⟩ := hg ε hε
  refine ⟨smaller δf δg,by grind [smaller],?_⟩
  intro h hp hh
  have hb : (@ite R (p x) (Classical.propDecidable _) (f x) (g x))=f x := by split <;> grind
  rw [hb]
  split
  · exact hf' h hp (by grind [smaller])
  · rw [hbase]
    exact hg' h hp (by grind [smaller])

-- Rudin Examples 5.4, linear polynomial with slope -1.
theorem derivative_negative (x : R) : HasDerivative (fun t => -t) x (-1) := by
  apply derivative_of_exact_increment
  intro h; grind

-- Application of Rudin Theorems 5.3(c), 5.5, and 8.6(b) to 1/E(-x); not
-- a separate theorem in the book.
theorem derivative_reciprocal_expSeries (x : R) (hx : expSeries (-x)≠0) :
    HasDerivative (fun t => 1/expSeries (-t)) x (1/expSeries (-x)) := by
  have hin := derivative_comp expSeries (fun t => -t) x (expSeries (-x)) (-1)
    (derivative_expSeries (-x)) (derivative_negative x)
  have hi := derivative_inv (fun t => expSeries (-t)) x (expSeries (-x)*(-1)) hin hx
  have heq : -(expSeries (-x)*(-1))/(expSeries (-x)*expSeries (-x))=1/expSeries (-x) := by grind
  simpa only [heq] using hi

-- Analogue of Rudin Theorem 8.6(a),(b) for this piecewise exp. This
-- proof does not identify it with the all-real series E or follow
-- Rudin's construction.
theorem derivative_exp (x : R) : HasDerivative exp x (exp x) := by
  by_cases hz : x=0
  · subst x
    have h₁ := derivative_expSeries (0:R)
    rw [expSeries_zero] at h₁
    have hn : -(0:R)=0 := by grind
    have hi := derivative_reciprocal_expSeries (0:R) (by rw [hn,expSeries_zero]; grind)
    have hv : 1/expSeries (-(0:R))=1 := by rw [hn,expSeries_zero]; grind
    rw [hv] at hi
    rw [exp_zero]
    exact derivative_piecewise expSeries (fun t => 1/expSeries (-t)) (fun t => 0≤t) 0 1
      (by rw [hn,expSeries_zero]; grind) h₁ hi
  · by_cases hx : 0≤x
    · have hp : 0<x := by grind
      have hbase : exp x=expSeries x := by rw [exp,if_pos hx]
      rw [hbase]
      apply derivative_local_congr exp expSeries x (expSeries x) x hp hbase
      · intro h hh
        have hh' := (abs_lt _ _).mp hh
        rw [exp,if_pos (by grind)]
      · exact derivative_expSeries x
    · have hp : 0< -x := by grind
      have hbase : exp x=1/expSeries (-x) := by rw [exp,if_neg hx]
      have hnonzero : expSeries (-x)≠0 := by
        have := expSeries_ge_one (-x) (by grind)
        grind
      rw [hbase]
      apply derivative_local_congr exp (fun t => 1/expSeries (-t)) x (1/expSeries (-x)) (-x) hp hbase
      · intro h hh
        have hh' := (abs_lt _ _).mp hh
        rw [exp,if_neg (by grind)]
      · exact derivative_reciprocal_expSeries x hnonzero

/-!
## Sigmoid and Two-Class Softmax

![A sigmoid curve with its bell-shaped derivative.](site/diagrams/rudin-sigmoid-slope.svg)

*The blue sigmoid flattens at both ends; its amber derivative peaks in the middle.*
-/

-- Application of Rudin Theorems 5.3 and 5.5 to the exponential
-- derivative, Theorem 8.6(b); sigmoid is an addition to this article.
theorem derivative_sigmoid (x : R) :
    HasDerivative (fun t => 1/(1+exp (-t))) x
      ((1/(1+exp (-x)))*(1-1/(1+exp (-x)))) := by
  have he := derivative_comp exp (fun t => -t) x (exp (-x)) (-1)
    (derivative_exp (-x)) (derivative_negative x)
  have hs := derivative_add (fun _ => (1:R)) (fun t => exp (-t)) x 0 (exp (-x)*(-1))
    (derivative_const 1 x) he
  have hp := exp_pos (-x)
  have hn : 1+exp (-x)≠0 := by grind
  have hd := derivative_inv (fun t => 1+exp (-t)) x (0+exp (-x)*(-1)) hs hn
  have hid : -(0+exp (-x)*(-1))/((1+exp (-x))*(1+exp (-x)))=
      (1/(1+exp (-x)))*(1-1/(1+exp (-x))) := by grind
  simpa only [hid] using hd

-- Application of Rudin Theorems 5.3(c) and 5.5 with Theorem 8.6(b);
-- two-class softmax is an addition to this article.
theorem derivative_softmax_pair (f g : R → R) (x df dg : R)
    (hf : HasDerivative f x df) (hg : HasDerivative g x dg) :
    let p := exp (f x)/(exp (f x)+exp (g x))
    HasDerivative (fun t => exp (f t)/(exp (f t)+exp (g t))) x (p*(1-p)*(df-dg)) := by
  dsimp only
  have hfe := derivative_comp exp f x (exp (f x)) df (derivative_exp (f x)) hf
  have hge := derivative_comp exp g x (exp (g x)) dg (derivative_exp (g x)) hg
  have hp := exp_pos (f x)
  have hq := exp_pos (g x)
  have hn : exp (f x)+exp (g x)≠0 := by grind
  have hi := derivative_inv (fun t => exp (f t)+exp (g t)) x _
    (derivative_add _ _ _ _ _ hfe hge) hn
  have hm := derivative_mul (fun t => exp (f t)) (fun t => 1/(exp (f t)+exp (g t))) x _ _ hfe hi
  have heq : (fun t => exp (f t)*(1/(exp (f t)+exp (g t))))=
      (fun t => exp (f t)/(exp (f t)+exp (g t))) := by funext t; grind
  rw [heq] at hm
  have hc : exp (f x)*df*(1/(exp (f x)+exp (g x)))+
      exp (f x)*(-(exp (f x)*df+exp (g x)*dg)/((exp (f x)+exp (g x))*(exp (f x)+exp (g x))))=
      (exp (f x)/(exp (f x)+exp (g x)))*(1-exp (f x)/(exp (f x)+exp (g x)))*(df-dg) := by grind
  simpa only [hc] using hm
/-!
# Backpropagation

## Scalar Expressions
-/

inductive Expr (R : Type) where
  | const : R → Expr R
  | param : Nat → Expr R
  | add : Expr R → Expr R → Expr R
  | mul : Expr R → Expr R → Expr R
  | inv : Expr R → Expr R
  | exp : Expr R → Expr R

namespace Expr

def eval (exponential : R → R) (θ : Nat → R) : Expr R → R
  | .const c => c
  | .param i => θ i
  | .add a b => eval exponential θ a + eval exponential θ b
  | .mul a b => eval exponential θ a * eval exponential θ b
  | .inv a => 1 / eval exponential θ a
  | .exp a => exponential (eval exponential θ a)

def Regular (exponential : R → R) (θ : Nat → R) : Expr R → Prop
  | .const _ | .param _ => True
  | .add a b | .mul a b => Regular exponential θ a ∧ Regular exponential θ b
  | .inv a => Regular exponential θ a ∧ eval exponential θ a ≠ 0
  | .exp a => Regular exponential θ a

/-!
## Forward Differentiation

![An input perturbation travels forward through a branching computation.](site/diagrams/rudin-forward-tangent.svg)

*An input perturbation travels forward. Each operation combines the changes arriving from its inputs.*
-/

def tangent (exponential : R → R) (θ seed : Nat → R) : Expr R → R
  | .const _ => 0
  | .param i => seed i
  | .add a b => tangent exponential θ seed a + tangent exponential θ seed b
  | .mul a b =>
      tangent exponential θ seed a * eval exponential θ b +
      eval exponential θ a * tangent exponential θ seed b
  | .inv a =>
      -(tangent exponential θ seed a) / (eval exponential θ a * eval exponential θ a)
  | .exp a => exponential (eval exponential θ a) * tangent exponential θ seed a

/-!
## Reverse Accumulation
-/

def backward (exponential : R → R) (θ : Nat → R) : Expr R → R → Nat → R
  | .const _, _ => fun _ => 0
  | .param j, bar => fun i => if i = j then bar else 0
  | .add a b, bar => fun i =>
      backward exponential θ a bar i + backward exponential θ b bar i
  | .mul a b, bar => fun i =>
      backward exponential θ a (bar * eval exponential θ b) i +
      backward exponential θ b (bar * eval exponential θ a) i
  | .inv a, bar =>
      backward exponential θ a (-bar / (eval exponential θ a * eval exponential θ a))
  | .exp a, bar =>
      backward exponential θ a (bar * exponential (eval exponential θ a))

-- Additional backpropagation algorithm identity; no corresponding Rudin
-- theorem.
theorem backward_eq_tangent (exponential : R → R) (θ : Nat → R)
    (expression : Expr R) (bar : R) (i : Nat) :
    backward exponential θ expression bar i =
      bar * tangent exponential θ (fun j => if i = j then 1 else 0) expression := by
  induction expression generalizing bar with
  | const c => simp [backward, tangent]; grind [smaller]
  | param j => simp only [backward, tangent]; split <;> grind [smaller]
  | add a b ha hb => simp only [backward, tangent, ha, hb]; grind [smaller]
  | mul a b ha hb => simp only [backward, tangent, ha, hb]; grind [smaller]
  | inv a ha => simp only [backward, tangent, ha]; grind [smaller]
  | exp a ha => simp only [backward, tangent, ha]; grind [smaller]

-- Additional example of accumulation for a shared parameter; no
-- corresponding Rudin theorem.
theorem shared_parameter (exponential : R → R) (θ : Nat → R) (i : Nat) :
    backward exponential θ (.mul (.param i) (.param i)) 1 i = θ i + θ i := by
  simp [backward, eval]
  grind [smaller]

def neg (a : Expr R) : Expr R := .mul (.const (-1)) a

def sum : List (Expr R) → Expr R
  | [] => .const 0
  | a :: rest => .add a (sum rest)

/-!
## Softmax

![Three scores become positive exponential weights and then normalized shares.](site/diagrams/rudin-softmax-normalization.svg)

*Scores become positive weights, then shares that sum to one.*
-/

def softmax (first : Expr R) (rest : List (Expr R)) : Expr R :=
  let weight := Expr.exp first
  .mul weight (.inv (.add weight (sum (rest.map Expr.exp))))

/-!
## A Multilayer Perceptron
-/

def sigmoid (a : Expr R) : Expr R :=
  .inv (.add (.const 1) (.exp (neg a)))

def affine (w x b : Expr R) : Expr R := .add (.mul w x) b

structure Parameters where
  w₀ : Expr R
  b₀ : Expr R
  w₁ : Expr R
  b₁ : Expr R
  v₀₀ : Expr R
  v₀₁ : Expr R
  c₀ : Expr R
  v₁₀ : Expr R
  v₁₁ : Expr R
  c₁ : Expr R

def parameterLeaves : Parameters (R := R) :=
  ⟨.param 0, .param 1, .param 2, .param 3, .param 4,
    .param 5, .param 6, .param 7, .param 8, .param 9⟩

def mlp (p : Parameters (R := R)) (x : Expr R) : Expr R :=
  let h₀ := sigmoid (affine p.w₀ x p.b₀)
  let h₁ := sigmoid (affine p.w₁ x p.b₁)
  let z₀ := .add (.add (.mul p.v₀₀ h₀) (.mul p.v₀₁ h₁)) p.c₀
  let z₁ := .add (.add (.mul p.v₁₀ h₀) (.mul p.v₁₁ h₁)) p.c₁
  softmax z₀ [z₁]

def squaredLoss (prediction : Expr R) (target : R) : Expr R :=
  let error := .add prediction (.const (-target))
  .mul (.const (1 / 2)) (.mul error error)

def trainingLoss (x y : R) : Expr R :=
  squaredLoss (mlp parameterLeaves (.const x)) y

/-!
## Backpropagation Gives the Derivative
-/

def perturb (θ seed : Nat → R) (t : R) : Nat → R := fun i => θ i+seed i*t

-- Implementation identity for scalar parameter perturbations; no
-- corresponding Rudin theorem.
theorem perturb_zero (θ seed : Nat → R) : perturb θ seed 0=θ := by
  funext i; dsimp [perturb]; grind

-- Structural application of Rudin Theorems 5.3, 5.5, and 8.6(b) to the
-- expression language; not a theorem stated by Rudin.
theorem eval_derivative (θ seed : Nat → R) (expression : Expr R) :
    Regular Speedrun.exp θ expression →
    HasDerivative (fun t => eval Speedrun.exp (perturb θ seed t) expression) 0
      (tangent Speedrun.exp θ seed expression) := by
  induction expression with
  | const c => intro _; exact derivative_const c 0
  | param i =>
    intro _
    apply derivative_of_exact_increment
    intro h; dsimp [eval,perturb,tangent]; grind
  | add a b ha hb =>
    intro ⟨hra,hrb⟩
    exact derivative_add _ _ _ _ _ (ha hra) (hb hrb)
  | mul a b ha hb =>
    intro ⟨hra,hrb⟩
    have h := derivative_mul _ _ _ _ _ (ha hra) (hb hrb)
    simpa only [perturb_zero,eval,tangent] using h
  | inv a ha =>
    intro ⟨hra,hne⟩
    have h := derivative_inv _ _ _ (ha hra) (by simpa only [perturb_zero] using hne)
    simpa only [perturb_zero,eval,tangent] using h
  | exp a ha =>
    intro hra
    have h := derivative_comp Speedrun.exp
      (fun t => eval Speedrun.exp (perturb θ seed t) a) 0
      (Speedrun.exp (eval Speedrun.exp θ a))
      (tangent Speedrun.exp θ seed a)
      (by simpa only [perturb_zero] using derivative_exp (eval Speedrun.exp θ a)) (ha hra)
    simpa only [eval,tangent] using h

-- Implementation helper for expression-domain conditions; no
-- corresponding Rudin theorem.
theorem regular_sum (θ : Nat → R) (xs : List (Expr R))
    (hx : ∀ a, a∈xs → Regular Speedrun.exp θ a) :
    Regular Speedrun.exp θ (sum xs) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    exact ⟨hx a (by simp),ih (fun b hb => hx b (by simp [hb]))⟩

-- Finite-sum consequence of exponential positivity, Rudin Theorem
-- 8.6(c); formulated for this article's expression evaluator.
theorem sum_exp_nonneg (θ : Nat → R) (xs : List (Expr R)) :
    0≤eval Speedrun.exp θ (sum (xs.map Expr.exp)) := by
  induction xs with
  | nil => change (0:R)≤0; grind
  | cons a xs ih =>
    have hp := exp_pos (eval Speedrun.exp θ a)
    change 0≤Speedrun.exp (eval Speedrun.exp θ a)+
      eval Speedrun.exp θ (sum (xs.map Expr.exp))
    grind

-- Additional softmax denominator check using the positivity property in
-- Rudin Theorem 8.6(c); no direct Rudin counterpart.
theorem regular_softmax (θ : Nat → R) (first : Expr R) (rest : List (Expr R))
    (hf : Regular Speedrun.exp θ first)
    (hr : ∀ a, a∈rest → Regular Speedrun.exp θ a) :
    Regular Speedrun.exp θ (softmax first rest) := by
  have hsum : Regular Speedrun.exp θ (sum (rest.map Expr.exp)) := by
    apply regular_sum
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hr b hb
  have hne : Speedrun.exp (eval Speedrun.exp θ first)+
      eval Speedrun.exp θ (sum (rest.map Expr.exp))≠0 := by
    have := exp_pos (eval Speedrun.exp θ first)
    have := sum_exp_nonneg θ rest
    grind
  exact ⟨hf,⟨⟨hf,hsum⟩,hne⟩⟩

-- Additional sigmoid denominator check using exponential positivity; no
-- direct Rudin counterpart.
theorem regular_sigmoid (θ : Nat → R) (a : Expr R)
    (ha : Regular Speedrun.exp θ a) : Regular Speedrun.exp θ (sigmoid a) := by
  have hp := exp_pos (-1*eval Speedrun.exp θ a)
  exact ⟨⟨trivial,⟨trivial,ha⟩⟩,by change 1+Speedrun.exp (-1*eval Speedrun.exp θ a)≠0; grind⟩

-- Implementation helper for the squared-loss expression; no
-- corresponding Rudin theorem.
theorem regular_squaredLoss (θ : Nat → R) (p : Expr R) (y : R)
    (hp : Regular Speedrun.exp θ p) : Regular Speedrun.exp θ (squaredLoss p y) :=
  ⟨trivial,⟨⟨hp,trivial⟩,⟨hp,trivial⟩⟩⟩

-- Additional domain check for the MLP training loss; no corresponding
-- Rudin theorem.
theorem trainingLoss_regular (θ : Nat → R) (x y : R) :
    Regular Speedrun.exp θ (trainingLoss x y) := by
  apply regular_squaredLoss
  have h₀ := regular_sigmoid θ (affine (.param 0) (.const x) (.param 1))
    (show Regular Speedrun.exp θ (affine (.param 0) (.const x) (.param 1)) from ⟨⟨trivial,trivial⟩,trivial⟩)
  have h₁ := regular_sigmoid θ (affine (.param 2) (.const x) (.param 3))
    (show Regular Speedrun.exp θ (affine (.param 2) (.const x) (.param 3)) from ⟨⟨trivial,trivial⟩,trivial⟩)
  apply regular_softmax
  · exact ⟨⟨⟨trivial,h₀⟩,⟨trivial,h₁⟩⟩,trivial⟩
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact ⟨⟨⟨trivial,h₀⟩,⟨trivial,h₁⟩⟩,trivial⟩

/-!
![Blue arrows carry values forward; amber arrows carry sensitivities backward through branching paths.](site/diagrams/rudin-backprop-derivative.svg)

*Blue carries values forward; amber carries sensitivities backward. Contributions add where paths meet.*
-/

-- Additional correctness theorem for backpropagation, built from
-- Rudin's scalar differentiation rules (5.3 and 5.5).
theorem backward_is_derivative (θ : Nat → R) (expression : Expr R) (i : Nat)
    (hr : Regular Speedrun.exp θ expression) :
    HasDerivative
      (fun t => eval Speedrun.exp (perturb θ (fun j => if i=j then 1 else 0) t) expression) 0
      (backward Speedrun.exp θ expression 1 i) := by
  have he := backward_eq_tangent Speedrun.exp θ expression 1 i
  have heq : backward Speedrun.exp θ expression 1 i=
      tangent Speedrun.exp θ (fun j => if i=j then 1 else 0) expression := by grind
  rw [heq]
  exact eval_derivative θ _ expression hr

/-!
![A small neural network with one amber weight, beside a loss curve and its amber tangent.](site/diagrams/rudin-mlp-gradient.svg)

*Vary the amber weight while holding the others fixed. Backpropagation gives the slope of the resulting loss curve.*
-/

-- Additional correctness theorem for the MLP's parameter derivatives;
-- no corresponding Rudin theorem.
theorem mlp_backward_is_derivative (θ : Nat → R) (x y : R) (i : Nat) :
    HasDerivative
      (fun t => eval Speedrun.exp (perturb θ (fun j => if i=j then 1 else 0) t) (trainingLoss x y)) 0
      (backward Speedrun.exp θ (trainingLoss x y) 1 i) :=
  backward_is_derivative θ _ i (trainingLoss_regular θ x y)

end Expr

end

end Speedrun
