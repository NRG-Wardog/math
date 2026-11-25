import Lean

/-! General theorems on nonnegative weighted transition systems.
These results do not formalize a particular solver or assert its correctness.
-/
namespace Math.CostPartitionedBellman

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

inductive Path {S : Type} (edge : S → S → Nat → Prop) : S → S → Nat → Prop where
  | done (s : S) : Path edge s s 0
  | more (s u t : S) (c k : Nat) (first : edge s u c)
      (rest : Path edge u t k) : Path edge s t (c + k)

def Admissible {S : Type} (edge : S → S → Nat → Prop)
    (goal : S → Prop) (h : S → Nat) : Prop :=
  ∀ s t c, Path edge s t c → goal t → h s ≤ c

theorem bellman_admissible {S : Type} (edge : S → S → Nat → Prop)
    (goal : S → Prop) (d : S → Nat)
    (atGoal : ∀ t, goal t → d t = 0)
    (bellman : ∀ s u c, edge s u c → d s ≤ c + d u) :
    Admissible edge goal d := by
  intro s t c p
  induction p with
  | done s =>
    intro hg
    simp [atGoal s hg]
  | more s u t a b first rest ih =>
    intro hg
    have h1 := bellman s u a first
    have h2 := ih hg
    omega

theorem abstraction_admissible {S A : Type}
    (edge : S → S → Nat → Prop) (goal : S → Prop)
    (ae : A → A → Nat → Prop) (ag : A → Prop)
    (project : S → A) (d : A → Nat)
    (goalMap : ∀ s, goal s → ag (project s))
    (stepMap : ∀ s u c, edge s u c →
      project s = project u ∨ ∃ k, k ≤ c ∧ ae (project s) (project u) k)
    (az : ∀ x, ag x → d x = 0)
    (ab : ∀ x y c, ae x y c → d x ≤ c + d y) :
    Admissible edge goal (fun s => d (project s)) := by
  apply bellman_admissible
  · intro t hg
    exact az (project t) (goalMap t hg)
  · intro s u c he
    rcases stepMap s u c he with heq | ⟨k, hk, ha⟩
    · rw [heq]
      omega
    · have hb := ab (project s) (project u) k ha
      omega

structure ChargedPotential (S : Type) where
  estimate : S → Nat
  charge : S → S → Nat → Nat

def estimateSum {S : Type} : List (ChargedPotential S) → S → Nat
  | [], _ => 0
  | p :: ps, s => p.estimate s + estimateSum ps s

def chargeSum {S : Type} : List (ChargedPotential S) → S → S → Nat → Nat
  | [], _, _, _ => 0
  | p :: ps, s, t, c => p.charge s t c + chargeSum ps s t c

theorem sum_step {S : Type} (ps : List (ChargedPotential S))
    (s t : S) (c : Nat)
    (hstep : ∀ p, p ∈ ps → p.estimate s ≤ p.charge s t c + p.estimate t) :
    estimateSum ps s ≤ chargeSum ps s t c + estimateSum ps t := by
  induction ps with
  | nil => simp [estimateSum, chargeSum]
  | cons p ps ih =>
    have hp := hstep p (by simp)
    have ht := ih (fun q hq => hstep q (List.mem_cons_of_mem p hq))
    simp only [estimateSum, chargeSum]
    omega

theorem sum_zero {S : Type} (ps : List (ChargedPotential S)) (s : S)
    (hz : ∀ p, p ∈ ps → p.estimate s = 0) :
    estimateSum ps s = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hz p (by simp)
    have ht := ih (fun q hq => hz q (List.mem_cons_of_mem p hq))
    simp [estimateSum, hp, ht]

theorem additive_admissible {S : Type}
    (edge : S → S → Nat → Prop) (goal : S → Prop)
    (ps : List (ChargedPotential S))
    (hz : ∀ p, p ∈ ps → ∀ s, goal s → p.estimate s = 0)
    (hstep : ∀ p, p ∈ ps → ∀ s t c, edge s t c →
       p.estimate s ≤ p.charge s t c + p.estimate t)
    (budget : ∀ s t c, edge s t c → chargeSum ps s t c ≤ c) :
    Admissible edge goal (estimateSum ps) := by
  apply bellman_admissible
  · intro s hg
    exact sum_zero ps s (fun p hp => hz p hp s hg)
  · intro s t c he
    have h := sum_step ps s t c (fun p hp => hstep p hp s t c he)
    have b := budget s t c he
    omega

def maximum {S : Type} : List (S → Nat) → S → Nat
  | [], _ => 0
  | h :: hs, s => max (h s) (maximum hs s)

theorem maximum_budget {S : Type} (hs : List (S → Nat)) (s : S) (b : Nat)
    (h : ∀ f, f ∈ hs → f s ≤ b) :
    maximum hs s ≤ b := by
  induction hs with
  | nil => exact Nat.zero_le _
  | cons f fs ih =>
    exact Nat.max_le_of_le_of_le (h f (by simp))
      (ih (fun q hq => h q (List.mem_cons_of_mem f hq)))

theorem maximum_admissible {S : Type}
    (edge : S → S → Nat → Prop) (goal : S → Prop)
    (hs : List (S → Nat))
    (sound : ∀ h, h ∈ hs → Admissible edge goal h) :
    Admissible edge goal (maximum hs) := by
  intro s t c path hg
  exact maximum_budget hs s c (fun h hm => sound h hm s t c path hg)

#print axioms bellman_admissible
#print axioms abstraction_admissible
#print axioms sum_step
#print axioms sum_zero
#print axioms additive_admissible
#print axioms maximum_budget
#print axioms maximum_admissible

end Math.CostPartitionedBellman
