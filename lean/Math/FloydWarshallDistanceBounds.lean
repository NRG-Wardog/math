import Math.AdmissibilityOfCostPartitionedBellmanPotentials

/-! A generic, nonnegative-weight Floyd–Warshall formalization.
    Infinity is represented by none. The proof is independent of applications. -/
namespace Math.FloydWarshall

open Math.CostPartitionedBellman
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

abbrev Distance := Option Nat
abbrev Matrix := Nat → Nat → Distance

def distLE : Distance → Distance → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

def distAdd : Distance → Distance → Distance
  | some a, some b => some (a+b)
  | _, _ => none

def distMin : Distance → Distance → Distance
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

theorem distLE_refl (a : Distance) : distLE a a := by
  cases a <;> simp [distLE]

theorem distLE_trans {a b c : Distance} (hab : distLE a b) (hbc : distLE b c) :
    distLE a c := by
  cases a <;> cases b <;> cases c <;> simp [distLE] at * <;> omega

theorem distAdd_mono {a b c d : Distance} (h₁ : distLE a b) (h₂ : distLE c d) :
    distLE (distAdd a c) (distAdd b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [distLE, distAdd] at * <;> omega

theorem distAdd_assoc (a b c : Distance) :
    distAdd (distAdd a b) c = distAdd a (distAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [distAdd, Nat.add_assoc]

theorem distLE_add_right (a b : Distance) : distLE a (distAdd a b) := by
  cases a <;> cases b <;> simp [distLE, distAdd] <;> omega

theorem distLE_add_left (a b : Distance) : distLE b (distAdd a b) := by
  cases a <;> cases b <;> simp [distLE, distAdd] <;> omega

theorem distAdd_zero_left (a : Distance) : distAdd (some 0) a = a := by
  cases a <;> simp [distAdd]

theorem distAdd_zero_right (a : Distance) : distAdd a (some 0) = a := by
  cases a <;> simp [distAdd]

theorem distMin_le_left (a b : Distance) : distLE (distMin a b) a := by
  cases a <;> cases b <;> simp [distMin, distLE, Nat.min_le_left]

theorem distMin_le_right (a b : Distance) : distLE (distMin a b) b := by
  cases a <;> cases b <;> simp [distMin, distLE, Nat.min_le_right]

theorem distMin_self (a : Distance) : distMin a a = a := by
  cases a <;> simp [distMin]

theorem distMin_zero (a : Distance) : distMin (some 0) a = some 0 := by
  cases a <;> simp [distMin]

theorem distMin_repeat (a b : Distance) :
    distMin (distMin a b) b = distMin a b := by
  cases a <;> cases b <;> simp [distMin, Nat.min_assoc]

theorem distMin_choice (a b : Distance) : distMin a b = a ∨ distMin a b = b := by
  cases a with
  | none => exact Or.inr rfl
  | some x =>
    cases b with
    | none => exact Or.inl rfl
    | some y =>
      rcases Nat.le_total x y with h | h
      · exact Or.inl (by simp [distMin, Nat.min_eq_left h])
      · exact Or.inr (by simp [distMin, Nat.min_eq_right h])

def ZeroDiagonal (d : Matrix) : Prop := ∀ a, d a a = some 0

def PivotTriangle (d : Matrix) (v : Nat) : Prop :=
  ∀ a b, distLE (d a b) (distAdd (d a v) (d v b))

def fwStep (d : Matrix) (k : Nat) : Matrix :=
  fun a b => distMin (d a b) (distAdd (d a k) (d k b))

theorem fwStep_le (d : Matrix) (k a b : Nat) :
    distLE (fwStep d k a b) (d a b) :=
  distMin_le_left _ _

theorem fwStep_diag (d : Matrix) (k : Nat) (hd : ZeroDiagonal d) :
    ZeroDiagonal (fwStep d k) := by
  intro a
  unfold fwStep
  rw [hd a]
  exact distMin_zero _

theorem fwStep_row (d : Matrix) (k : Nat) (hd : ZeroDiagonal d) (b : Nat) :
    fwStep d k k b = d k b := by
  unfold fwStep
  rw [hd k, distAdd_zero_left, distMin_self]

theorem fwStep_col (d : Matrix) (k : Nat) (hd : ZeroDiagonal d) (a : Nat) :
    fwStep d k a k = d a k := by
  unfold fwStep
  rw [hd k, distAdd_zero_right, distMin_self]

theorem fwStep_new_triangle (d : Matrix) (k : Nat) (hd : ZeroDiagonal d) :
    PivotTriangle (fwStep d k) k := by
  intro a b
  rw [fwStep_col d k hd a, fwStep_row d k hd b]
  exact distMin_le_right _ _

theorem fwStep_preserves_triangle (d : Matrix) (k v : Nat)
    (tri : PivotTriangle d v) : PivotTriangle (fwStep d k) v := by
  intro a b
  change distLE (distMin (d a b) (distAdd (d a k) (d k b)))
    (distAdd (distMin (d a v) (distAdd (d a k) (d k v)))
             (distMin (d v b) (distAdd (d v k) (d k b))))
  rcases distMin_choice (d a v) (distAdd (d a k) (d k v)) with hl | hl <;>
    rcases distMin_choice (d v b) (distAdd (d v k) (d k b)) with hr | hr <;>
    rw [hl, hr]
  · exact distLE_trans (distMin_le_left _ _) (tri a b)
  · apply distLE_trans (distMin_le_right _ _)
    rw [← distAdd_assoc]
    exact distAdd_mono (tri a k) (distLE_refl _)
  · apply distLE_trans (distMin_le_right _ _)
    rw [distAdd_assoc]
    exact distAdd_mono (distLE_refl _) (tri k b)
  · exact distLE_trans (distMin_le_right _ _)
      (distAdd_mono (distLE_add_right _ _) (distLE_add_left _ _))

def fwCell (d : Matrix) (k : Nat) (ij : Nat × Nat) : Matrix :=
  fun a b => if (a,b) = ij then fwStep d k a b else d a b

theorem fwCell_diag (d : Matrix) (k : Nat) (ij : Nat × Nat)
    (hd : ZeroDiagonal d) : ZeroDiagonal (fwCell d k ij) := by
  intro a
  unfold fwCell
  split
  · exact fwStep_diag d k hd a
  · exact hd a

theorem fwCell_row (d : Matrix) (k : Nat) (ij : Nat × Nat)
    (hd : ZeroDiagonal d) (b : Nat) : fwCell d k ij k b = d k b := by
  unfold fwCell
  split
  · exact fwStep_row d k hd b
  · rfl

theorem fwCell_col (d : Matrix) (k : Nat) (ij : Nat × Nat)
    (hd : ZeroDiagonal d) (a : Nat) : fwCell d k ij a k = d a k := by
  unfold fwCell
  split
  · exact fwStep_col d k hd a
  · rfl

theorem fwCell_step_stable (d : Matrix) (k : Nat) (ij : Nat × Nat)
    (hd : ZeroDiagonal d) (a b : Nat) :
    fwStep (fwCell d k ij) k a b = fwStep d k a b := by
  change distMin (fwCell d k ij a b)
    (distAdd (fwCell d k ij a k) (fwCell d k ij k b)) = fwStep d k a b
  rw [fwCell_col d k ij hd a, fwCell_row d k ij hd b]
  unfold fwCell
  split
  · exact distMin_repeat _ _
  · rfl

def fwSweep (d : Matrix) (k : Nat) : List (Nat × Nat) → Matrix
  | [] => d
  | ij :: rest => fwSweep (fwCell d k ij) k rest

theorem fwSweep_entry (d : Matrix) (k : Nat) (cells : List (Nat × Nat))
    (hd : ZeroDiagonal d) (a b : Nat) :
    fwSweep d k cells a b = if (a,b) ∈ cells then fwStep d k a b else d a b := by
  induction cells generalizing d with
  | nil => simp [fwSweep]
  | cons ij rest ih =>
    simp only [fwSweep]
    rw [ih (fwCell d k ij) (fwCell_diag d k ij hd)]
    by_cases hm : (a,b) ∈ rest
    · simp [hm, fwCell_step_stable d k ij hd a b]
    · by_cases heq : (a,b) = ij
      · simp [hm, heq, fwCell]
      · simp [hm, heq, fwCell]

theorem fwSweep_complete (d : Matrix) (k : Nat) (cells : List (Nat × Nat))
    (hd : ZeroDiagonal d) (a b : Nat) (visited : (a,b) ∈ cells) :
    fwSweep d k cells a b = fwStep d k a b := by
  rw [fwSweep_entry d k cells hd a b, if_pos visited]

def fwRun (d : Matrix) : List Nat → Matrix
  | [] => d
  | k :: ks => fwRun (fwStep d k) ks

theorem fwRun_le (d : Matrix) (pivots : List Nat) (a b : Nat) :
    distLE (fwRun d pivots a b) (d a b) := by
  induction pivots generalizing d with
  | nil => exact distLE_refl _
  | cons k ks ih =>
    exact distLE_trans (ih (fwStep d k)) (fwStep_le d k a b)

theorem fwRun_diag (d : Matrix) (pivots : List Nat) (hd : ZeroDiagonal d) :
    ZeroDiagonal (fwRun d pivots) := by
  induction pivots generalizing d with
  | nil => exact hd
  | cons k ks ih => exact ih (fwStep d k) (fwStep_diag d k hd)

theorem fwRun_keeps_triangle (d : Matrix) (pivots : List Nat) (v : Nat)
    (tri : PivotTriangle d v) : PivotTriangle (fwRun d pivots) v := by
  induction pivots generalizing d with
  | nil => exact tri
  | cons k ks ih => exact ih (fwStep d k) (fwStep_preserves_triangle d k v tri)

theorem fwRun_triangle_of_mem (d : Matrix) (pivots : List Nat) (v : Nat)
    (hd : ZeroDiagonal d) (hm : v ∈ pivots) : PivotTriangle (fwRun d pivots) v := by
  induction pivots generalizing d with
  | nil => simp at hm
  | cons k ks ih =>
    rcases List.mem_cons.mp hm with heq | ht
    · subst k
      exact fwRun_keeps_triangle (fwStep d v) ks v (fwStep_new_triangle d v hd)
    · exact ih (fwStep d k) (fwStep_diag d k hd) ht

-- Nonnegative weighted transition relation. The input matrix may be any
-- lower bound on each concrete edge; no optimum is assumed as a premise.
theorem computed_edge_budget (d : Matrix) (pivots : List Nat)
    (hd : ZeroDiagonal d) (edge : Nat → Nat → Nat → Prop)
    (hEdge : ∀ a b c, edge a b c → distLE (d a b) (some c))
    (covered : ∀ a b c, edge a b c → b ∈ pivots)
    (a b g c : Nat) (he : edge a b c) :
    distLE (fwRun d pivots a g) (distAdd (some c) (fwRun d pivots b g)) := by
  have tri := fwRun_triangle_of_mem d pivots b hd (covered a b c he)
  have hb := distLE_trans (fwRun_le d pivots a b) (hEdge a b c he)
  exact distLE_trans (tri a g) (distAdd_mono hb (distLE_refl _))

theorem computed_path_budget (d : Matrix) (pivots : List Nat)
    (hd : ZeroDiagonal d) (edge : Nat → Nat → Nat → Prop)
    (hEdge : ∀ a b c, edge a b c → distLE (d a b) (some c))
    (covered : ∀ a b c, edge a b c → b ∈ pivots)
    {s t c : Nat} (p : Path edge s t c) :
    ∃ x, fwRun d pivots s t = some x ∧ x ≤ c := by
  induction p with
  | done s => exact ⟨0, fwRun_diag d pivots hd s, Nat.le_refl _⟩
  | more s u t a b first rest ih =>
    rcases ih with ⟨y,hy,hyb⟩
    have h := computed_edge_budget d pivots hd edge hEdge covered s u t a first
    rw [hy] at h
    cases hx : fwRun d pivots s t with
    | none => simp [hx, distLE, distAdd] at h
    | some x =>
      have hxy : x ≤ a+y := by simpa [hx, distLE, distAdd] using h
      exact ⟨x,rfl,by omega⟩

#print axioms fwStep_preserves_triangle
#print axioms fwStep_new_triangle
#print axioms fwSweep_complete
#print axioms fwRun_triangle_of_mem
#print axioms computed_edge_budget
#print axioms computed_path_budget

end Math.FloydWarshall
