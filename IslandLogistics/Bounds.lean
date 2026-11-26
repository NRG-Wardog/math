import Lean.Elab.Tactic.Omega

/-!
  Island Logistics: research proof kernel.
  This proves path-potential, cost-partition and crossing-inventory lemmas.
  The full Python-to-Lean refinement and pruning proof are NOT certified here.
  No assignment identifiers or private data are included.
-/
namespace IslandLogistics

inductive Path {S : Type} (edge : S → S → Nat → Nat → Prop) :
    S → S → Nat → Nat → Prop where
  | nil (s : S) : Path edge s s 0 0
  | cons {s t u : S} {a b m h : Nat} :
      edge s t a b → Path edge t u m h → Path edge s u (a + m) (b + h)

theorem potential_bound {S : Type} {edge : S → S → Nat → Nat → Prop}
    (pot : S → Nat) (stepBound : ∀ s t a b, edge s t a b → pot s ≤ a + pot t)
    {s t : S} {m h : Nat} (p : Path edge s t m h) :
    pot s ≤ m + pot t := by
  induction p with
  | nil s => simp
  | cons step rest ih =>
    have he := stepBound _ _ _ _ step
    omega

theorem handling_bound {S : Type} {edge : S → S → Nat → Nat → Prop}
    (pot : S → Nat) (stepBound : ∀ s t a b, edge s t a b → pot s ≤ b + pot t)
    {s t : S} {m h : Nat} (p : Path edge s t m h) :
    pot s ≤ h + pot t := by
  induction p with
  | nil s => simp
  | cons step rest ih =>
    have he := stepBound _ _ _ _ step
    omega

theorem partition_bound {S : Type} {edge : S → S → Nat → Nat → Prop}
    (transport handling : S → Nat)
    (ht : ∀ s t a b, edge s t a b → transport s ≤ a + transport t)
    (hh : ∀ s t a b, edge s t a b → handling s ≤ b + handling t)
    {s t : S} {m h : Nat} (p : Path edge s t m h)
    (gt : transport t = 0) (gh : handling t = 0) :
    transport s + handling s ≤ m + h := by
  have tm := potential_bound transport ht p
  have hm := handling_bound handling hh p
  omega

theorem max_bound (x y z : Nat) (hx : x ≤ z) (hy : y ≤ z) :
    max x y ≤ z := Nat.max_le.mpr ⟨hx, hy⟩

theorem sum_partition (h cut residual moves handle : Nat)
    (hh : h ≤ handle) (hc : cut ≤ moves) (hr : residual ≤ moves - cut) :
    h + cut + residual ≤ moves + handle := by omega

-- Explicitly alternating physical crossings. A truck cannot cross the same
-- cut twice in one direction without a crossing in the opposite direction.
inductive CrossTrace : Bool → Bool → Nat → Nat → Prop where
  | nil (s : Bool) : CrossTrace s s 0 0
  | enter {s : Bool} {i o : Nat} :
      CrossTrace true s i o → CrossTrace false s (i + 1) o
  | leave {s : Bool} {i o : Nat} :
      CrossTrace false s i o → CrossTrace true s i (o + 1)

def sideStock (s : Bool) : Nat := if s then 1 else 0

theorem crossing_balance {s t : Bool} {i o : Nat}
    (p : CrossTrace s t i o) : i + sideStock s = o + sideStock t := by
  induction p with
  | nil s => simp
  | enter rest ih => simp [sideStock] at ih ⊢; omega
  | leave rest ih => simp [sideStock] at ih ⊢; omega

theorem crossing_pair_form {s t : Bool} {i o : Nat}
    (p : CrossTrace s t i o) :
    ∃ k : Nat,
      i = k + (if s = false ∧ t = true then 1 else 0) ∧
      o = k + (if s = true ∧ t = false then 1 else 0) := by
  have h := crossing_balance p
  cases s <;> cases t <;> simp [sideStock] at h <;>
    refine ⟨min i o, ?_, ?_⟩ <;> simp <;> omega

theorem inventory_lower (i o enter leave stock trucks : Nat)
    (hi : i ≤ enter) (ho : o ≤ leave)
    (hb1 : enter ≤ leave + (trucks - stock))
    (hb2 : leave ≤ enter + stock) :
    i + o ≤ enter + leave ∧
    2 * i - (trucks - stock) ≤ enter + leave ∧
    2 * o - stock ≤ enter + leave := by omega

theorem ceil_lower (n d k : Nat) (hd : 0 < d) (hn : n ≤ k * d) :
    (n + d - 1) / d ≤ k := by
  have h : n + d - 1 < (k + 1) * d := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h' := (Nat.div_lt_iff_lt_mul hd).2 h
  omega

theorem paired_capacity_bound (I O oddI oddO C pairs : Nat)
    (hC : 0 < C) (hi : I ≤ pairs * C + oddI) (ho : O ≤ pairs * C + oddO) :
    max ((I - oddI + C - 1) / C) ((O - oddO + C - 1) / C) ≤ pairs := by
  apply max_bound
  · exact ceil_lower (I - oddI) C pairs hC (by omega)
  · exact ceil_lower (O - oddO) C pairs hC (by omega)

#print axioms potential_bound
#print axioms partition_bound
#print axioms crossing_pair_form
#print axioms paired_capacity_bound
end IslandLogistics
