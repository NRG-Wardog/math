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


namespace IslandLogistics
-- Functional representation of the tuple encoding in the implementation.
-- Finite index bounds and capacity checks are part of the transition rules.
inductive TruckPosition where
  | land : Nat → TruckPosition
  | onFerry : Nat → TruckPosition
  deriving DecidableEq

inductive ParcelPosition where
  | ground : Nat → ParcelPosition
  | onTruck : Nat → ParcelPosition
  deriving DecidableEq

structure World where
  locations : Nat
  trucks : Nat
  ferries : Nat
  parcels : Nat
  road : Nat → Nat → Prop
  route : Nat → Nat → Prop
  capacity : Nat → Nat
  slots : Nat → Nat
  weight : Nat → Nat
  goal : Nat → Nat

structure State where
  truck : Nat → TruckPosition
  ferry : Nat → Nat
  parcel : Nat → ParcelPosition

def setAt {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

def sumN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumN f n + f n

def load (w : World) (s : State) (t : Nat) : Nat :=
  sumN (fun p => if s.parcel p = .onTruck t then w.weight p else 0) w.parcels

def occupancy (w : World) (s : State) (f : Nat) : Nat :=
  sumN (fun t => if s.truck t = .onFerry f then 1 else 0) w.trucks

def Goal (w : World) (s : State) : Prop :=
  ∀ p, p < w.parcels → s.parcel p = .ground (w.goal p)

-- Cost indices split movement and handling (sum equals actual action cost).
inductive Step (w : World) : State → State → Nat → Nat → Prop where
  | drive (s : State) (t a b : Nat)
      (ht : s.truck t = .land a) (hr : w.road a b)
      (valid : t < w.trucks ∧ a < w.locations ∧ b < w.locations) :
      Step w s {s with truck := setAt s.truck t (.land b)} 1 0
  | board (s : State) (t f a : Nat)
      (ht : s.truck t = .land a) (hf : s.ferry f = a) (hr : w.route f a)
      (room : occupancy w s f < w.slots f)
      (valid : t < w.trucks ∧ f < w.ferries ∧ a < w.locations) :
      Step w s {s with truck := setAt s.truck t (.onFerry f)} 1 0
  | disembark (s : State) (t f : Nat)
      (ht : s.truck t = .onFerry f) (valid : t < w.trucks ∧ f < w.ferries) :
      Step w s {s with truck := setAt s.truck t (.land (s.ferry f))} 1 0
  | sail (s : State) (f b : Nat)
      (hr : w.route f b) (hne : s.ferry f ≠ b)
      (valid : f < w.ferries ∧ b < w.locations) :
      Step w s {s with ferry := setAt s.ferry f b} 3 0
  | load (s : State) (p t a : Nat)
      (hp : s.parcel p = .ground a) (ht : s.truck t = .land a)
      (room : load w s t + w.weight p ≤ w.capacity t)
      (valid : p < w.parcels ∧ t < w.trucks ∧ a < w.locations) :
      Step w s {s with parcel := setAt s.parcel p (.onTruck t)} 0 1
  | unload (s : State) (p t a : Nat)
      (hp : s.parcel p = .onTruck t) (ht : s.truck t = .land a)
      (valid : p < w.parcels ∧ t < w.trucks ∧ a < w.locations) :
      Step w s {s with parcel := setAt s.parcel p (.ground a)} 0 1

inductive Vertex where
  | ground : Nat → Vertex
  | aboard : Nat → Nat → Vertex
  deriving DecidableEq

structure Projection where
  vertex : Vertex
  ferry : Nat → Nat

def truckVertex (s : State) (t : Nat) : Vertex :=
  match s.truck t with
  | .land a => .ground a
  | .onFerry f => .aboard f (s.ferry f)

def parcelVertex (s : State) (p : Nat) : Vertex :=
  match s.parcel p with
  | .ground a => .ground a
  | .onTruck t => truckVertex s t

def project (s : State) (p : Nat) : Projection :=
  ⟨parcelVertex s p, s.ferry⟩

def sailVertex (v : Vertex) (f b : Nat) : Vertex :=
  match v with
  | .ground a => .ground a
  | .aboard g a => if g = f then .aboard g b else .aboard g a

-- Exact one-vehicle movement abstraction with all ferry coordinates retained.
-- Capacity, other trucks and package handling are relaxed.
inductive AStep (w : World) : Projection → Projection → Nat → Prop where
  | stay (x : Projection) (c : Nat) : AStep w x x c
  | drive (cfg : Nat → Nat) (a b : Nat) (hr : w.road a b) :
      AStep w ⟨.ground a, cfg⟩ ⟨.ground b, cfg⟩ 1
  | board (cfg : Nat → Nat) (f : Nat) :
      AStep w ⟨.ground (cfg f), cfg⟩ ⟨.aboard f (cfg f), cfg⟩ 1
  | disembark (cfg : Nat → Nat) (f : Nat) :
      AStep w ⟨.aboard f (cfg f), cfg⟩ ⟨.ground (cfg f), cfg⟩ 1
  | sail (cfg : Nat → Nat) (v : Vertex) (f b : Nat)
      (hr : w.route f b) (hne : cfg f ≠ b) :
      AStep w ⟨v, cfg⟩ ⟨sailVertex v f b, setAt cfg f b⟩ 3

theorem sail_projection (s : State) (p f b : Nat) :
    project {s with ferry := setAt s.ferry f b} p =
      ⟨sailVertex (parcelVertex s p) f b, setAt s.ferry f b⟩ := by
  cases hp : s.parcel p with
  | ground a => simp [project, parcelVertex, hp, sailVertex]
  | onTruck t =>
    cases ht : s.truck t with
    | land a => simp [project, parcelVertex, hp, truckVertex, ht, sailVertex]
    | onFerry g =>
      by_cases eq : g = f
      · subst g
        simp [project, parcelVertex, hp, truckVertex, ht, sailVertex, setAt]
      · simp [project, parcelVertex, hp, truckVertex, ht, sailVertex, setAt, eq]

theorem project_step (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) (p : Nat) : AStep w (project s p) (project u p) m := by
  cases st with
  | drive t a b ht hr valid =>
    cases hp : s.parcel p with
    | ground x =>
      simpa [project, parcelVertex, hp] using
        (AStep.stay (w := w) ⟨Vertex.ground x, s.ferry⟩ 1)
    | onTruck q =>
      by_cases eq : q = t
      · subst q
        simpa [project, parcelVertex, hp, truckVertex, ht, setAt] using
          (AStep.drive (w := w) s.ferry a b hr)
      · simpa [project, parcelVertex, hp, truckVertex, setAt, eq] using
          (AStep.stay (w := w) ⟨truckVertex s q, s.ferry⟩ 1)
  | board t f a ht hf hr room valid =>
    cases hp : s.parcel p with
    | ground x =>
      simpa [project, parcelVertex, hp] using
        (AStep.stay (w := w) ⟨Vertex.ground x, s.ferry⟩ 1)
    | onTruck q =>
      by_cases eq : q = t
      · subst q
        simpa [project, parcelVertex, hp, truckVertex, ht, setAt, hf] using
          (AStep.board (w := w) s.ferry f)
      · simpa [project, parcelVertex, hp, truckVertex, setAt, eq] using
          (AStep.stay (w := w) ⟨truckVertex s q, s.ferry⟩ 1)
  | disembark t f ht valid =>
    cases hp : s.parcel p with
    | ground x =>
      simpa [project, parcelVertex, hp] using
        (AStep.stay (w := w) ⟨Vertex.ground x, s.ferry⟩ 1)
    | onTruck q =>
      by_cases eq : q = t
      · subst q
        simpa [project, parcelVertex, hp, truckVertex, ht, setAt] using
          (AStep.disembark (w := w) s.ferry f)
      · simpa [project, parcelVertex, hp, truckVertex, setAt, eq] using
          (AStep.stay (w := w) ⟨truckVertex s q, s.ferry⟩ 1)
  | sail f b hr hne valid =>
    rw [sail_projection]
    exact AStep.sail s.ferry (parcelVertex s p) f b hr hne
  | load q t a hp ht room valid =>
    by_cases eq : p = q
    · subst p
      simpa [project, parcelVertex, hp, truckVertex, ht, setAt] using
        (AStep.stay (w := w) ⟨Vertex.ground a, s.ferry⟩ 0)
    · simpa [project, parcelVertex, setAt, eq, truckVertex] using
        (AStep.stay (w := w) (project s p) 0)
  | unload q t a hp ht valid =>
    by_cases eq : p = q
    · subst p
      simpa [project, parcelVertex, hp, truckVertex, ht, setAt] using
        (AStep.stay (w := w) ⟨Vertex.ground a, s.ferry⟩ 0)
    · simpa [project, parcelVertex, setAt, eq, truckVertex] using
        (AStep.stay (w := w) (project s p) 0)

-- A graph-edge certificate is a finite data obligation, not an assumption
-- of admissibility or a statement about optimal plans.
theorem single_parcel_bound (w : World) (p : Nat) (hp : p < w.parcels)
    (d : Projection → Nat)
    (edgeCertificate : ∀ x y c, AStep w x y c → d x ≤ c + d y)
    (goalCertificate : ∀ cfg, d ⟨.ground (w.goal p), cfg⟩ = 0)
    {s u : State} {m h : Nat} (path : Path (Step w) s u m h)
    (goal : Goal w u) : d (project s p) ≤ m := by
  have hh := potential_bound (fun s => d (project s p))
    (fun s t a b st => edgeCertificate _ _ _ (project_step w st p)) path
  have hz : d (project u p) = 0 := by
    simpa [project, parcelVertex, goal p hp] using goalCertificate u.ferry
  change d (project s p) ≤ m + d (project u p) at hh
  rw [hz, Nat.add_zero] at hh
  exact hh

#print axioms project_step
#print axioms single_parcel_bound
end IslandLogistics


namespace IslandLogistics

theorem sumN_congr (f g : Nat → Nat) (n : Nat)
    (heq : ∀ q, q < n → f q = g q) : sumN f n = sumN g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e := heq n (by omega)
    have pref := ih (fun q hq => heq q (by omega))
    simp only [sumN]
    omega

theorem sumN_zero (n : Nat) : sumN (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumN, ih]

theorem sumN_one_change (f g : Nat → Nat) (p n : Nat)
    (heq : ∀ q, q ≠ p → f q = g q)
    (hp : f p ≤ 1 + g p) : sumN f n ≤ 1 + sumN g n := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
    by_cases eq : n = p
    · subst n
      have pref := sumN_congr f g p (fun q hq => heq q (by omega))
      simp only [sumN]
      omega
    · have e := heq n eq
      simp only [sumN]
      omega

def handleOne (w : World) (s : State) (p : Nat) : Nat :=
  match s.parcel p with
  | .ground a => if a = w.goal p then 0 else 2
  | .onTruck _ => 1

def handling (w : World) (s : State) : Nat :=
  sumN (handleOne w s) w.parcels

theorem handling_step (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) : handling w s ≤ h + handling w u := by
  cases st with
  | drive t a b ht hr valid =>
    rw [Nat.zero_add]
    exact Nat.le_refl _
  | board t f a ht hf hr room valid =>
    rw [Nat.zero_add]
    exact Nat.le_refl _
  | disembark t f ht valid =>
    rw [Nat.zero_add]
    exact Nat.le_refl _
  | sail f b hr hne valid =>
    rw [Nat.zero_add]
    exact Nat.le_refl _
  | load p t a hp ht room valid =>
    unfold handling
    apply sumN_one_change (p := p)
    · intro q neq
      simp [handleOne, setAt, neq]
    · simp [handleOne, setAt, hp]
      split <;> omega
  | unload p t a hp ht valid =>
    unfold handling
    apply sumN_one_change (p := p)
    · intro q neq
      simp [handleOne, setAt, neq]
    · simp [handleOne, setAt, hp]

theorem handling_goal (w : World) (s : State) (g : Goal w s) :
    handling w s = 0 := by
  unfold handling
  have e := sumN_congr (handleOne w s) (fun _ => 0) w.parcels
    (fun q hq => by simp [handleOne, g q hq])
  rw [e, sumN_zero]

theorem handling_path (w : World) {s u : State} {m h : Nat}
    (path : Path (Step w) s u m h) (g : Goal w u) :
    handling w s ≤ h := by
  have e := handling_bound (handling w) (fun _ _ _ _ st => handling_step w st) path
  rw [handling_goal w u g, Nat.add_zero] at e
  exact e

theorem single_parcel_plus_handling (w : World) (p : Nat) (hp : p < w.parcels)
    (d : Projection → Nat)
    (edgeCertificate : ∀ x y c, AStep w x y c → d x ≤ c + d y)
    (goalCertificate : ∀ cfg, d ⟨.ground (w.goal p), cfg⟩ = 0)
    {s u : State} {m h : Nat} (path : Path (Step w) s u m h)
    (goal : Goal w u) : d (project s p) + handling w s ≤ m + h := by
  have hd := single_parcel_bound w p hp d edgeCertificate goalCertificate path goal
  have hh := handling_path w path goal
  omega

#print axioms handling_step
#print axioms handling_path
#print axioms single_parcel_plus_handling
end IslandLogistics


namespace IslandLogistics

def sailAt (s : State) (f b : Nat) : State :=
  {s with ferry := setAt s.ferry f b}

theorem setAt_same (v : Nat → Nat) (f b c : Nat) :
    setAt (setAt v f b) f c = setAt v f c := by
  funext i
  by_cases e : i = f <;> simp [setAt, e]

theorem setAt_commute (v : Nat → Nat) (f g b c : Nat) (hne : g ≠ f) :
    setAt (setAt v f b) g c = setAt (setAt v g c) f b := by
  funext i
  by_cases e : i = f
  · subst i
    have hfg : f ≠ g := Ne.symm hne
    simp [setAt, hfg]
  · by_cases h : i = g <;> simp [setAt, e, h, hne]

-- Exactly the concrete transitions that do not perform a service or sail
-- on the selected ferry. A truck aboard it cannot drive/load/unload
-- because those operations require a land position.
inductive OtherStep (w : World) (f : Nat) : State → State → Nat → Nat → Prop where
  | drive (s : State) (t a b : Nat)
      (ht : s.truck t = .land a) (hr : w.road a b)
      (valid : t < w.trucks ∧ a < w.locations ∧ b < w.locations) :
      OtherStep w f s {s with truck := setAt s.truck t (.land b)} 1 0
  | board (s : State) (t g a : Nat)
      (diff : g ≠ f) (ht : s.truck t = .land a) (hg : s.ferry g = a)
      (hr : w.route g a) (room : occupancy w s g < w.slots g)
      (valid : t < w.trucks ∧ g < w.ferries ∧ a < w.locations) :
      OtherStep w f s {s with truck := setAt s.truck t (.onFerry g)} 1 0
  | disembark (s : State) (t g : Nat)
      (diff : g ≠ f) (ht : s.truck t = .onFerry g)
      (valid : t < w.trucks ∧ g < w.ferries) :
      OtherStep w f s {s with truck := setAt s.truck t (.land (s.ferry g))} 1 0
  | sail (s : State) (g b : Nat)
      (diff : g ≠ f) (hr : w.route g b) (hne : s.ferry g ≠ b)
      (valid : g < w.ferries ∧ b < w.locations) :
      OtherStep w f s (sailAt s g b) 3 0
  | load (s : State) (p t a : Nat)
      (hp : s.parcel p = .ground a) (ht : s.truck t = .land a)
      (room : load w s t + w.weight p ≤ w.capacity t)
      (valid : p < w.parcels ∧ t < w.trucks ∧ a < w.locations) :
      OtherStep w f s {s with parcel := setAt s.parcel p (.onTruck t)} 0 1
  | unload (s : State) (p t a : Nat)
      (hp : s.parcel p = .onTruck t) (ht : s.truck t = .land a)
      (valid : p < w.parcels ∧ t < w.trucks ∧ a < w.locations) :
      OtherStep w f s {s with parcel := setAt s.parcel p (.ground a)} 0 1

theorem other_is_step (w : World) (f : Nat) {s u : State} {m h : Nat}
    (step : OtherStep w f s u m h) : Step w s u m h := by
  cases step with
  | drive t a b ht hr valid => exact Step.drive s t a b ht hr valid
  | board t g a diff ht hg hr room valid => exact Step.board s t g a ht hg hr room valid
  | disembark t g diff ht valid => exact Step.disembark s t g ht valid
  | sail g b diff hr hne valid => exact Step.sail s g b hr hne valid
  | load p t a hp ht room valid => exact Step.load s p t a hp ht room valid
  | unload p t a hp ht valid => exact Step.unload s p t a hp ht valid

theorem other_preserves_ferry (w : World) (f : Nat) {s u : State} {m h : Nat}
    (step : OtherStep w f s u m h) : u.ferry f = s.ferry f := by
  cases step with
  | sail g b diff hr hne valid =>
    simp [sailAt, setAt, Ne.symm diff]
  | drive t a b ht hr valid => rfl
  | board t g a diff ht hg hr room valid => rfl
  | disembark t g diff ht valid => rfl
  | load p t a hp ht room valid => rfl
  | unload p t a hp ht valid => rfl

-- The same unrelated action can be replayed after any reposition of f;
-- its target is exactly the repositioned original target.
theorem other_commutes (w : World) (f b : Nat) {s u : State} {m h : Nat}
    (step : OtherStep w f s u m h) :
    OtherStep w f (sailAt s f b) (sailAt u f b) m h := by
  cases step with
  | drive t a c ht hr valid =>
    exact OtherStep.drive _ t a c ht hr valid
  | board t g a diff ht hg hr room valid =>
    have hg' : (sailAt s f b).ferry g = a := by simpa [sailAt, setAt, diff] using hg
    exact OtherStep.board _ t g a diff ht hg' hr room valid
  | disembark t g diff ht valid =>
    have hg' : (sailAt s f b).ferry g = s.ferry g := by simp [sailAt, setAt, diff]
    simpa [sailAt, setAt, diff] using
      (OtherStep.disembark (w := w) (f := f) (sailAt s f b) t g diff ht valid)
  | sail g c diff hr hne valid =>
    have hne' : (sailAt s f b).ferry g ≠ c := by simpa [sailAt, setAt, diff] using hne
    have eq : sailAt (sailAt s f b) g c = sailAt (sailAt s g c) f b := by
      unfold sailAt
      rw [setAt_commute s.ferry f g b c diff]
    rw [← eq]
    exact OtherStep.sail _ g c diff hr hne' valid
  | load p t a hp ht room valid =>
    exact OtherStep.load _ p t a hp ht room valid
  | unload p t a hp ht valid =>
    exact OtherStep.unload _ p t a hp ht valid

theorem other_path_is_path (w : World) (f : Nat) {s u : State} {m h : Nat}
    (p : Path (OtherStep w f) s u m h) : Path (Step w) s u m h := by
  induction p with
  | nil s => exact Path.nil s
  | cons step rest ih => exact Path.cons (other_is_step w f step) ih

theorem other_path_preserves_ferry (w : World) (f : Nat)
    {s u : State} {m h : Nat} (p : Path (OtherStep w f) s u m h) :
    u.ferry f = s.ferry f := by
  induction p with
  | nil s => rfl
  | cons step rest ih => exact ih.trans (other_preserves_ferry w f step)

theorem other_path_commutes (w : World) (f b : Nat)
    {s u : State} {m h : Nat} (p : Path (OtherStep w f) s u m h) :
    Path (OtherStep w f) (sailAt s f b) (sailAt u f b) m h := by
  induction p with
  | nil s => exact Path.nil _
  | cons step rest ih => exact Path.cons (other_commutes w f b step) ih

-- Delay a sail until after an arbitrary prefix with no events on that
-- ferry. The result is exactly the same state, and the cost is unchanged.
theorem delay_sail (w : World) (f b : Nat) {s u : State} {m h : Nat}
    (p : Path (OtherStep w f) s u m h)
    (hr : w.route f b) (hne : s.ferry f ≠ b)
    (valid : f < w.ferries ∧ b < w.locations) :
    Step w u (sailAt u f b) 3 0 := by
  apply Step.sail u f b hr
  · rw [other_path_preserves_ferry w f p]
    exact hne
  · exact valid

-- Two consecutive sails, with no service between, can be replaced by
-- a single direct sail (or zero actions when returning to the start).
theorem contract_sails (w : World) (s : State) (f b c : Nat)
    (hr : w.route f c) (valid : f < w.ferries ∧ c < w.locations) :
    ∃ m : Nat, m ≤ 6 ∧ Path (Step w) s (sailAt (sailAt s f b) f c) m 0 := by
  have eq : sailAt (sailAt s f b) f c = sailAt s f c := by
    unfold sailAt
    rw [setAt_same]
  rw [eq]
  by_cases same : s.ferry f = c
  · have e : sailAt s f c = s := by
      cases s with
      | mk truck ferry parcel =>
        simp only [sailAt, State.mk.injEq, true_and, and_true]
        funext i
        by_cases hi : i = f
        · subst i
          simpa [setAt] using same.symm
        · simp [setAt, hi]
    rw [e]
    exact ⟨0, by omega, Path.nil s⟩
  · exact ⟨3, by omega, Path.cons (Step.sail s f c hr same valid) (Path.nil _)⟩

#print axioms other_commutes
#print axioms other_path_commutes
#print axioms delay_sail
#print axioms contract_sails
end IslandLogistics


namespace IslandLogistics

-- Extra charge for a physical UNLOAD outside a parcel's own goal.
-- This is exactly the 2-unit residual charged by the geographic
-- patterns (a projected non-goal is necessarily a real non-goal).
def extraOne (w : World) (s u : State) (p : Nat) : Nat :=
  match s.parcel p, u.parcel p with
  | .onTruck _, .ground a => if a = w.goal p then 0 else 2
  | _, _ => 0

def extraUnload (w : World) (s u : State) : Nat :=
  sumN (extraOne w s u) w.parcels

theorem sumN_add (f g : Nat → Nat) (n : Nat) :
    sumN (fun q => f q + g q) n = sumN f n + sumN g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumN, ih]
    omega

theorem extra_same (w : World) (s u : State) (p : Nat)
    (he : s.parcel p = u.parcel p) :
    extraOne w s u p = 0 := by
  unfold extraOne
  rw [he]
  cases u.parcel p <;> rfl

theorem residual_same (w : World) (s u : State) (p : Nat)
    (he : s.parcel p = u.parcel p) :
    handleOne w s p + extraOne w s u p = handleOne w u p := by
  rw [extra_same w s u p he, Nat.add_zero]
  simp only [handleOne, he]

theorem residual_unchanged (w : World) (s u : State)
    (he : s.parcel = u.parcel) :
    handling w s + extraUnload w s u ≤ 0 + handling w u := by
  unfold handling extraUnload
  rw [← sumN_add, Nat.zero_add]
  have h := sumN_congr
    (fun q => handleOne w s q + extraOne w s u q)
    (handleOne w u) w.parcels
    (fun q _ => residual_same w s u q (congrFun he q))
  rw [h]
  exact Nat.le_refl _

theorem residual_step (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) :
    handling w s + extraUnload w s u ≤ h + handling w u := by
  cases st with
  | drive t a b ht hr valid => exact residual_unchanged w _ _ rfl
  | board t f a ht hf hr room valid => exact residual_unchanged w _ _ rfl
  | disembark t f ht valid => exact residual_unchanged w _ _ rfl
  | sail f b hr hne valid => exact residual_unchanged w _ _ rfl
  | load p t a hp ht room valid =>
    unfold handling extraUnload
    rw [← sumN_add]
    apply sumN_one_change (p := p)
    · intro q neq
      apply residual_same
      simp [setAt, neq]
    · simp [handleOne, extraOne, hp, setAt]
      split <;> omega
  | unload p t a hp ht valid =>
    unfold handling extraUnload
    rw [← sumN_add]
    apply sumN_one_change (p := p)
    · intro q neq
      apply residual_same
      simp [setAt, neq]
    · simp [handleOne, extraOne, hp, setAt]

-- The index e is the actual sum of non-goal unloading charges along the
-- path, not an assumed bound on the true optimum.
inductive ResidualPath (w : World) : State → State → Nat → Nat → Nat → Prop where
  | nil (s : State) : ResidualPath w s s 0 0 0
  | cons {s t u : State} {a b m h e : Nat} :
      Step w s t a b → ResidualPath w t u m h e →
      ResidualPath w s u (a + m) (b + h) (extraUnload w s t + e)

theorem residual_path_budget (w : World) {s u : State} {m h e : Nat}
    (p : ResidualPath w s u m h e) :
    handling w s + e ≤ h + handling w u := by
  induction p with
  | nil s => simp
  | cons st rest ih =>
    have he := residual_step w st
    omega

theorem residual_goal_budget (w : World) {s u : State} {m h e : Nat}
    (p : ResidualPath w s u m h e) (g : Goal w u) :
    handling w s + e ≤ h := by
  have he := residual_path_budget w p
  rw [handling_goal w u g, Nat.add_zero] at he
  exact he

theorem residual_path_is_path (w : World) {s u : State} {m h e : Nat}
    (p : ResidualPath w s u m h e) : Path (Step w) s u m h := by
  induction p with
  | nil s => exact Path.nil _
  | cons step rest ih => exact Path.cons step ih

-- Each candidate route/assignment has a handling penalty. It is enough
-- that there exists the witness induced by the actual completion.
-- This arithmetic theorem does not assert that the Python DP finds it.
theorem transfer_witness_combine (handling0 movement routeCost extraCost
    r m h candidate : Nat)
    (hm : movement ≤ m) (hr : routeCost + extraCost ≤ m)
    (hh : handling0 + 2*r ≤ h)
    (hc : candidate ≤ 2*r + max movement (routeCost + extraCost)) :
    handling0 + candidate ≤ m + h := by
  have hm' : max movement (routeCost + extraCost) ≤ m :=
    max_bound _ _ _ hm hr
  omega

#print axioms residual_step
#print axioms residual_path_budget
#print axioms residual_goal_budget
#print axioms transfer_witness_combine
end IslandLogistics
