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


namespace IslandLogistics

/- A counterexample to the stronger contract quantifying over all
   well-formed configurations, including ones unreachable from INIT.
   This is NOT a counterexample over the reachable-state space. -/
def disconnectedWorld : World where
  locations := 5
  trucks := 2
  ferries := 0
  parcels := 1
  road a b := a < 4 ∧ b < 4 ∧ (a + 1 = b ∨ b + 1 = a)
  route _ _ := False
  capacity _ := 1
  slots _ := 0
  weight _ := 1
  goal _ := 2

def disconnectedInit : State :=
  ⟨fun t => .land (if t = 0 then 3 else 4), fun _ => 0, fun _ => .ground 3⟩

def disconnectedBad : State :=
  ⟨fun _ => .land 3, fun _ => 0, fun _ => .ground 3⟩

def disconnectedLoaded : State :=
  {disconnectedBad with parcel := setAt disconnectedBad.parcel 0 (.onTruck 0)}

def disconnectedDriven : State :=
  {disconnectedLoaded with truck := setAt disconnectedLoaded.truck 0 (.land 2)}

def disconnectedDone : State :=
  {disconnectedDriven with parcel := setAt disconnectedDriven.parcel 0 (.ground 2)}

theorem disconnected_three_cost :
    Path (Step disconnectedWorld) disconnectedBad disconnectedDone 1 2 := by
  have e1 : Step disconnectedWorld disconnectedBad disconnectedLoaded 0 1 :=
    Step.load disconnectedBad 0 0 3 rfl rfl (by decide) (by decide)
  have e2 : Step disconnectedWorld disconnectedLoaded disconnectedDriven 1 0 :=
    Step.drive disconnectedLoaded 0 3 2 rfl (by change 3 < 4 ∧ 2 < 4 ∧ (3 + 1 = 2 ∨ 2 + 1 = 3); decide) (by decide)
  have e3 : Step disconnectedWorld disconnectedDriven disconnectedDone 0 1 :=
    Step.unload disconnectedDriven 0 0 2 rfl rfl (by decide)
  exact Path.cons e1 (Path.cons e2 (Path.cons e3 (Path.nil _)))

theorem disconnected_done_goal : Goal disconnectedWorld disconnectedDone := by
  intro p hp
  have hz : p = 0 := by change p < 1 at hp; omega
  subst p
  rfl

theorem isolated_truck_step {s u : State} {m h : Nat}
    (st : Step disconnectedWorld s u m h)
    (initial : s.truck 1 = .land 4) : u.truck 1 = .land 4 := by
  cases st with
  | drive t a b ht hr valid =>
    by_cases ht1 : t = 1
    · subst t
      have ha : a = 4 := TruckPosition.land.inj (ht.symm.trans initial)
      subst a
      change 4 < 4 ∧ b < 4 ∧ (4 + 1 = b ∨ b + 1 = 4) at hr
      omega
    · change setAt s.truck t (.land b) 1 = .land 4
      simp [setAt, Ne.symm ht1, initial]
  | board t f a ht hf hr room valid =>
    change t < 2 ∧ f < 0 ∧ a < 5 at valid
    omega
  | disembark t f ht valid =>
    change t < 2 ∧ f < 0 at valid
    omega
  | sail f b hr hne valid =>
    change f < 0 ∧ b < 5 at valid
    omega
  | load p t a hp ht room valid => exact initial
  | unload p t a hp ht valid => exact initial

theorem isolated_truck_path {s u : State} {m h : Nat}
    (p : Path (Step disconnectedWorld) s u m h) :
    s.truck 1 = .land 4 → u.truck 1 = .land 4 := by
  induction p with
  | nil s => exact fun h => h
  | cons st rest ih =>
    intro hs
    exact ih (isolated_truck_step st hs)

theorem disconnected_bad_unreachable (m h : Nat) :
    ¬ Path (Step disconnectedWorld) disconnectedInit disconnectedBad m h := by
  intro p
  have h := isolated_truck_path p (by rfl)
  change TruckPosition.land 3 = TruckPosition.land 4 at h
  cases h

-- The three road-profile expressions used by the Python cut DP in
-- this example, with initial component budget 1 but current stock 2.
-- This theorem verifies their arithmetic, not Python refinement.
def disconnectedProfile (I O finish : Int) : Int :=
  max (2 * I - (finish - 2)) (2 * O + (finish - 2))

theorem disconnected_phantom_crossings (f1 f2 f3 : Int)
    (h1 : f1 ≤ 1) (h2 : f2 ≤ 1) (h3 : f3 ≤ 1) :
    3 ≤ disconnectedProfile 0 0 f1 +
      disconnectedProfile 0 0 f2 + disconnectedProfile 0 1 f3 := by
  unfold disconnectedProfile
  have a := Int.le_max_left (2 * (0 : Int) - (f1 - 2)) (2 * (0 : Int) + (f1 - 2))
  have b := Int.le_max_left (2 * (0 : Int) - (f2 - 2)) (2 * (0 : Int) + (f2 - 2))
  have c := Int.le_max_left (2 * (0 : Int) - (f3 - 2)) (2 * (1 : Int) + (f3 - 2))
  omega

theorem disconnected_phantom_exact :
    disconnectedProfile 0 0 1 + disconnectedProfile 0 0 1 +
      disconnectedProfile 0 1 1 = 3 := by decide

#print axioms disconnected_three_cost
#print axioms disconnected_done_goal
#print axioms disconnected_bad_unreachable
#print axioms disconnected_phantom_crossings
#print axioms disconnected_phantom_exact
end IslandLogistics


namespace IslandLogistics

def physicalTruck (s : State) (t : Nat) : Nat :=
  match s.truck t with
  | .land a => a
  | .onFerry f => s.ferry f

def physicalParcel (s : State) (p : Nat) : Nat :=
  match s.parcel p with
  | .ground a => a
  | .onTruck t => physicalTruck s t

-- Transport components are fixed by roads and *usable* ferry routes.
-- The assumptions below state precisely that the computed component map
-- is constant on those links. They do not assume anything about h or h*.
structure ComponentLabels (w : World) where
  label : Nat → Nat
  roads : ∀ a b, w.road a b → label a = label b
  ferry : ∀ f a b, 0 < w.slots f → w.route f a → w.route f b →
    label a = label b

def ValidFerries (w : World) (s : State) : Prop :=
  ∀ f, f < w.ferries → w.route f (s.ferry f)

def ValidTruckCarriers (w : World) (s : State) : Prop :=
  ∀ t, t < w.trucks → ∀ f, s.truck t = .onFerry f →
    f < w.ferries ∧ 0 < w.slots f

def ValidParcelCarriers (w : World) (s : State) : Prop :=
  ∀ p, p < w.parcels → ∀ t, s.parcel p = .onTruck t → t < w.trucks

theorem step_valid_ferries (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) (v : ValidFerries w s) : ValidFerries w u := by
  cases st with
  | sail f b hr hne valid =>
    intro g hg
    change w.route g (setAt s.ferry f b g)
    by_cases eq : g = f
    · subst g
      simpa [setAt] using hr
    · simpa [setAt, eq] using v g hg
  | drive t a b ht hr valid => exact v
  | board t f a ht hf hr room valid => exact v
  | disembark t f ht valid => exact v
  | load p t a hp ht room valid => exact v
  | unload p t a hp ht valid => exact v

theorem step_valid_truck_carriers (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) (v : ValidTruckCarriers w s) :
    ValidTruckCarriers w u := by
  cases st with
  | drive t a b ht hr valid =>
    intro q hq f hf
    change setAt s.truck t (.land b) q = .onFerry f at hf
    by_cases eq : q = t
    · subst q
      simp [setAt] at hf
    · exact v q hq f (by simpa [setAt, eq] using hf)
  | board t f a ht hf hr room valid =>
    intro q hq g hg
    change setAt s.truck t (.onFerry f) q = .onFerry g at hg
    by_cases eq : q = t
    · subst q
      have he : f = g := by simpa [setAt] using hg
      subst g
      exact ⟨valid.2.1, by omega⟩
    · exact v q hq g (by simpa [setAt, eq] using hg)
  | disembark t f ht valid =>
    intro q hq g hg
    change setAt s.truck t (.land (s.ferry f)) q = .onFerry g at hg
    by_cases eq : q = t
    · subst q
      simp [setAt] at hg
    · exact v q hq g (by simpa [setAt, eq] using hg)
  | sail f b hr hne valid => exact v
  | load p t a hp ht room valid => exact v
  | unload p t a hp ht valid => exact v

theorem step_valid_parcel_carriers (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) (v : ValidParcelCarriers w s) :
    ValidParcelCarriers w u := by
  cases st with
  | load p t a hp ht room valid =>
    intro q hq z hz
    change setAt s.parcel p (.onTruck t) q = .onTruck z at hz
    by_cases eq : q = p
    · subst q
      have he : t = z := by simpa [setAt] using hz
      subst z
      exact valid.2.1
    · exact v q hq z (by simpa [setAt, eq] using hz)
  | unload p t a hp ht valid =>
    intro q hq z hz
    change setAt s.parcel p (.ground a) q = .onTruck z at hz
    by_cases eq : q = p
    · subst q
      simp [setAt] at hz
    · exact v q hq z (by simpa [setAt, eq] using hz)
  | drive t a b ht hr valid => exact v
  | board t f a ht hf hr room valid => exact v
  | disembark t f ht valid => exact v
  | sail f b hr hne valid => exact v

theorem step_truck_component (w : World) (c : ComponentLabels w)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s)
    (q : Nat) (hq : q < w.trucks) :
    c.label (physicalTruck s q) = c.label (physicalTruck u q) := by
  cases st with
  | drive t a b ht hr valid =>
    by_cases eq : q = t
    · subst q
      simpa [physicalTruck, ht, setAt] using c.roads a b hr
    · simp [physicalTruck, setAt, eq]
  | board t f a ht hf hr room valid =>
    by_cases eq : q = t
    · subst q
      simp [physicalTruck, ht, hf, setAt]
    · simp [physicalTruck, setAt, eq]
  | disembark t f ht valid =>
    by_cases eq : q = t
    · subst q
      simp [physicalTruck, ht, setAt]
    · simp [physicalTruck, setAt, eq]
  | sail f b hr hne valid =>
    cases hq' : s.truck q with
    | land a => simp [physicalTruck, hq']
    | onFerry g =>
      by_cases eq : g = f
      · subst g
        have hh := vt q hq f hq'
        simpa [physicalTruck, hq', setAt] using
          c.ferry f (s.ferry f) b hh.2 (vf f hh.1) hr
      · simp [physicalTruck, hq', setAt, eq]
  | load p t a hp ht room valid => rfl
  | unload p t a hp ht valid => rfl

theorem step_parcel_component (w : World) (c : ComponentLabels w)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s)
    (vp : ValidParcelCarriers w s)
    (q : Nat) (hq : q < w.parcels) :
    c.label (physicalParcel s q) = c.label (physicalParcel u q) := by
  have hh := step_truck_component w c st vf vt
  cases st with
  | drive t a b ht hr valid =>
    cases hp : s.parcel q with
    | ground x => simp [physicalParcel, hp]
    | onTruck z => simpa [physicalParcel, hp] using hh z (vp q hq z hp)
  | board t f a ht hf hr room valid =>
    cases hp : s.parcel q with
    | ground x => simp [physicalParcel, hp]
    | onTruck z => simpa [physicalParcel, hp] using hh z (vp q hq z hp)
  | disembark t f ht valid =>
    cases hp : s.parcel q with
    | ground x => simp [physicalParcel, hp]
    | onTruck z => simpa [physicalParcel, hp] using hh z (vp q hq z hp)
  | sail f b hr hne valid =>
    cases hp : s.parcel q with
    | ground x => simp [physicalParcel, hp]
    | onTruck z => simpa [physicalParcel, hp] using hh z (vp q hq z hp)
  | load p t a hp ht room valid =>
    by_cases eq : q = p
    · subst q
      simp [physicalParcel, physicalTruck, hp, ht, setAt]
    · simp [physicalParcel, physicalTruck, setAt, eq]
  | unload p t a hp ht valid =>
    by_cases eq : q = p
    · subst q
      simp [physicalParcel, physicalTruck, hp, ht, setAt]
    · simp [physicalParcel, physicalTruck, setAt, eq]

theorem path_component_invariant (w : World) (c : ComponentLabels w)
    {s u : State} {m h : Nat} (path : Path (Step w) s u m h)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s)
    (vp : ValidParcelCarriers w s) :
    (∀ q, q < w.trucks →
      c.label (physicalTruck s q) = c.label (physicalTruck u q)) ∧
    (∀ q, q < w.parcels →
      c.label (physicalParcel s q) = c.label (physicalParcel u q)) := by
  induction path with
  | nil s => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons st rest ih =>
    have next := ih (step_valid_ferries w st vf)
      (step_valid_truck_carriers w st vt) (step_valid_parcel_carriers w st vp)
    exact ⟨fun q hq => (step_truck_component w c st vf vt q hq).trans (next.1 q hq),
      fun q hq => (step_parcel_component w c st vf vt vp q hq).trans (next.2 q hq)⟩

def componentStock (w : World) (c : ComponentLabels w) (s : State) (k : Nat) :=
  sumN (fun t => if c.label (physicalTruck s t) = k then 1 else 0) w.trucks

theorem reachable_stock_eq (w : World) (c : ComponentLabels w)
    {s u : State} {m h : Nat} (path : Path (Step w) s u m h)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s)
    (vp : ValidParcelCarriers w s) (k : Nat) :
    componentStock w c s k = componentStock w c u k := by
  apply sumN_congr
  intro t ht
  rw [(path_component_invariant w c path vf vt vp).1 t ht]

#print axioms path_component_invariant
#print axioms reachable_stock_eq

end IslandLogistics


namespace IslandLogistics

-- Exact per-truck crossing formula used by the coupled cut DP.
-- The premise is the actual crossing balance, not admissibility.
theorem coupled_cross_profile (I O i o delta : Int)
    (hI : I ≤ i) (hO : O ≤ o) (balance : i - o = delta) :
    2 * max I (O + delta) - delta ≤ i + o := by
  have h : max I (O + delta) ≤ i := by
    apply Int.max_le.mpr
    exact ⟨hI, by omega⟩
  omega

theorem aggregate_cross_profile (I O i o delta : Int)
    (hI : I ≤ i) (hO : O ≤ o) (balance : i - o = delta) :
    max (2*I-delta) (2*O+delta) ≤ i+o := by
  apply Int.max_le.mpr
  constructor <;> omega

def minCandidate (fallback : Nat) : List Nat → Nat
  | [] => fallback
  | x :: xs => min x (minCandidate fallback xs)

theorem minCandidate_le_member (fallback : Nat) (xs : List Nat) (x : Nat)
    (hx : x ∈ xs) : minCandidate fallback xs ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.mem_cons] at hx
    rcases hx with h | h
    · subst y
      exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih h)

-- Source-level route/cut assignment composition. The witness is the
-- particular retained-job assignment induced by a legal path. The
-- separate obligation that the executable enumerates this witness is
-- intentionally not hidden in the theorem statement.
theorem route_witness_admissible (w : World) {s u : State} {m a e : Nat}
    (p : ResidualPath w s u m a e) (g : Goal w u)
    (move route extra r fallback : Nat) (xs : List Nat)
    (hm : move ≤ m) (hr : route + extra ≤ m) (he : 2*r ≤ e)
    (member : 2*r + max move (route + extra) ∈ xs) :
    handling w s + minCandidate fallback xs ≤ m + a := by
  have hh := residual_goal_budget w p g
  have hmin := minCandidate_le_member fallback xs _ member
  have hmax := max_bound move (route+extra) m hm hr
  omega

theorem geographic_budget_admissible (w : World) {s u : State} {m a e : Nat}
    (p : ResidualPath w s u m a e) (g : Goal w u) (geo : Nat)
    (hgeo : geo ≤ m + e) :
    handling w s + geo ≤ m + a := by
  have hh := residual_goal_budget w p g
  omega

theorem ordinary_budget_admissible (w : World) {s u : State} {m a : Nat}
    (p : Path (Step w) s u m a) (g : Goal w u) (movement : Nat)
    (hm : movement ≤ m) : handling w s + movement ≤ m + a := by
  have hh := handling_path w p g
  omega

#print axioms coupled_cross_profile
#print axioms aggregate_cross_profile
#print axioms route_witness_admissible
#print axioms geographic_budget_admissible
#print axioms ordinary_budget_admissible

end IslandLogistics


namespace IslandLogistics
/-! Executable finite assignment enumeration and min-plus recurrence.
The code below verifies the actual least-significant-digit enumeration used
by DirectCutAssignments.assignment and the witness inequality of the
subset-min/merge recurrence. The concrete extraction of all geometric
witnesses and NumPy refinement remain separate obligations. -/

-- Exact minimum of a nonempty list, with a fallback ONLY on empty input.
-- In particular, no extra finite sentinel can weaken the Python DP.
def foldCutMin (seed : Nat) : List Nat → Nat
  | [] => seed
  | x :: xs => foldCutMin (min seed x) xs

theorem foldCutMin_le_seed (seed : Nat) (xs : List Nat) :
    foldCutMin seed xs ≤ seed := by
  induction xs generalizing seed with
  | nil => simp [foldCutMin]
  | cons x xs ih =>
    exact Nat.le_trans (ih (min seed x)) (Nat.min_le_left _ _)

theorem foldCutMin_le_member (seed : Nat) (xs : List Nat) (z : Nat)
    (hz : z ∈ xs) : foldCutMin seed xs ≤ z := by
  induction xs generalizing seed with
  | nil => simp at hz
  | cons x xs ih =>
    rw [List.mem_cons] at hz
    rcases hz with eq | h
    · subst z
      exact Nat.le_trans (foldCutMin_le_seed (min seed x) xs) (Nat.min_le_right _ _)
    · exact ih (min seed x) h

def exactCutMin (fallback : Nat) : List Nat → Nat
  | [] => fallback
  | x :: xs => foldCutMin x xs

theorem exactCutMin_le_member (fallback : Nat) (xs : List Nat) (z : Nat)
    (hz : z ∈ xs) : exactCutMin fallback xs ≤ z := by
  cases xs with
  | nil => simp at hz
  | cons x xs =>
    rw [List.mem_cons] at hz
    rcases hz with eq | h
    · subst z
      exact foldCutMin_le_seed _ _
    · exact foldCutMin_le_member _ _ _ h

theorem foldCutMin_attained (seed : Nat) (xs : List Nat) :
    foldCutMin seed xs ∈ seed :: xs := by
  induction xs generalizing seed with
  | nil => simp [foldCutMin]
  | cons x xs ih =>
    have h := ih (min seed x)
    rw [List.mem_cons] at h
    change foldCutMin (min seed x) xs ∈ seed :: x :: xs
    rcases h with eq | hm
    · rw [eq]
      by_cases he : seed ≤ x
      · rw [Nat.min_eq_left he]; simp
      · have he' : x ≤ seed := by omega
        rw [Nat.min_eq_right he']; simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

theorem exactCutMin_attained (fallback : Nat) (xs : List Nat) (h : xs ≠ []) :
    exactCutMin fallback xs ∈ xs := by
  cases xs with
  | nil => contradiction
  | cons x xs => exact foldCutMin_attained x xs

def encodeDigits (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + base * encodeDigits base ds

def decodeDigits (base : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, z => (z % base) :: decodeDigits base n (z / base)

theorem radix_head (b d x : Nat) (hd : d < b) :
    (d + b*x) % b = d := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

theorem radix_tail (b d x : Nat) (hd : d < b) :
    (d + b*x) / b = x := by
  rw [Nat.add_mul_div_left d x (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]

theorem digit_code_bound (base : Nat) (ds : List Nat)
    (valid : ∀ d ∈ ds, d < base) :
    encodeDigits base ds < base ^ ds.length := by
  induction ds with
  | nil => simp [encodeDigits]
  | cons d ds ih =>
    have hd := valid d (by simp)
    have ht := ih (fun x hx => valid x (List.mem_cons_of_mem d hx))
    simp only [encodeDigits, List.length_cons, Nat.pow_succ]
    have hm := Nat.mul_le_mul_left base (show encodeDigits base ds + 1 ≤ base^ds.length by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    rw [Nat.mul_comm (base^ds.length) base]
    omega

theorem decode_encoded_digits (base : Nat) (ds : List Nat)
    (valid : ∀ d ∈ ds, d < base) :
    decodeDigits base ds.length (encodeDigits base ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd := valid d (by simp)
    have ht := ih (fun x hx => valid x (List.mem_cons_of_mem d hx))
    simp only [List.length_cons, encodeDigits, decodeDigits]
    rw [radix_head _ _ _ hd, radix_tail _ _ _ hd, ht]

structure AssignmentJob where
  weight : Nat
  owner : Option Nat

def admissibleDigit (caps : List Nat) (job : AssignmentJob) (d : Nat) : Bool :=
  d == caps.length ||
    (decide (d < caps.length) && decide (job.weight ≤ caps.getD d 0) &&
      (job.owner.isNone || job.owner == some d))

def admissibleDigits (caps : List Nat) : List AssignmentJob → List Nat → Bool
  | [], [] => true
  | j :: js, d :: ds => admissibleDigit caps j d && admissibleDigits caps js ds
  | _, _ => false

def assignmentColumns (caps : List Nat) (jobs : List AssignmentJob) : List (List Nat) :=
  ((List.range ((caps.length+1)^jobs.length)).map
    (decodeDigits (caps.length+1) jobs.length)).filter (admissibleDigits caps jobs)

theorem assignment_column_complete (caps : List Nat) (jobs : List AssignmentJob)
    (digits : List Nat) (hl : digits.length = jobs.length)
    (hv : ∀ d ∈ digits, d < caps.length+1)
    (hf : admissibleDigits caps jobs digits = true) :
    digits ∈ assignmentColumns caps jobs := by
  unfold assignmentColumns
  apply List.mem_filter.mpr
  refine ⟨?_, hf⟩
  apply List.mem_map.mpr
  refine ⟨encodeDigits (caps.length+1) digits, ?_, ?_⟩
  · apply List.mem_range.mpr
    rw [← hl]
    exact digit_code_bound _ _ hv
  · rw [← hl]
    exact decode_encoded_digits _ _ hv

def omittedPenalty (T : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => (if d = T then 2 else 0) + omittedPenalty T ds

theorem omitted_penalty_exact (T : Nat) (digits : List Nat) :
    omittedPenalty T digits = 2 * digits.count T := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    by_cases e : d = T
    · subst d
      simp [omittedPenalty, ih, Nat.mul_add]
      omega
    · have ne : T ≠ d := Ne.symm e
      simp [omittedPenalty, ih, e, ne]

-- A binary-mask column is eligible precisely when it is a submask.
-- This enumerator equals the mathematical range/filter definition used
-- to build self.subsets in the Python constructor.
def submaskColumns (mask : Nat) : List Nat :=
  (List.range (mask+1)).filter (fun j => (j &&& mask) == j)

theorem submask_column_complete (mask j : Nat) (h : j ≤ mask)
    (hs : j &&& mask = j) : j ∈ submaskColumns mask := by
  simp [submaskColumns, hs, show j < mask+1 by omega]

-- Literal min-plus entries: merge computes the minimum over all
-- disjoint allocations represented by (mask xor submask, submask).
def mergeValue (top : Nat) (left right : Nat → Nat) (mask : Nat) : Nat :=
  exactCutMin top ((submaskColumns mask).map (fun j => left (mask ^^^ j) + right j))

theorem mergeValue_witness (top : Nat) (left right : Nat → Nat) (mask j : Nat)
    (h : j ≤ mask) (hs : j &&& mask = j) :
    mergeValue top left right mask ≤ left (mask ^^^ j) + right j := by
  apply exactCutMin_le_member
  exact List.mem_map.mpr ⟨j, submask_column_complete mask j h hs, rfl⟩

def subsetMinValue (top : Nat) (row : Nat → Nat) (mask : Nat) : Nat :=
  exactCutMin top ((submaskColumns mask).map row)

theorem subsetMinValue_witness (top : Nat) (row : Nat → Nat) (mask j : Nat)
    (h : j ≤ mask) (hs : j &&& mask = j) :
    subsetMinValue top row mask ≤ row j := by
  apply exactCutMin_le_member
  exact List.mem_map.mpr ⟨j, submask_column_complete mask j h hs, rfl⟩

-- A syntax tree for exactly the operations of the scalar cut DP.
-- Each edge row is indexed by its permitted terminal truck set.
-- Relax is subset_min; split is merge; repeat charges a chain of
-- equal profiles after contraction; leaf permits unused endpoints.
inductive CutDP where
  | leaf
  | addEdge : (Nat → Nat) → CutDP → CutDP
  | relax : CutDP → CutDP
  | split : CutDP → CutDP → CutDP
  | repeat : Nat → (Nat → Nat) → CutDP → CutDP

def evalCut (top : Nat) : CutDP → Nat → Nat
  | .leaf, _ => 0
  | .addEdge edge child, mask => edge mask + evalCut top child mask
  | .relax child, mask => subsetMinValue top (evalCut top child) mask
  | .split left right, mask => mergeValue top (evalCut top left) (evalCut top right) mask
  | .repeat n edge child, mask => n * edge mask + evalCut top child mask

-- A concrete assignment of endpoint masks at every DP operation.
-- Costs here are built from the actual row functions, not postulated
-- admissibility of a computed minimum.
inductive CutWitness : CutDP → Nat → Nat → Prop where
  | leaf (mask : Nat) : CutWitness .leaf mask 0
  | addEdge {edge child mask cost} :
      CutWitness child mask cost →
      CutWitness (.addEdge edge child) mask (edge mask + cost)
  | relax {child mask sub cost} :
      sub ≤ mask → sub &&& mask = sub →
      CutWitness child sub cost → CutWitness (.relax child) mask cost
  | split {left right mask sub lcost rcost} :
      sub ≤ mask → sub &&& mask = sub →
      CutWitness left (mask ^^^ sub) lcost → CutWitness right sub rcost →
      CutWitness (.split left right) mask (lcost + rcost)
  | repeat {n edge child mask cost} :
      CutWitness child mask cost →
      CutWitness (.repeat n edge child) mask (n*edge mask + cost)

theorem evalCut_le_witness (top : Nat) {tree mask cost}
    (witness : CutWitness tree mask cost) : evalCut top tree mask ≤ cost := by
  induction witness with
  | leaf mask => simp [evalCut]
  | addEdge hw ih =>
    simp only [evalCut]
    omega
  | relax hm hs hw ih =>
    exact Nat.le_trans (subsetMinValue_witness _ _ _ _ hm hs) ih
  | split hm hs hleft hright il ir =>
    apply Nat.le_trans (mergeValue_witness _ _ _ _ _ hm hs)
    omega
  | «repeat» hw ih =>
    simp only [evalCut]
    omega

-- This combines the actual enumerator with the concrete cut DP witness.
-- The extra cost of omitted jobs is not guessed: the preceding
-- residual_goal_budget theorem bounds it by non-goal unloads.
def assignmentCutBound (top : Nat) (caps : List Nat) (jobs : List AssignmentJob)
    (baseMove scale aboard mask : Nat) (tree : List Nat → CutDP) : Nat :=
  exactCutMin top ((assignmentColumns caps jobs).map (fun ds =>
    omittedPenalty caps.length ds +
      max baseMove ((evalCut top (tree ds) mask + scale - 1) / scale - aboard)))

theorem assignmentCutBound_le_witness (top : Nat) (caps : List Nat)
    (jobs : List AssignmentJob) (baseMove scale aboard mask : Nat)
    (tree : List Nat → CutDP) (ds : List Nat) (cost : Nat)
    (hl : ds.length = jobs.length) (hv : ∀ d ∈ ds, d < caps.length+1)
    (hf : admissibleDigits caps jobs ds = true)
    (witness : CutWitness (tree ds) mask cost) :
    assignmentCutBound top caps jobs baseMove scale aboard mask tree ≤
      omittedPenalty caps.length ds + max baseMove ((cost+scale-1)/scale-aboard) := by
  have member := assignment_column_complete caps jobs ds hl hv hf
  have hmin : assignmentCutBound top caps jobs baseMove scale aboard mask tree ≤
      omittedPenalty caps.length ds +
        max baseMove ((evalCut top (tree ds) mask + scale - 1) / scale - aboard) := by
    apply exactCutMin_le_member
    exact List.mem_map.mpr ⟨ds, member, rfl⟩
  have hcost := evalCut_le_witness top witness
  have hceil : (evalCut top (tree ds) mask + scale - 1) / scale ≤ (cost + scale - 1) / scale :=
    by
      by_cases hs : scale = 0
      · simp [hs]
      · have hp : 0 < scale := by omega
        have hb : cost + scale - 1 < ((cost + scale - 1) / scale + 1) * scale :=
          (Nat.div_lt_iff_lt_mul hp).mp (by omega)
        have ha : evalCut top (tree ds) mask + scale - 1 <
            ((cost + scale - 1) / scale + 1) * scale := by omega
        have h := (Nat.div_lt_iff_lt_mul hp).mpr ha
        omega
  have hm : (evalCut top (tree ds) mask + scale - 1) / scale - aboard ≤
      (cost + scale - 1) / scale - aboard := by omega
  have hmax : max baseMove ((evalCut top (tree ds) mask + scale - 1) / scale - aboard) ≤
      max baseMove ((cost + scale - 1) / scale - aboard) := by
    apply Nat.max_le.mpr
    exact ⟨Nat.le_max_left _ _, Nat.le_trans hm (Nat.le_max_right _ _)⟩
  omega

#print axioms digit_code_bound
#print axioms decode_encoded_digits
#print axioms assignment_column_complete
#print axioms omitted_penalty_exact
#print axioms mergeValue_witness
#print axioms subsetMinValue_witness
#print axioms evalCut_le_witness
#print axioms assignmentCutBound_le_witness
end IslandLogistics


namespace IslandLogistics

-- Capacity feasibility of each individually carried parcel follows from
-- the concrete LOAD precondition; this is preserved by all six actions.
def ValidParcelFit (w : World) (s : State) : Prop :=
  ∀ p, p < w.parcels → ∀ t, s.parcel p = .onTruck t →
    w.weight p ≤ w.capacity t

theorem step_parcel_fit (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) (v : ValidParcelFit w s) : ValidParcelFit w u := by
  cases st with
  | load p t a hp ht room valid =>
    intro q hq z hz
    change setAt s.parcel p (.onTruck t) q = .onTruck z at hz
    by_cases eq : q = p
    · subst q
      have he : t = z := by simpa [setAt] using hz
      subst z
      omega
    · exact v q hq z (by simpa [setAt, eq] using hz)
  | unload p t a hp ht valid =>
    intro q hq z hz
    change setAt s.parcel p (.ground a) q = .onTruck z at hz
    by_cases eq : q = p
    · subst q
      simp [setAt] at hz
    · exact v q hq z (by simpa [setAt, eq] using hz)
  | drive t a b ht hr valid => exact v
  | board t f a ht hf hr room valid => exact v
  | disembark t f ht valid => exact v
  | sail f b hr hne valid => exact v

theorem path_parcel_fit (w : World) {s u : State} {m h : Nat}
    (path : Path (Step w) s u m h) (v : ValidParcelFit w s) :
    ValidParcelFit w u := by
  induction path with
  | nil s => exact v
  | cons st rest ih => exact ih (step_parcel_fit w st v)

-- Paths in which the particular parcel has no non-goal unload.
inductive SafeJobPath (w : World) (p : Nat) : State → State → Nat → Nat → Prop where
  | nil (s : State) : SafeJobPath w p s s 0 0
  | cons {s t u : State} {a b m h : Nat} :
      Step w s t a b → extraOne w s t p = 0 →
      SafeJobPath w p t u m h → SafeJobPath w p s u (a+m) (b+h)

theorem safe_job_is_path (w : World) (p : Nat) {s u : State} {m h : Nat}
    (path : SafeJobPath w p s u m h) : Path (Step w) s u m h := by
  induction path with
  | nil s => exact Path.nil s
  | cons st safe rest ih => exact Path.cons st ih

theorem held_job_step (w : World) (p t : Nat)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (held : s.parcel p = .onTruck t) (safe : extraOne w s u p = 0) :
    u.parcel p = .onTruck t ∨
      (u.parcel p = .ground (w.goal p) ∧ s.truck t = .land (w.goal p) ∧ m = 0 ∧ h = 1) := by
  cases st with
  | drive q a b ht hr valid => exact Or.inl held
  | board q f a ht hf hr room valid => exact Or.inl held
  | disembark q f ht valid => exact Or.inl held
  | sail f b hr hne valid => exact Or.inl held
  | load q z a hp ht room valid =>
    by_cases eq : p = q
    · subst q
      rw [hp] at held
      cases held
    · left
      simpa [setAt, eq] using held
  | unload q z a hp ht valid =>
    by_cases eq : p = q
    · subst q
      have ht' : z = t := ParcelPosition.onTruck.inj (hp.symm.trans held)
      subst z
      have e : a = w.goal p := by
        by_cases e : a = w.goal p
        · exact e
        · simp [extraOne, setAt, hp, e] at safe
      subst a
      right
      exact ⟨by simp [setAt], ht, rfl, rfl⟩
    · left
      simpa [setAt, eq] using held

theorem ground_job_step (w : World) (p a : Nat)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (ground : s.parcel p = .ground a) :
    u.parcel p = .ground a ∨
      (∃ t, u.parcel p = .onTruck t ∧ s.truck t = .land a ∧
         t < w.trucks ∧ w.weight p ≤ w.capacity t ∧ m = 0 ∧ h = 1) := by
  cases st with
  | drive q b c ht hr valid => exact Or.inl ground
  | board q f b ht hf hr room valid => exact Or.inl ground
  | disembark q f ht valid => exact Or.inl ground
  | sail f b hr hne valid => exact Or.inl ground
  | load q t b hp ht room valid =>
    by_cases eq : p = q
    · subst q
      have he : b = a := ParcelPosition.ground.inj (hp.symm.trans ground)
      subst b
      right
      refine ⟨t, by simp [setAt], ht, valid.2.1, ?_, rfl, rfl⟩
      omega
    · left
      simpa [setAt, eq] using ground
  | unload q t b hp ht valid =>
    by_cases eq : p = q
    · subst q
      rw [hp] at ground
      cases ground
    · left
      simpa [setAt, eq] using ground

-- A literal contiguous segment of the concrete path, with the parcel
-- on the very same truck in every state, including both endpoints.
inductive CarrierSegment (w : World) (p t : Nat) :
    State → State → Nat → Nat → Prop where
  | nil (s : State) : s.parcel p = .onTruck t → CarrierSegment w p t s s 0 0
  | cons {s v u : State} {a b m h : Nat} :
      s.parcel p = .onTruck t → Step w s v a b →
      CarrierSegment w p t v u m h →
      CarrierSegment w p t s u (a+m) (b+h)

theorem carrier_segment_is_path (w : World) (p t : Nat)
    {s u : State} {m h : Nat} (seg : CarrierSegment w p t s u m h) :
    Path (Step w) s u m h := by
  induction seg with
  | nil s hs => exact Path.nil s
  | cons hs st rest ih => exact Path.cons st ih

-- If the parcel is already carried and has no non-goal unload, its first
-- delivery is performed by its actual initial carrier.  The witness is
-- extracted from the legal path rather than assumed as a DP property.
theorem held_first_delivery (w : World) (p t : Nat)
    {s u : State} {m h : Nat} (path : SafeJobPath w p s u m h)
    (held : s.parcel p = .onTruck t)
    (done : u.parcel p = .ground (w.goal p)) :
    ∃ x y cm ch rm rh,
      CarrierSegment w p t s x cm ch ∧
      Step w x y 0 1 ∧ x.truck t = .land (w.goal p) ∧
      y.parcel p = .ground (w.goal p) ∧
      Path (Step w) y u rm rh ∧
      m = cm + rm ∧ h = ch + 1 + rh := by
  induction path with
  | nil s =>
    rw [held] at done
    cases done
  | @cons s v u a b m h st safe rest ih =>
    rcases held_job_step w p t st held safe with keep | finish
    · obtain ⟨x,y,cm,ch,rm,rh,seg,un,atGoal,delivered,suffix,hm,hh⟩ := ih keep done
      exact ⟨x,y,a+cm,b+ch,rm,rh,CarrierSegment.cons held st seg,
        un,atGoal,delivered,suffix,by omega,by omega⟩
    · obtain ⟨delivered,atGoal,hm,hh⟩ := finish
      subst a
      subst b
      exact ⟨s,v,0,0,m,h,CarrierSegment.nil s held,st,atGoal,delivered,
        safe_job_is_path w p rest,by omega,by omega⟩

-- A ground, unfinished parcel must first be picked up at its original
-- source.  The corresponding truck satisfies the true LOAD capacity.
theorem ground_first_pickup (w : World) (p source : Nat)
    {s u : State} {m h : Nat} (path : SafeJobPath w p s u m h)
    (ground : s.parcel p = .ground source)
    (unfinished : source ≠ w.goal p)
    (done : u.parcel p = .ground (w.goal p)) :
    ∃ t x y pm ph rm rh,
      SafeJobPath w p s x pm ph ∧ Step w x y 0 1 ∧
      x.truck t = .land source ∧ y.parcel p = .onTruck t ∧
      t < w.trucks ∧ w.weight p ≤ w.capacity t ∧
      SafeJobPath w p y u rm rh ∧
      m = pm + rm ∧ h = ph + 1 + rh := by
  induction path with
  | nil s =>
    exact False.elim (unfinished (ParcelPosition.ground.inj (ground.symm.trans done)))
  | @cons s v u a b m h st safe rest ih =>
    rcases ground_job_step w p source st ground with keep | pick
    · obtain ⟨t,x,y,pm,ph,rm,rh,prepath,load,atSource,held,valid,fit,suffix,hm,hh⟩ := ih keep done
      exact ⟨t,x,y,a+pm,b+ph,rm,rh,SafeJobPath.cons st safe prepath,
        load,atSource,held,valid,fit,suffix,by omega,by omega⟩
    · obtain ⟨t,held,atSource,valid,fit,hm,hh⟩ := pick
      subst a
      subst b
      exact ⟨t,s,v,0,0,m,h,SafeJobPath.nil s,st,atSource,held,valid,fit,
        rest,by omega,by omega⟩

-- Flags are derived from each concrete edge, not from a guessed assignment.
inductive FlaggedPath (w : World) :
    State → State → Nat → Nat → Nat → (Nat → Bool) → Prop where
  | nil (s : State) : FlaggedPath w s s 0 0 0 (fun _ => false)
  | cons {s v u : State} {a b m h e : Nat} {flags : Nat → Bool} :
      Step w s v a b → FlaggedPath w v u m h e flags →
      FlaggedPath w s u (a+m) (b+h) (extraUnload w s v+e)
        (fun p => decide (extraOne w s v p ≠ 0) || flags p)

theorem flags_from_residual (w : World) {s u : State} {m h e : Nat}
    (path : ResidualPath w s u m h e) :
    ∃ flags, FlaggedPath w s u m h e flags := by
  induction path with
  | nil s => exact ⟨_,FlaggedPath.nil s⟩
  | cons st rest ih =>
    obtain ⟨flags,pr⟩ := ih
    exact ⟨_,FlaggedPath.cons st pr⟩

theorem flag_false_safe (w : World) (p : Nat)
    {s u : State} {m h e : Nat} {flags : Nat → Bool}
    (path : FlaggedPath w s u m h e flags) (safe : flags p = false) :
    SafeJobPath w p s u m h := by
  induction path with
  | nil s => exact SafeJobPath.nil s
  | @cons s v u a b m h e flags st rest ih =>
    have hs : extraOne w s v p = 0 ∧ flags p = false := by
      simpa [Bool.or_eq_false_iff] using safe
    exact SafeJobPath.cons st hs.1 (ih hs.2)

theorem extraOne_zero_or_two (w : World) (s u : State) (p : Nat) :
    extraOne w s u p = 0 ∨ extraOne w s u p = 2 := by
  cases hs : s.parcel p <;> cases hu : u.parcel p <;> simp [extraOne,hs,hu]
  exact Classical.em _

def flagCharge (w : World) (flags : Nat → Bool) : Nat :=
  sumN (fun p => if flags p then 2 else 0) w.parcels

theorem sumN_mono (f g : Nat → Nat) (n : Nat)
    (h : ∀ q, q < n → f q ≤ g q) : sumN f n ≤ sumN g n := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
    have h1 := h n (by omega)
    have h2 := ih (fun q hq => h q (by omega))
    simp only [sumN]
    omega

theorem flags_cost (w : World)
    {s u : State} {m h e : Nat} {flags : Nat → Bool}
    (path : FlaggedPath w s u m h e flags) : flagCharge w flags ≤ e := by
  induction path with
  | nil s => simp [flagCharge, sumN_zero]
  | @cons s v u a b m h e flags st rest ih =>
    have hsum : sumN (fun p => if (decide (extraOne w s v p ≠ 0) || flags p) then 2 else 0) w.parcels ≤
        sumN (fun p => extraOne w s v p + (if flags p then 2 else 0)) w.parcels := by
      apply sumN_mono
      intro q hq
      rcases extraOne_zero_or_two w s v q with hz | ht
      · simp [hz]
      · cases hf : flags q <;> simp [ht,hf]
    rw [sumN_add] at hsum
    unfold flagCharge at *
    unfold extraUnload
    dsimp only
    omega

#print axioms path_parcel_fit
#print axioms held_first_delivery
#print axioms ground_first_pickup
#print axioms flags_from_residual
#print axioms flag_false_safe
#print axioms flags_cost

end IslandLogistics


namespace IslandLogistics

def jobOwner (s : State) (p : Nat) : Option Nat :=
  match s.parcel p with
  | .ground _ => none
  | .onTruck t => some t

def concreteJob (w : World) (s : State) (p : Nat) : AssignmentJob :=
  ⟨w.weight p, jobOwner s p⟩

def selectedJobs (w : World) (s : State) (ids : List Nat) : List AssignmentJob :=
  ids.map (concreteJob w s)

-- A carrier witness records a genuine segment between pickup/current
-- carriage and first delivery. All paths are part of the full legal model.
def RealCarrier (w : World) (p t : Nat) (s u : State) : Prop :=
  ∃ v x y pm ph cm ch rm rh,
    Path (Step w) s v pm ph ∧
    v.parcel p = .onTruck t ∧
    CarrierSegment w p t v x cm ch ∧
    Step w x y 0 1 ∧ x.truck t = .land (w.goal p) ∧
    y.parcel p = .ground (w.goal p) ∧
    Path (Step w) y u rm rh

theorem path_append_step {S : Type} {edge : S → S → Nat → Nat → Prop}
    {s u v : S} {m h a b : Nat} (path : Path edge s u m h)
    (last : edge u v a b) : Path edge s v (m+a) (h+b) := by
  induction path with
  | nil s =>
    simpa using (Path.cons last (Path.nil v))
  | cons st rest ih =>
    simpa [Nat.add_assoc] using (Path.cons st (ih last))

theorem real_carrier_from_safe (w : World) (p : Nat)
    {s u : State} {m h : Nat} (path : SafeJobPath w p s u m h)
    (hp : p < w.parcels)
    (active : s.parcel p ≠ .ground (w.goal p))
    (done : Goal w u) (vp : ValidParcelCarriers w s)
    (vf : ValidParcelFit w s) :
    ∃ t, t < w.trucks ∧ w.weight p ≤ w.capacity t ∧
      (jobOwner s p = none ∨ jobOwner s p = some t) ∧
      RealCarrier w p t s u := by
  cases initial : s.parcel p with
  | ground a =>
    have ha : a ≠ w.goal p := by
      intro e
      exact active (by simpa [e] using initial)
    obtain ⟨t,x,y,pm,ph,rm,rh,pre,ld,atSource,held,valid,fit,suf,hm,hh⟩ :=
      ground_first_pickup w p a path initial ha (done p hp)
    obtain ⟨x2,y2,cm,ch,rm2,rh2,seg,un,atGoal,delivered,suffix,hm2,hh2⟩ :=
      held_first_delivery w p t suf held (done p hp)
    refine ⟨t,valid,fit,Or.inl (by simp [jobOwner,initial]),?_⟩
    exact ⟨y,x2,y2,pm+0,ph+1,cm,ch,rm2,rh2,
      path_append_step (safe_job_is_path w p pre) ld,held,seg,
      un,atGoal,delivered,suffix⟩
  | onTruck t =>
    obtain ⟨x,y,cm,ch,rm,rh,seg,un,atGoal,delivered,suffix,hm,hh⟩ :=
      held_first_delivery w p t path initial (done p hp)
    exact ⟨t,vp p hp t initial,vf p hp t initial,
      Or.inr (by simp [jobOwner,initial]),
      s,x,y,0,0,cm,ch,rm,rh,Path.nil s,initial,seg,un,atGoal,delivered,suffix⟩

-- DirectCutAssignments enumerates exactly one digit per active parcel.
-- A flagged parcel is assigned the omission digit; an unflagged parcel
-- receives the carrier extracted from its own concrete path.
inductive PathAssignment (w : World) (s u : State) (flags : Nat → Bool) :
    List Nat → List Nat → Prop where
  | nil : PathAssignment w s u flags [] []
  | omit {p ps ds} : flags p = true → PathAssignment w s u flags ps ds →
      PathAssignment w s u flags (p::ps) (w.trucks::ds)
  | keep {p ps ds t} :
      flags p = false → t < w.trucks → w.weight p ≤ w.capacity t →
      (jobOwner s p = none ∨ jobOwner s p = some t) →
      RealCarrier w p t s u → PathAssignment w s u flags ps ds →
      PathAssignment w s u flags (p::ps) (t::ds)

theorem path_assignment_exists (w : World) {s u : State} {m h e : Nat}
    {flags : Nat → Bool} (path : FlaggedPath w s u m h e flags)
    (done : Goal w u) (vp : ValidParcelCarriers w s)
    (vf : ValidParcelFit w s) (ids : List Nat)
    (valid : ∀ p ∈ ids, p < w.parcels ∧ s.parcel p ≠ .ground (w.goal p)) :
    ∃ ds, PathAssignment w s u flags ids ds := by
  induction ids with
  | nil => exact ⟨[],PathAssignment.nil⟩
  | cons p ps ih =>
    obtain ⟨hp,active⟩ := valid p (by simp)
    obtain ⟨ds,tail⟩ := ih (fun q hq => valid q (List.mem_cons_of_mem _ hq))
    cases flag : flags p with
    | false =>
      obtain ⟨t,ht,fit,owner,carrier⟩ :=
        real_carrier_from_safe w p (flag_false_safe w p path flag) hp active done vp vf
      exact ⟨t::ds,PathAssignment.keep flag ht fit owner carrier tail⟩
    | true => exact ⟨w.trucks::ds,PathAssignment.omit flag tail⟩

theorem path_assignment_valid (w : World) (s u : State) (flags : Nat → Bool)
    (caps : List Nat) (cl : caps.length = w.trucks)
    (cv : ∀ t, t < w.trucks → caps.getD t 0 = w.capacity t)
    {ids ds : List Nat} (pa : PathAssignment w s u flags ids ds) :
    ds.length = ids.length ∧
    (∀ d ∈ ds, d < caps.length+1) ∧
    admissibleDigits caps (selectedJobs w s ids) ds = true ∧
    omittedPenalty w.trucks ds =
      (ids.map (fun p => if flags p then 2 else 0)).sum := by
  induction pa with
  | nil => simp [selectedJobs,admissibleDigits,omittedPenalty]
  | @«omit» p ps ds flag tail ih =>
    obtain ⟨hl,hv,hf,he⟩ := ih
    constructor
    · simp [hl]
    constructor
    · intro d hd
      rw [List.mem_cons] at hd
      rcases hd with eq | h
      · subst d; omega
      · exact hv d h
    constructor
    · simpa [selectedJobs,admissibleDigits,admissibleDigit,cl] using hf
    · simp [omittedPenalty,flag,he]
  | @keep p ps ds t flag ht fit owner carrier tail ih =>
    obtain ⟨hl,hv,hf,he⟩ := ih
    constructor
    · simp [hl]
    constructor
    · intro d hd
      rw [List.mem_cons] at hd
      rcases hd with eq | h
      · subst d; omega
      · exact hv d h
    constructor
    · have digit : admissibleDigit caps (concreteJob w s p) t = true := by
        have hn : t ≠ caps.length := by omega
        have hlt : t < caps.length := by omega
        have hfit : w.weight p ≤ caps.getD t 0 := by
          rw [cv t ht]
          exact fit
        have hfit' : w.weight p ≤ caps[t] := by simpa [hlt] using hfit
        rcases owner with own | own
        · simp [admissibleDigit,concreteJob,hn,hlt,hfit,hfit',own]
        · simp [admissibleDigit,concreteJob,hn,hlt,hfit,hfit',own]
      change (admissibleDigit caps (concreteJob w s p) t &&
        admissibleDigits caps (selectedJobs w s ps) ds) = true
      simp [digit,hf]
    · have hn : t ≠ w.trucks := by omega
      simp [omittedPenalty,flag,he,hn]

-- The list of actually active parcels is a filter of range. Its charged
-- flags cannot exceed the total concrete residual budget.
def activeParcels (w : World) (s : State) : List Nat :=
  (List.range w.parcels).filter (fun p => s.parcel p != .ground (w.goal p))

theorem natListSum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]

theorem sum_range_eq_sumN (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = sumN f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.map_append,natListSum_append]
    simp [sumN,ih]

theorem filtered_weight_le (xs : List Nat) (keep : Nat → Bool) (f : Nat → Nat) :
    ((xs.filter keep).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : keep x <;> simp [h] <;> omega

theorem active_flags_cost (w : World) (s : State) (flags : Nat → Bool) :
    ((activeParcels w s).map (fun p => if flags p then 2 else 0)).sum ≤
      flagCharge w flags := by
  have h := filtered_weight_le (List.range w.parcels)
    (fun p => s.parcel p != .ground (w.goal p)) (fun p => if flags p then 2 else 0)
  rw [sum_range_eq_sumN] at h
  exact h

-- The full assignment enumeration is now linked to the actual legal path
-- and to its real handling cost. It does not hypothesize that a valid
-- column exists; this theorem constructs and proves one exists.
theorem legal_path_assignment_column (w : World) {s u : State} {m h e : Nat}
    (path : ResidualPath w s u m h e) (done : Goal w u)
    (vp : ValidParcelCarriers w s) (vf : ValidParcelFit w s)
    (caps : List Nat) (cl : caps.length = w.trucks)
    (cv : ∀ t, t < w.trucks → caps.getD t 0 = w.capacity t) :
    ∃ ds flags,
      FlaggedPath w s u m h e flags ∧
      PathAssignment w s u flags (activeParcels w s) ds ∧
      ds ∈ assignmentColumns caps (selectedJobs w s (activeParcels w s)) ∧
      handling w s + omittedPenalty caps.length ds ≤ h := by
  obtain ⟨flags,flagpath⟩ := flags_from_residual w path
  have valid : ∀ p ∈ activeParcels w s,
      p < w.parcels ∧ s.parcel p ≠ .ground (w.goal p) := by
    intro p hp
    simpa [activeParcels] using hp
  obtain ⟨ds,pa⟩ := path_assignment_exists w flagpath done vp vf _ valid
  obtain ⟨hl,hv,hf,he⟩ := path_assignment_valid w s u flags caps cl cv pa
  have col := assignment_column_complete caps (selectedJobs w s (activeParcels w s)) ds
    (by simpa [selectedJobs] using hl) hv hf
  have hc := active_flags_cost w s flags
  have hb := flags_cost w flagpath
  have hh := residual_goal_budget w path done
  refine ⟨ds,flags,flagpath,pa,col,?_⟩
  rw [cl,he]
  omega

#print axioms real_carrier_from_safe
#print axioms path_assignment_exists
#print axioms path_assignment_valid
#print axioms legal_path_assignment_column
end IslandLogistics


namespace IslandLogistics
/- Exact lexicographic bin-packing recurrence used in ex1.py:1293ff,
   _bin and DirectCutAssignments.bins.
   The subset is represented by its list of remaining item weights.
   Each remove-one choice is the list analogue of clearing one set bit.
   This proof concerns the actual recurrence, not a fractional surrogate. -/
abbrev BinState := Nat × Nat

def binLE (a b : BinState) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

theorem binLE_refl (a : BinState) : binLE a a := by
  unfold binLE
  omega

theorem binLE_trans {a b c : BinState} (ab : binLE a b) (bc : binLE b c) :
    binLE a c := by
  unfold binLE at *
  omega

theorem binLE_count {a b : BinState} (h : binLE a b) : a.1 ≤ b.1 := by
  unfold binLE at h
  omega

def binNext (C : Nat) (a : BinState) (w : Nat) : BinState :=
  if a.1 ≠ 0 ∧ a.2 + w ≤ C then (a.1,a.2+w) else (a.1+1,w)

theorem binNext_mono (C w : Nat) {a b : BinState} (ab : binLE a b) :
    binLE (binNext C a w) (binNext C b w) := by
  unfold binNext
  split <;> split <;> unfold binLE at * <;> simp_all <;> omega

theorem binNext_fresh (C w : Nat) (a : BinState) :
    binLE (binNext C a w) (a.1+1,w) := by
  unfold binNext
  split <;> unfold binLE <;> simp <;> omega

def binMin (a b : BinState) : BinState :=
  if a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) then a else b

theorem binMin_left (a b : BinState) : binLE (binMin a b) a := by
  unfold binMin binLE
  split <;> omega

theorem binMin_right (a b : BinState) : binLE (binMin a b) b := by
  unfold binMin binLE
  split <;> omega

def binFold (seed : BinState) : List BinState → BinState
  | [] => seed
  | a::as => binFold (binMin seed a) as

theorem binFold_le_seed (seed : BinState) (xs : List BinState) :
    binLE (binFold seed xs) seed := by
  induction xs generalizing seed with
  | nil => exact binLE_refl _
  | cons a as ih => exact binLE_trans (ih _) (binMin_left _ _)

theorem binFold_le_member (seed : BinState) (xs : List BinState) (x : BinState)
    (h : x ∈ xs) : binLE (binFold seed xs) x := by
  induction xs generalizing seed with
  | nil => simp at h
  | cons a as ih =>
    rw [List.mem_cons] at h
    rcases h with eq | rest
    · subst x
      exact binLE_trans (binFold_le_seed (binMin seed a) as) (binMin_right seed a)
    · exact ih _ rest

inductive RemoveWeight (w : Nat) : List Nat → List Nat → Prop where
  | head (xs : List Nat) : RemoveWeight w (w::xs) xs
  | tail {xs ys : List Nat} (v : Nat) :
      RemoveWeight w xs ys → RemoveWeight w (v::xs) (v::ys)

def lastChoices : List Nat → List (Nat × List Nat)
  | [] => []
  | w::xs => (w,xs) :: (lastChoices xs).map (fun (v,ys) => (v,w::ys))

theorem removeWeight_choice {w : Nat} {xs ys : List Nat}
    (h : RemoveWeight w xs ys) : (w,ys) ∈ lastChoices xs := by
  induction h with
  | head xs => simp [lastChoices]
  | @tail xs ys v h ih =>
    simp only [lastChoices,List.mem_cons]
    right
    exact List.mem_map.mpr ⟨(w,ys),ih,rfl⟩

theorem removeWeight_length {w : Nat} {xs ys : List Nat}
    (h : RemoveWeight w xs ys) : xs.length = ys.length+1 := by
  induction h with
  | head xs => simp
  | tail v h ih => simp [ih]

theorem removeWeight_last (xs : List Nat) (w : Nat) :
    RemoveWeight w (xs++[w]) xs := by
  induction xs with
  | nil => exact RemoveWeight.head []
  | cons x xs ih => exact RemoveWeight.tail x ih

-- The seed matches the finite (P+1,0) sentinel of the Python code.
-- It can be arbitrary for the witness inequality; no bound on h is built in.
def binDP (C : Nat) (seed : BinState) : Nat → List Nat → BinState
  | _, [] => (0,0)
  | 0, _::_ => seed
  | k+1, w::xs =>
    binFold seed (((lastChoices (w::xs)).filter (fun x => x.1 ≤ C)).map
      (fun x => binNext C (binDP C seed k x.2) x.1))

-- A packing witness has any item order and may start a new bin even
-- when the previous bin has remaining capacity. Reuse always respects
-- capacity. Empty bins need not be represented.
inductive BinWitness (C : Nat) : List Nat → BinState → Prop where
  | empty : BinWitness C [] (0,0)
  | fresh {xs ys : List Nat} {w : Nat} {st : BinState} :
      RemoveWeight w xs ys → w ≤ C → BinWitness C ys st →
      BinWitness C xs (st.1+1,w)
  | reuse {xs ys : List Nat} {w : Nat} {st : BinState} :
      RemoveWeight w xs ys → w ≤ C → st.1 ≠ 0 → st.2+w ≤ C →
      BinWitness C ys st → BinWitness C xs (st.1,st.2+w)

theorem binDP_le_next (C : Nat) (seed : BinState) (k : Nat)
    {xs ys : List Nat} {w : Nat}
    (rem : RemoveWeight w xs ys) (fit : w ≤ C) :
    binLE (binDP C seed (k+1) xs) (binNext C (binDP C seed k ys) w) := by
  have mem := removeWeight_choice rem
  cases xs with
  | nil => cases rem
  | cons a as =>
    rw [binDP]
    apply binFold_le_member
    apply List.mem_map.mpr
    refine ⟨(w,ys),?_,rfl⟩
    simp [mem,fit]

theorem binDP_le_witness (C : Nat) (seed : BinState)
    {xs : List Nat} {st : BinState} (pw : BinWitness C xs st)
    (fuel : Nat) (enough : xs.length ≤ fuel) :
    binLE (binDP C seed fuel xs) st := by
  induction pw generalizing fuel with
  | empty => simp [binDP,binLE]
  | @fresh xs ys w st rem fit rest ih =>
    cases fuel with
    | zero =>
      have h := removeWeight_length rem
      omega
    | succ k =>
      have h := removeWeight_length rem
      have pref := ih k (by omega)
      exact binLE_trans (binDP_le_next C seed k rem fit)
        (binLE_trans (binNext_mono C w pref) (binNext_fresh C w st))
  | @reuse xs ys w st rem fit nonzero room rest ih =>
    cases fuel with
    | zero =>
      have h := removeWeight_length rem
      omega
    | succ k =>
      have h := removeWeight_length rem
      have pref := ih k (by omega)
      have hn := binNext_mono C w pref
      have he : binNext C st w = (st.1,st.2+w) := by
        simp [binNext,nonzero,room]
      rw [he] at hn
      exact binLE_trans (binDP_le_next C seed k rem fit) hn

theorem binDP_count_le_witness (C : Nat) (seed : BinState)
    {xs : List Nat} {st : BinState} (pw : BinWitness C xs st) :
    (binDP C seed xs.length xs).1 ≤ st.1 :=
  binLE_count (binDP_le_witness C seed pw xs.length (by omega))

-- The following construction converts each nonempty capacity-feasible
-- cargo group into one bin. The list may be ordered by the actual
-- crossing events; the recurrence permits any removal order.
theorem binWitness_reuse_list (C : Nat)
    (xs more : List Nat) (b l : Nat)
    (h : BinWitness C xs (b,l)) (hb : b ≠ 0) (room : l+more.sum ≤ C) :
    BinWitness C (xs++more) (b,l+more.sum) := by
  induction more generalizing xs l with
  | nil => simpa using h
  | cons w ws ih =>
    have hsum : (w::ws).sum = w+ws.sum := by simp
    have hw : w ≤ C := by rw [hsum] at room; omega
    have hl : l+w ≤ C := by rw [hsum] at room; omega
    have next : BinWitness C (xs++[w]) (b,l+w) :=
      BinWitness.reuse (removeWeight_last xs w) hw hb hl h
    have hn := ih (xs++[w]) (l+w) next (by rw [hsum] at room; omega)
    simpa [List.append_assoc,Nat.add_assoc,hsum] using hn

theorem binWitness_add_group (C : Nat) (xs group : List Nat)
    (st : BinState) (h : BinWitness C xs st)
    (nonempty : group ≠ []) (fit : group.sum ≤ C) :
    BinWitness C (xs++group) (st.1+1,group.sum) := by
  cases group with
  | nil => contradiction
  | cons w ws =>
    have hw : w ≤ C := by simp at fit; omega
    have next : BinWitness C (xs++[w]) (st.1+1,w) :=
      BinWitness.fresh (removeWeight_last xs w) hw h
    have hn := binWitness_reuse_list C (xs++[w]) ws (st.1+1) w next (by omega)
      (by simpa using fit)
    simpa [List.append_assoc] using hn

-- The exact recursive DP never returns more bins than any concrete
-- packing witness, including distinct equal-weight parcels.
#print axioms binNext_mono
#print axioms removeWeight_choice
#print axioms binDP_le_witness
#print axioms binDP_count_le_witness
#print axioms binWitness_add_group
end IslandLogistics


namespace IslandLogistics
theorem removeWeight_of_mem {w : Nat} {xs : List Nat} (hm : w ∈ xs) :
    ∃ ys, RemoveWeight w xs ys := by
  induction xs with
  | nil => simp at hm
  | cons v vs ih =>
    rw [List.mem_cons] at hm
    rcases hm with eq | tail
    · subst v
      exact ⟨vs,RemoveWeight.head vs⟩
    · obtain ⟨ys,h⟩ := ih tail
      exact ⟨v::ys,RemoveWeight.tail v h⟩

theorem removeWeight_perm {w : Nat} {xs ys : List Nat}
    (h : RemoveWeight w xs ys) : List.Perm (w::ys) xs := by
  induction h with
  | head xs => exact List.Perm.refl _
  | @tail xs ys v h ih =>
    exact (List.Perm.swap v w ys).trans (List.Perm.cons v ih)

theorem binWitness_perm (C : Nat) {xs : List Nat} {st : BinState}
    (h : BinWitness C xs st) (zs : List Nat) (p : List.Perm zs xs) :
    BinWitness C zs st := by
  induction h generalizing zs with
  | empty =>
    have hlen := p.length_eq
    cases zs with
    | nil => exact BinWitness.empty
    | cons z zs => simp at hlen
  | @fresh xs ys w st rem fit rest ih =>
    have pm := (removeWeight_perm rem).trans p.symm
    have mem : w ∈ zs := pm.mem_iff.mp (by simp)
    obtain ⟨rs,r⟩ := removeWeight_of_mem mem
    have pc : List.Perm (w::rs) (w::ys) :=
      (removeWeight_perm r).trans pm.symm
    exact BinWitness.fresh r fit (ih rs pc.cons_inv)
  | @reuse xs ys w st rem fit nonzero room rest ih =>
    have pm := (removeWeight_perm rem).trans p.symm
    have mem : w ∈ zs := pm.mem_iff.mp (by simp)
    obtain ⟨rs,r⟩ := removeWeight_of_mem mem
    have pc : List.Perm (w::rs) (w::ys) :=
      (removeWeight_perm r).trans pm.symm
    exact BinWitness.reuse r fit nonzero room (ih rs pc.cons_inv)

theorem binWitness_groups (C : Nat) (groups : List (List Nat))
    (xs : List Nat) (st : BinState) (start : BinWitness C xs st)
    (feasible : ∀ g ∈ groups, g.sum ≤ C) :
    ∃ endState, BinWitness C (xs++groups.flatten) endState ∧
      endState.1 ≤ st.1+groups.length := by
  induction groups generalizing xs st with
  | nil => exact ⟨st,by simpa using start,by simp⟩
  | cons g gs ih =>
    have fit := feasible g (by simp)
    have hf : ∀ q ∈ gs, q.sum ≤ C := fun q hq => feasible q (List.mem_cons_of_mem _ hq)
    by_cases empty : g = []
    · subst g
      obtain ⟨e,hw,hn⟩ := ih xs st start hf
      exact ⟨e,by simpa using hw,by simp; omega⟩
    · have step := binWitness_add_group C xs g st start empty fit
      obtain ⟨e,hw,hn⟩ := ih (xs++g) (st.1+1,g.sum) step hf
      refine ⟨e,?_,?_⟩
      · simpa [List.flatten,List.append_assoc] using hw
      · simp
        omega

-- Every grouping of the actual multiset of parcel weights into
-- capacity-feasible truck crossings is a witness. No optimal grouping
-- or enumeration-completeness hypothesis is needed.
theorem binDP_le_feasible_groups (C : Nat) (seed : BinState)
    (xs : List Nat) (groups : List (List Nat))
    (perm : List.Perm xs groups.flatten)
    (feasible : ∀ g ∈ groups, g.sum ≤ C) :
    (binDP C seed xs.length xs).1 ≤ groups.length := by
  obtain ⟨st,hw,hb⟩ := binWitness_groups C groups [] (0,0) BinWitness.empty feasible
  have hflat : BinWitness C groups.flatten st := by simpa using hw
  have h := binDP_count_le_witness C seed (binWitness_perm C hflat xs perm)
  simp at hb
  omega

#print axioms removeWeight_perm
#print axioms binWitness_perm
#print axioms binWitness_groups
#print axioms binDP_le_feasible_groups
end IslandLogistics


namespace IslandLogistics

-- The real LOAD/UNLOAD rules preserve the *total* capacity invariant,
-- not merely each individual package's ability to fit the carrier.
def ValidTruckLoad (w : World) (s : State) : Prop :=
  ∀ t, t < w.trucks → load w s t ≤ w.capacity t

theorem sumN_one_delta (f g : Nat → Nat) (p n k : Nat)
    (hp : p < n) (heq : ∀ q, q ≠ p → f q = g q)
    (hdelta : f p = g p + k) :
    sumN f n = sumN g n + k := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases e : n = p
    · subst n
      have h := sumN_congr f g p (fun q hq => heq q (by omega))
      simp only [sumN]
      omega
    · have hh : p < n := by omega
      have h := ih hh
      have eq := heq n e
      simp only [sumN]
      omega

theorem load_after_load (w : World) (s : State) (p t a : Nat)
    (hp : p < w.parcels) (hg : s.parcel p = .ground a) :
    load w {s with parcel := setAt s.parcel p (.onTruck t)} t =
      load w s t + w.weight p := by
  unfold load
  apply sumN_one_delta _ _ p _ _ hp
  · intro q hq
    simp [setAt,hq]
  · simp [setAt,hg]

theorem load_after_unload (w : World) (s : State) (p t a : Nat)
    (hp : p < w.parcels) (hc : s.parcel p = .onTruck t) :
    load w s t =
      load w {s with parcel := setAt s.parcel p (.ground a)} t + w.weight p := by
  unfold load
  apply sumN_one_delta _ _ p _ _ hp
  · intro q hq
    simp [setAt,hq]
  · simp [setAt,hc]

theorem step_valid_load (w : World) {s u : State} {m h : Nat}
    (st : Step w s u m h) (v : ValidTruckLoad w s) :
    ValidTruckLoad w u := by
  cases st with
  | load p t a hp ht room valid =>
    intro q hq
    by_cases e : q = t
    · subst q
      rw [load_after_load w s p t a valid.1 hp]
      exact room
    · have eq : load w {s with parcel := setAt s.parcel p (.onTruck t)} q = load w s q := by
        unfold load
        apply sumN_congr
        intro x hx
        by_cases ex : x = p
        · subst x
          simp [setAt,hp,Ne.symm e]
        · simp [setAt,ex]
      rw [eq]
      exact v q hq
  | unload p t a hp ht valid =>
    intro q hq
    by_cases e : q = t
    · subst q
      have hh := load_after_unload w s p t a valid.1 hp
      have hv := v t hq
      omega
    · have eq : load w {s with parcel := setAt s.parcel p (.ground a)} q = load w s q := by
        unfold load
        apply sumN_congr
        intro x hx
        by_cases ex : x = p
        · subst x
          simp [setAt,hp,Ne.symm e]
        · simp [setAt,ex]
      rw [eq]
      exact v q hq
  | drive t a b ht hr valid => exact v
  | board t f a ht hf hr room valid => exact v
  | disembark t f ht valid => exact v
  | sail f b hr hne valid => exact v

theorem path_valid_load (w : World) {s u : State} {m h : Nat}
    (path : Path (Step w) s u m h) (v : ValidTruckLoad w s) :
    ValidTruckLoad w u := by
  induction path with
  | nil s => exact v
  | cons st rest ih => exact ih (step_valid_load w st v)

-- A parcel's physical side can change only while it is carried by
-- the same truck at both endpoints of a legal primitive transition.
theorem parcel_side_change_carrier (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (vp : ValidParcelCarriers w s) (p : Nat) (hp : p < w.parcels)
    (diff : side (physicalParcel s p) ≠ side (physicalParcel u p)) :
    ∃ t, t < w.trucks ∧ s.parcel p = .onTruck t ∧ u.parcel p = .onTruck t := by
  cases st with
  | drive t a b ht hr valid =>
    cases eq : s.parcel p with
    | ground x => simp [physicalParcel,eq] at diff
    | onTruck q => exact ⟨q,vp p hp q eq,rfl,rfl⟩
  | board t f a ht hf hr room valid =>
    cases eq : s.parcel p with
    | ground x => simp [physicalParcel,eq] at diff
    | onTruck q => exact ⟨q,vp p hp q eq,rfl,rfl⟩
  | disembark t f ht valid =>
    cases eq : s.parcel p with
    | ground x => simp [physicalParcel,eq] at diff
    | onTruck q => exact ⟨q,vp p hp q eq,rfl,rfl⟩
  | sail f b hr hne valid =>
    cases eq : s.parcel p with
    | ground x => simp [physicalParcel,eq] at diff
    | onTruck q => exact ⟨q,vp p hp q eq,rfl,rfl⟩
  | load q t a hq ht room valid =>
    by_cases eq : p = q
    · subst q
      simp [physicalParcel,physicalTruck,setAt,hq,ht] at diff
    · simp [physicalParcel,setAt,eq,physicalTruck] at diff
  | unload q t a hq ht valid =>
    by_cases eq : p = q
    · subst q
      simp [physicalParcel,physicalTruck,setAt,hq,ht] at diff
    · simp [physicalParcel,setAt,eq,physicalTruck] at diff

def enteringTrucks (w : World) (side : Nat → Bool) (s u : State) : List Nat :=
  (List.range w.trucks).filter (fun t =>
    !side (physicalTruck s t) && side (physicalTruck u t))

def sourceOwner (s : State) (p : Nat) : Nat :=
  match s.parcel p with
  | .ground _ => 0
  | .onTruck t => t

theorem entering_parcel_owner (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (vp : ValidParcelCarriers w s) (p : Nat) (hp : p < w.parcels)
    (outside : side (physicalParcel s p) = false)
    (inside : side (physicalParcel u p) = true) :
    sourceOwner s p ∈ enteringTrucks w side s u ∧
      s.parcel p = .onTruck (sourceOwner s p) := by
  have diff : side (physicalParcel s p) ≠ side (physicalParcel u p) := by
    simp [outside,inside]
  obtain ⟨t,valid,hs,hu⟩ := parcel_side_change_carrier w side st vp p hp diff
  have ho : side (physicalTruck s t) = false := by simpa [physicalParcel,hs] using outside
  have hi : side (physicalTruck u t) = true := by simpa [physicalParcel,hu] using inside
  exact ⟨by simp [sourceOwner,hs,enteringTrucks,valid,ho,hi],by simp [sourceOwner,hs]⟩

#print axioms step_valid_load
#print axioms path_valid_load
#print axioms parcel_side_change_carrier
#print axioms entering_parcel_owner

end IslandLogistics


namespace IslandLogistics

theorem perm_move_front {α : Type} (x : α) (as bs : List α) :
    List.Perm (x::(as++bs)) (as++(x::bs)) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    exact (List.Perm.swap a x (as++bs)).trans (List.Perm.cons a ih)

theorem filter_partition_perm {α : Type} (xs : List α) (p : α → Bool) :
    List.Perm xs (xs.filter p ++ xs.filter (fun x => !p x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : p x with
    | true => simpa [h] using (List.Perm.cons x ih)
    | false =>
      have hh := (List.Perm.cons x ih).trans
        (perm_move_front x (xs.filter p) (xs.filter (fun x => !p x)))
      simpa [h] using hh

theorem filter_twice {α : Type} (xs : List α) (p q : α → Bool) :
    (xs.filter p).filter q = xs.filter (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [hp,hq,ih]

theorem filter_empty_of_false {α : Type} (xs : List α) (p : α → Bool)
    (h : ∀ x ∈ xs, p x = false) : xs.filter p = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [hx,hxs]

def selectedWeights (w : World) (sel : Nat → Bool) : List Nat :=
  ((List.range w.parcels).filter sel).map w.weight

theorem selectedWeight_split (w : World) (sel pred : Nat → Bool) :
    List.Perm (selectedWeights w sel)
      (selectedWeights w (fun p => sel p && pred p) ++
       selectedWeights w (fun p => sel p && !pred p)) := by
  have h := (filter_partition_perm ((List.range w.parcels).filter sel) pred).map w.weight
  simpa only [List.map_append,filter_twice,selectedWeights] using h

theorem selectedWeight_empty (w : World) (sel : Nat → Bool)
    (h : ∀ p, p < w.parcels → sel p = false) :
    selectedWeights w sel = [] := by
  unfold selectedWeights
  rw [filter_empty_of_false _ _ (fun p hp => h p (List.mem_range.mp hp))]
  rfl

theorem filter_map_sum_nat {α : Type} (xs : List α) (sel : α → Bool)
    (f : α → Nat) :
    ((xs.filter sel).map f).sum =
      (xs.map (fun x => if sel x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : sel x <;> simp [h,ih]

theorem selectedWeights_sum (w : World) (sel : Nat → Bool) :
    (selectedWeights w sel).sum =
      sumN (fun p => if sel p then w.weight p else 0) w.parcels := by
  unfold selectedWeights
  rw [filter_map_sum_nat,sum_range_eq_sumN]

theorem selectedWeight_carrier_le (w : World) (s : State) (t : Nat)
    (sel : Nat → Bool)
    (h : ∀ p, p < w.parcels → sel p = true → s.parcel p = .onTruck t) :
    (selectedWeights w sel).sum ≤ load w s t := by
  rw [selectedWeights_sum]
  unfold load
  apply sumN_mono
  intro p hp
  cases he : sel p with
  | false => simp [he]
  | true => simp [he,h p hp he]

-- Mathematical witness: one bucket per real crossing truck. Empty
-- buckets are permitted, since they still correspond to real crossings.
def groupWeights (w : World) (key : Nat → Nat) :
    List Nat → (Nat → Bool) → List (List Nat)
  | [], _ => []
  | t::ts, sel =>
    selectedWeights w (fun p => sel p && (key p == t)) ::
    groupWeights w key ts (fun p => sel p && !(key p == t))

theorem groupWeights_length (w : World) (key : Nat → Nat)
    (ts : List Nat) (sel : Nat → Bool) :
    (groupWeights w key ts sel).length = ts.length := by
  induction ts generalizing sel with
  | nil => rfl
  | cons t ts ih => simp [groupWeights,ih]

theorem groupWeights_perm (w : World) (key : Nat → Nat)
    (ts : List Nat) (sel : Nat → Bool)
    (cover : ∀ p, p < w.parcels → sel p = true → key p ∈ ts) :
    List.Perm (selectedWeights w sel) (groupWeights w key ts sel).flatten := by
  induction ts generalizing sel with
  | nil =>
    have h : ∀ p, p < w.parcels → sel p = false := by
      intro p hp
      cases he : sel p with
      | false => rfl
      | true => have hh := cover p hp he; simp at hh
    simp [groupWeights,selectedWeight_empty w sel h]
  | cons t ts ih =>
    let pred : Nat → Bool := fun p => key p == t
    have cv : ∀ p, p < w.parcels →
        (sel p && !pred p) = true → key p ∈ ts := by
      intro p hp hh
      have h : sel p = true ∧ key p ≠ t := by simpa [pred] using hh
      have hm := cover p hp h.1
      rcases List.mem_cons.mp hm with eq | mem
      · exact False.elim (h.2 eq)
      · exact mem
    have hp := selectedWeight_split w sel pred
    have ht := ih (fun p => sel p && !pred p) cv
    have he := hp.trans (List.Perm.append (List.Perm.refl _) ht)
    simpa [groupWeights,pred] using he

theorem groupWeights_fit (w : World) (s : State) (C : Nat)
    (key : Nat → Nat) (ts : List Nat) (sel : Nat → Bool)
    (vl : ValidTruckLoad w s)
    (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (valid : ∀ t ∈ ts, t < w.trucks)
    (owner : ∀ p, p < w.parcels → sel p = true →
      s.parcel p = .onTruck (key p)) :
    ∀ g ∈ groupWeights w key ts sel, g.sum ≤ C := by
  induction ts generalizing sel with
  | nil => simp [groupWeights]
  | cons t ts ih =>
    intro g hg
    simp only [groupWeights,List.mem_cons] at hg
    rcases hg with eq | hg
    · subst g
      have h := selectedWeight_carrier_le w s t
        (fun p => sel p && (key p == t)) (by
          intro p hp he
          have he' : sel p = true ∧ key p = t := by simpa using he
          rw [← he'.2]
          exact owner p hp he'.1)
      have ht := valid t (by simp)
      exact Nat.le_trans h (Nat.le_trans (vl t ht) (cap t ht))
    · apply ih (fun p => sel p && !(key p == t))
        (fun t ht => valid t (List.mem_cons_of_mem _ ht)) ?_ g hg
      intro p hp h
      have hs : sel p = true := by
        cases hs : sel p <;> simp_all
      exact owner p hp hs

-- For an actual legal primitive, all selected parcels which cross a
-- cut inward are partitioned into the trucks that really cross inward.
theorem legal_step_crossing_groups (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (sel : Nat → Bool)
    (moves : ∀ p, p < w.parcels → sel p = true →
      side (physicalParcel s p) = false ∧ side (physicalParcel u p) = true) :
    ∃ groups : List (List Nat),
      List.Perm (selectedWeights w sel) groups.flatten ∧
      (∀ g ∈ groups, g.sum ≤ C) ∧
      groups.length = (enteringTrucks w side s u).length := by
  have owns : ∀ p, p < w.parcels → sel p = true →
      sourceOwner s p ∈ enteringTrucks w side s u ∧
      s.parcel p = .onTruck (sourceOwner s p) := by
    intro p hp hs
    exact entering_parcel_owner w side st vp p hp (moves p hp hs).1 (moves p hp hs).2
  refine ⟨groupWeights w (sourceOwner s) (enteringTrucks w side s u) sel, ?_, ?_, ?_⟩
  · exact groupWeights_perm w _ _ _ (fun p hp hs => (owns p hp hs).1)
  · exact groupWeights_fit w s C _ _ _ vl cap
      (fun t ht => List.mem_range.mp (List.mem_filter.mp ht).1)
      (fun p hp hs => (owns p hp hs).2)
  · exact groupWeights_length w _ _ _

#print axioms groupWeights_perm
#print axioms selectedWeight_carrier_le
#print axioms legal_step_crossing_groups
end IslandLogistics


namespace IslandLogistics

def leavingTrucks (w : World) (side : Nat → Bool) (s u : State) : List Nat :=
  enteringTrucks w (fun v => !side v) s u

-- Counts are derived from the real endpoints of each primitive step.
-- One SAIL may contribute several truck crossings; no assumption that
-- a primitive can move at most one truck is used.
inductive FluxPath (w : World) (side : Nat → Bool) :
    State → State → Nat → Nat → Nat → Nat → Prop where
  | nil (s : State) : FluxPath w side s s 0 0 0 0
  | cons {s v u : State} {a b m h i o : Nat} :
      Step w s v a b → FluxPath w side v u m h i o →
      FluxPath w side s u (a+m) (b+h)
        ((enteringTrucks w side s v).length+i)
        ((leavingTrucks w side s v).length+o)

theorem flux_from_path (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} (path : Path (Step w) s u m h) :
    ∃ i o, FluxPath w side s u m h i o := by
  induction path with
  | nil s => exact ⟨0,0,FluxPath.nil s⟩
  | cons st tail ih =>
    obtain ⟨i,o,p⟩ := ih
    exact ⟨_,_,FluxPath.cons st p⟩

theorem flatten_append_nat (xs ys : List (List Nat)) :
    (xs++ys).flatten = xs.flatten ++ ys.flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatten,ih,List.append_assoc]

-- Extract a feasible group per actual inward truck crossing. Each
-- selected parcel is assigned to its FIRST inward crossing along the
-- concrete path. This includes arbitrary transfers and ferry occupancy.
theorem flux_path_groups (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (sel : Nat → Bool)
    (needs : ∀ p, p < w.parcels → sel p = true →
      side (physicalParcel s p) = false ∧ side (w.goal p) = true) :
    ∃ groups : List (List Nat),
      List.Perm (selectedWeights w sel) groups.flatten ∧
      (∀ g ∈ groups, g.sum ≤ C) ∧ groups.length = i := by
  induction path generalizing sel with
  | nil s =>
    have hfalse : ∀ p, p < w.parcels → sel p = false := by
      intro p hp
      cases hs : sel p with
      | false => rfl
      | true =>
        have hh := needs p hp hs
        have hd := done p hp
        simp [physicalParcel,hd,hh.2] at hh
    exact ⟨[],by simp [selectedWeight_empty w sel hfalse],by simp, rfl⟩
  | @cons s v u a b m h i o st tail ih =>
    let moved : Nat → Bool := fun p => sel p && side (physicalParcel v p)
    let remain : Nat → Bool := fun p => sel p && !side (physicalParcel v p)
    have moveCond : ∀ p, p < w.parcels → moved p = true →
        side (physicalParcel s p) = false ∧ side (physicalParcel v p) = true := by
      intro p hp hs
      have hh : sel p = true ∧ side (physicalParcel v p) = true := by
        simpa [moved] using hs
      exact ⟨(needs p hp hh.1).1,hh.2⟩
    have remCond : ∀ p, p < w.parcels → remain p = true →
        side (physicalParcel v p) = false ∧ side (w.goal p) = true := by
      intro p hp hs
      have hh : sel p = true ∧ side (physicalParcel v p) = false := by
        simpa [remain] using hs
      exact ⟨hh.2,(needs p hp hh.1).2⟩
    obtain ⟨gs,pg,fg,lg⟩ := legal_step_crossing_groups w side st vl vp C cap moved moveCond
    have vload := step_valid_load w st vl
    have vowner := step_valid_parcel_carriers w st vp
    have next : ∃ groups : List (List Nat),
        List.Perm (selectedWeights w remain) groups.flatten ∧
        (∀ g ∈ groups, g.sum ≤ C) ∧ groups.length = i := by
      apply ih <;> assumption
    obtain ⟨rs,pr,fr,lr⟩ := next
    refine ⟨gs++rs,?_,?_,?_⟩
    · have spl := selectedWeight_split w sel (fun p => side (physicalParcel v p))
      have comb := List.Perm.append pg pr
      rw [flatten_append_nat]
      exact spl.trans comb
    · intro g hg
      rcases List.mem_append.mp hg with left | right
      · exact fg g left
      · exact fr g right
    · simp [lg,lr]

def inwardSelection (w : World) (side : Nat → Bool) (s : State) : Nat → Bool :=
  fun p => !side (physicalParcel s p) && side (w.goal p)

def binInward (w : World) (side : Nat → Bool) (s : State) (C : Nat) (seed : BinState) : Nat :=
  let ws := selectedWeights w (inwardSelection w side s)
  (binDP C seed ws.length ws).1

theorem flux_inward_bin_bound (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (seed : BinState) :
    binInward w side s C seed ≤ i := by
  obtain ⟨gs,pg,fg,lg⟩ :=
    flux_path_groups w side path done vl vp C cap (inwardSelection w side s)
      (by intro p hp hs; simpa [inwardSelection] using hs)
  have h := binDP_le_feasible_groups C seed _ gs pg fg
  rw [lg] at h
  exact h

theorem flux_complement (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o) :
    FluxPath w (fun v => !side v) s u m h o i := by
  induction path with
  | nil s => exact FluxPath.nil s
  | cons st tail ih =>
    have h := FluxPath.cons st ih
    simpa [leavingTrucks] using h

def cutStockCount (w : World) (side : Nat → Bool) (s : State) : Nat :=
  sumN (fun t => if side (physicalTruck s t) then 1 else 0) w.trucks

theorem filtered_count_eq_sum (n : Nat) (sel : Nat → Bool) :
    ((List.range n).filter sel).length = sumN (fun p => if sel p then 1 else 0) n := by
  have eq : ∀ xs : List Nat, (xs.filter sel).length = ((xs.filter sel).map (fun _ => (1:Nat))).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases hs : sel x <;> simp [hs,ih,Nat.add_comm]
  rw [eq,filter_map_sum_nat,sum_range_eq_sumN]

theorem cut_stock_le (w : World) (side : Nat → Bool) (s : State) :
    cutStockCount w side s ≤ w.trucks := by
  unfold cutStockCount
  have h := sumN_mono (fun t => if side (physicalTruck s t) then 1 else 0)
    (fun _ => 1) w.trucks (by intro q hq; cases he : side (physicalTruck s q) <;> simp [he])
  have eq : sumN (fun _ => 1) w.trucks = w.trucks := by
    induction w.trucks with
    | zero => rfl
    | succ n ih => simp [sumN,ih]
  omega

theorem step_flux_balance (w : World) (side : Nat → Bool) (s u : State) :
    (enteringTrucks w side s u).length + cutStockCount w side s =
      (leavingTrucks w side s u).length + cutStockCount w side u := by
  simp only [leavingTrucks,enteringTrucks,cutStockCount]
  rw [filtered_count_eq_sum,filtered_count_eq_sum,← sumN_add,← sumN_add]
  apply sumN_congr
  intro t ht
  cases hs : side (physicalTruck s t) <;>
    cases hu : side (physicalTruck u t) <;> simp [hs,hu]

theorem path_flux_balance (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o) :
    i + cutStockCount w side s = o + cutStockCount w side u := by
  induction path with
  | nil s => simp
  | @cons s v u a b m h i o st tail ih =>
    have hh := step_flux_balance w side s v
    omega

-- The aggregate cut profile in ex1.py is now bounded directly by
-- actual truck crossings of every legal path: there are no I/O
-- demand premises left in this theorem.
theorem concrete_cut_profile_bound (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (seed : BinState) :
    let I := binInward w side s C seed
    let O := binInward w (fun v => !side v) s C seed
    let stock := cutStockCount w side s
    max (I+O) (max (2*I-(w.trucks-stock)) (2*O-stock)) ≤ i+o := by
  have hi := flux_inward_bin_bound w side path done vl vp C cap seed
  have ho := flux_inward_bin_bound w (fun v => !side v) (flux_complement w side path) done vl vp C cap seed
  have hb := path_flux_balance w side path
  have hs := cut_stock_le w side s
  have hu := cut_stock_le w side u
  dsimp
  omega

#print axioms flux_path_groups
#print axioms flux_inward_bin_bound
#print axioms path_flux_balance
#print axioms concrete_cut_profile_bound
end IslandLogistics


namespace IslandLogistics

theorem sumN_eq_zero_point (f : Nat → Nat) (n : Nat) (hz : sumN f n = 0)
    (t : Nat) (ht : t < n) : f t = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumN] at hz
    by_cases e : t = n
    · subst t; omega
    · exact ih (by omega) (by omega)

theorem no_trucks_in_side (w : World) (side : Nat → Bool) (s : State)
    (hz : cutStockCount w side s = 0) (t : Nat) (ht : t < w.trucks) :
    side (physicalTruck s t) = false := by
  have he := sumN_eq_zero_point (fun q => if side (physicalTruck s q) then 1 else 0)
    w.trucks hz t ht
  cases h : side (physicalTruck s t) <;> simp [h] at he ⊢

-- With no truck inside the side, no step can alter the status of a
-- parcel at a specified ground location in that side.
theorem step_preserves_unvisited_ground (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (hz : cutStockCount w side s = 0)
    (p a : Nat) (ha : side a = true) :
    s.parcel p = .ground a ↔ u.parcel p = .ground a := by
  cases st with
  | drive t b c ht hr valid => rfl
  | board t f b ht hf hr room valid => rfl
  | disembark t f ht valid => rfl
  | sail f b hr hne valid => rfl
  | load q t b hq ht room valid =>
    have hb := no_trucks_in_side w side s hz t valid.2.1
    have hb' : side b = false := by simpa [physicalTruck,ht] using hb
    have hne : b ≠ a := by
      intro e; subst b; rw [ha] at hb'; contradiction
    by_cases ep : p = q
    · subst p
      simp [hq,setAt,hne]
    · simp [setAt,ep]
  | unload q t b hq ht valid =>
    have hb := no_trucks_in_side w side s hz t valid.2.1
    have hb' : side b = false := by simpa [physicalTruck,ht] using hb
    have hne : b ≠ a := by
      intro e; subst b; rw [ha] at hb'; contradiction
    by_cases ep : p = q
    · subst p
      simp [hq,setAt,hne]
    · simp [setAt,ep]

theorem flux_no_entry_preserves_ground (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (stock : cutStockCount w side s = 0) (hi : i = 0)
    (p a : Nat) (ha : side a = true) :
    s.parcel p = .ground a ↔ u.parcel p = .ground a := by
  induction path with
  | nil s => rfl
  | @cons s v u a' b' m h i o st tail ih =>
    have hb := step_flux_balance w side s v
    have hv : cutStockCount w side v = 0 := by omega
    exact (step_preserves_unvisited_ground w side st stock p a ha).trans
      (ih hv (by omega))

-- A necessary entry follows from actual active work, even when
-- every selected parcel has source and goal on the same side.
theorem visit_inside_required (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (done : Goal w u) (vp : ValidParcelCarriers w s)
    (stock : cutStockCount w side s = 0)
    (p : Nat) (hp : p < w.parcels)
    (active : s.parcel p ≠ .ground (w.goal p))
    (work : side (physicalParcel s p) = true ∨ side (w.goal p) = true) :
    1 ≤ i := by
  by_cases hi : i = 0
  · exfalso
    rcases work with hs | hg
    · cases he : s.parcel p with
      | ground a =>
        have ha : side a = true := by simpa [physicalParcel,he] using hs
        have hstay := (flux_no_entry_preserves_ground w side path stock hi p a ha).mp he
        have hgoal := done p hp
        rw [hgoal] at hstay
        have ea : w.goal p = a := by simpa using hstay
        exact active (by simpa [ea] using he)
      | onTruck t =>
        have ht := vp p hp t he
        have hn := no_trucks_in_side w side s stock t ht
        simp [physicalParcel,he,hn] at hs
    · exact active ((flux_no_entry_preserves_ground w side path stock hi p (w.goal p) hg).mpr (done p hp))
  · omega

theorem stock_complement (w : World) (side : Nat → Bool) (s : State) :
    cutStockCount w side s + cutStockCount w (fun v => !side v) s = w.trucks := by
  unfold cutStockCount
  rw [← sumN_add]
  have hh := sumN_congr
    (fun t => (if side (physicalTruck s t) then 1 else 0) +
      (if !side (physicalTruck s t) then 1 else 0))
    (fun _ => 1) w.trucks (by
      intro t ht; cases he : side (physicalTruck s t) <;> simp [he])
  rw [hh]
  induction w.trucks with
  | zero => rfl
  | succ n ih => simp [sumN,ih]

def sideWork (w : World) (side : Nat → Bool) (s : State) : Prop :=
  ∃ p, p < w.parcels ∧ s.parcel p ≠ .ground (w.goal p) ∧
    (side (physicalParcel s p) = true ∨ side (w.goal p) = true)

noncomputable def visitInward (w : World) (side : Nat → Bool) (s : State)
    (C : Nat) (seed : BinState) : Nat := by
  classical
  exact if cutStockCount w side s = 0 ∧ sideWork w side s
    then max (binInward w side s C seed) 1 else binInward w side s C seed

theorem visit_inward_bound (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (seed : BinState) :
    visitInward w side s C seed ≤ i := by
  classical
  have hb := flux_inward_bin_bound w side path done vl vp C cap seed
  unfold visitInward
  split
  · rename_i hh
    obtain ⟨p,hp,ha,hw⟩ := hh.2
    have hv := visit_inside_required w side path done vp hh.1 p hp ha hw
    omega
  · exact hb

-- Both forced visit maxima from the real Python cut profile are included.
-- The conditional final stock formula is stated over signed integers so
-- final-stock subtraction has exactly the Python meaning.
theorem concrete_visit_cut_profile_bound (w : World) (side : Nat → Bool)
    {s u : State} {m h i o : Nat} (path : FluxPath w side s u m h i o)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C)
    (seed : BinState) :
    let I := visitInward w side s C seed
    let O := visitInward w (fun v => !side v) s C seed
    let k := cutStockCount w side s
    let f := cutStockCount w side u
    max (2*(I : Int)-((f : Int)-k)) (2*(O : Int)+((f : Int)-k)) ≤ (i : Int)+o ∧
    max (I+O) (max (2*I-(w.trucks-k)) (2*O-k)) ≤ i+o := by
  have hi := visit_inward_bound w side path done vl vp C cap seed
  have ho := visit_inward_bound w (fun v => !side v) (flux_complement w side path) done vl vp C cap seed
  have hb := path_flux_balance w side path
  have hs := cut_stock_le w side s
  have hu := cut_stock_le w side u
  dsimp
  omega

#print axioms visit_inside_required
#print axioms stock_complement
#print axioms concrete_visit_cut_profile_bound

end IslandLogistics


namespace IslandLogistics

def sideDelta (side : Nat → Bool) (a b : Nat) : Nat :=
  if side a = side b then 0 else 1

def truckFlux (w : World) (side : Nat → Bool) (s u : State) : Nat :=
  (enteringTrucks w side s u).length + (leavingTrucks w side s u).length

theorem truckFlux_sum (w : World) (side : Nat → Bool) (s u : State) :
    truckFlux w side s u =
      sumN (fun t => sideDelta side (physicalTruck s t) (physicalTruck u t)) w.trucks := by
  simp only [truckFlux,leavingTrucks,enteringTrucks,filtered_count_eq_sum,← sumN_add]
  apply sumN_congr
  intro t ht
  cases hs : side (physicalTruck s t) <;>
    cases hu : side (physicalTruck u t) <;> simp [sideDelta,hs,hu]

theorem sumN_single (f : Nat → Nat) (n t : Nat) (ht : t < n)
    (hf : ∀ q, q < n → q ≠ t → f q = 0) :
    sumN f n = f t := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : t = n
    · subst t
      have hz : sumN f n = 0 := by
        have h := sumN_congr f (fun _ => 0) n (fun q hq => hf q (by omega) (by omega))
        rw [h,sumN_zero]
      simp [sumN,hz]
    · have h := ih (by omega) (fun q hq neq => hf q (by omega) neq)
      have h0 := hf n (by omega) (by omega)
      simp [sumN,h,h0]

-- For each actual DRIVE, at most one selected true bridge cut changes
-- sides. All usable ferry routes stay within a side of each such cut.
-- These are graph properties, not claims about a heuristic or optimum.
structure RoadCutSystem (w : World) where
  cuts : List (Nat → Bool)
  road : ∀ a b, w.road a b → (cuts.map (fun side => sideDelta side a b)).sum ≤ 1
  ferry : ∀ side ∈ cuts, ∀ f a b, 0 < w.slots f →
    w.route f a → w.route f b → side a = side b

theorem step_drive_flux (w : World) (side : Nat → Bool)
    (s : State) (t a b : Nat) (ht : s.truck t = .land a) (valid : t < w.trucks) :
    truckFlux w side s {s with truck := setAt s.truck t (.land b)} = sideDelta side a b := by
  rw [truckFlux_sum]
  rw [sumN_single _ _ t valid (by
    intro q hq ne
    simp [physicalTruck,setAt,ne,sideDelta])]
  simp [physicalTruck,ht,setAt]

theorem flux_zero_of_same_side (w : World) (side : Nat → Bool) (s u : State)
    (h : ∀ t, t < w.trucks → side (physicalTruck s t) = side (physicalTruck u t)) :
    truckFlux w side s u = 0 := by
  rw [truckFlux_sum]
  have eq := sumN_congr (fun t => sideDelta side (physicalTruck s t) (physicalTruck u t))
    (fun _ => 0) w.trucks (fun t ht => by simp [sideDelta,h t ht])
  rw [eq,sumN_zero]

theorem sum_map_eq_zero {α : Type} (xs : List α) (f : α → Nat)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp),ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem sum_map_eq_on {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x = g x) : (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp),ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem step_road_cut_budget (w : World) (sys : RoadCutSystem w)
    {s u : State} {m h : Nat} (st : Step w s u m h)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s) :
    (sys.cuts.map (fun side => truckFlux w side s u)).sum ≤ m := by
  cases st with
  | drive t a b ht hr valid =>
    rw [sum_map_eq_on sys.cuts _ (fun side => sideDelta side a b)
      (fun side _ => step_drive_flux w side s t a b ht valid.1)]
    exact sys.road a b hr
  | board t f a ht hf hr room valid =>
    rw [sum_map_eq_zero sys.cuts _ (by
      intro side hside
      apply flux_zero_of_same_side
      intro q hq
      by_cases eq : q = t
      · subst q; simp [physicalTruck,ht,hf,setAt]
      · simp [physicalTruck,setAt,eq])]
    omega
  | disembark t f ht valid =>
    rw [sum_map_eq_zero sys.cuts _ (by
      intro side hside
      apply flux_zero_of_same_side
      intro q hq
      by_cases eq : q = t
      · subst q; simp [physicalTruck,ht,setAt]
      · simp [physicalTruck,setAt,eq])]
    omega
  | sail f b hr hne valid =>
    rw [sum_map_eq_zero sys.cuts _ (by
      intro side hside
      apply flux_zero_of_same_side
      intro q hq
      cases he : s.truck q with
      | land a => simp [physicalTruck,he]
      | onFerry g =>
        by_cases eq : g = f
        · subst g
          have hk := vt q hq f he
          simpa [physicalTruck,he,setAt] using
            sys.ferry side hside f (s.ferry f) b hk.2 (vf f hk.1) hr
        · simp [physicalTruck,he,setAt,eq])]
    omega
  | load p t a hp ht room valid =>
    rw [sum_map_eq_zero sys.cuts _ (fun side _ =>
      flux_zero_of_same_side w side s {s with parcel := setAt s.parcel p (.onTruck t)} (fun _ _ => rfl))]
    omega
  | unload p t a hp ht valid =>
    rw [sum_map_eq_zero sys.cuts _ (fun side _ =>
      flux_zero_of_same_side w side s {s with parcel := setAt s.parcel p (.ground a)} (fun _ _ => rfl))]
    omega

-- Reified legal trace, so crossing counts for ALL cuts are measured
-- on the same concrete completion, not different existential paths.
inductive LegalTrace (w : World) : State → State → Nat → Nat → Type where
  | nil (s : State) : LegalTrace w s s 0 0
  | cons {s v u : State} {a b m h : Nat} :
    Step w s v a b → LegalTrace w v u m h → LegalTrace w s u (a+m) (b+h)

theorem trace_from_path (w : World) {s u : State} {m h : Nat}
    (p : Path (Step w) s u m h) : Nonempty (LegalTrace w s u m h) := by
  induction p with
  | nil s => exact ⟨LegalTrace.nil s⟩
  | cons st tail ih =>
    obtain ⟨tr⟩ := ih
    exact ⟨LegalTrace.cons st tr⟩

def traceIn (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} : LegalTrace w s u m h → Nat
  | .nil _ => 0
  | @LegalTrace.cons _ s v u a b m h st tail =>
    (enteringTrucks w side s v).length + traceIn w side tail

def traceOut (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} : LegalTrace w s u m h → Nat
  | .nil _ => 0
  | @LegalTrace.cons _ s v u a b m h st tail =>
    (leavingTrucks w side s v).length + traceOut w side tail

theorem trace_flux_path (w : World) (side : Nat → Bool)
    {s u : State} {m h : Nat} (tr : LegalTrace w s u m h) :
    FluxPath w side s u m h (traceIn w side tr) (traceOut w side tr) := by
  induction tr with
  | nil s => exact FluxPath.nil s
  | cons st tail ih => exact FluxPath.cons st ih

theorem sum_map_add_nat {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hh := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp; omega

theorem trace_road_cut_budget (w : World) (sys : RoadCutSystem w)
    {s u : State} {m h : Nat} (tr : LegalTrace w s u m h)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s) :
    (sys.cuts.map (fun side => traceIn w side tr + traceOut w side tr)).sum ≤ m := by
  induction tr with
  | nil s => simp [traceIn,traceOut,sum_map_eq_zero]
  | @cons s v u a b m h st tail ih =>
    have hb := step_road_cut_budget w sys st vf vt
    have ht := ih (step_valid_ferries w st vf) (step_valid_truck_carriers w st vt)
    rw [sum_map_eq_on sys.cuts _
      (fun side => truckFlux w side s v + (traceIn w side tail + traceOut w side tail))
      (by intro side hs; simp [truckFlux,traceIn,traceOut]; omega)]
    rw [sum_map_add_nat]
    omega

noncomputable def independentCutCost (w : World) (side : Nat → Bool)
    (s : State) (C : Nat) (seed : BinState) : Nat :=
  let I := visitInward w side s C seed
  let O := visitInward w (fun a => !side a) s C seed
  let k := cutStockCount w side s
  max (I+O) (max (2*I-(w.trucks-k)) (2*O-k))

-- Actual theorem for the sum of independent true-road-bridge profiles,
-- including the forced visits. Every legal path supplies the witness.
theorem road_cut_sum_admissible (w : World) (sys : RoadCutSystem w)
    {s u : State} {m h : Nat} (path : Path (Step w) s u m h)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (vf : ValidFerries w s) (vt : ValidTruckCarriers w s)
    (C : Nat) (cap : ∀ t, t < w.trucks → w.capacity t ≤ C) (seed : BinState) :
    handling w s + (sys.cuts.map (fun side => independentCutCost w side s C seed)).sum ≤ m+h := by
  obtain ⟨tr⟩ := trace_from_path w path
  have hb := trace_road_cut_budget w sys tr vf vt
  have hs : (sys.cuts.map (fun side => independentCutCost w side s C seed)).sum ≤
      (sys.cuts.map (fun side => traceIn w side tr + traceOut w side tr)).sum := by
    apply sum_map_le
    intro side hside
    exact (concrete_visit_cut_profile_bound w side (trace_flux_path w side tr) done vl vp C cap seed).2
  have hhandling := handling_path w path done
  omega

#print axioms step_road_cut_budget
#print axioms trace_road_cut_budget
#print axioms road_cut_sum_admissible
end IslandLogistics


namespace IslandLogistics

-- Unlike the earlier existential carrier segment, these functions refer
-- to the very same reified legal trace used to count all cut crossings.
def traceCarrier (w : World) {s u : State} {m h : Nat}
    (tr : LegalTrace w s u m h) (p : Nat) : Option Nat :=
  match tr with
  | .nil s => jobOwner s p
  | @LegalTrace.cons _ s _ u a b m h st tail =>
    match s.parcel p with
    | .onTruck t => some t
    | .ground _ => traceCarrier w tail p

def traceSafe (w : World) {s u : State} {m h : Nat}
    (tr : LegalTrace w s u m h) (p : Nat) : Prop :=
  match tr with
  | .nil _ => True
  | @LegalTrace.cons _ s v u a b m h st tail =>
    extraOne w s v p = 0 ∧ traceSafe w tail p

theorem traceCarrier_held (w : World) {s u : State} {m h : Nat}
    (tr : LegalTrace w s u m h) (p t : Nat)
    (held : s.parcel p = .onTruck t) :
    traceCarrier w tr p = some t := by
  cases tr <;> simp [traceCarrier,jobOwner,held]

theorem traceCarrier_tail_active (w : World)
    {s v u : State} {a b m h : Nat} (st : Step w s v a b)
    (tail : LegalTrace w v u m h) (p : Nat)
    (safe : extraOne w s v p = 0)
    (active : v.parcel p ≠ .ground (w.goal p)) :
    traceCarrier w (LegalTrace.cons st tail) p = traceCarrier w tail p := by
  cases hp : s.parcel p with
  | ground x => simp [traceCarrier,hp]
  | onTruck t =>
    rcases held_job_step w p t st hp safe with hold | done
    · rw [traceCarrier_held w (LegalTrace.cons st tail) p t hp,
        traceCarrier_held w tail p t hold]
    · exact False.elim (active done.1)

def truckIn (side : Nat → Bool) (t : Nat) (s u : State) : Nat :=
  if !side (physicalTruck s t) && side (physicalTruck u t) then 1 else 0

def truckOut (side : Nat → Bool) (t : Nat) (s u : State) : Nat :=
  truckIn (fun v => !side v) t s u

def traceTruckIn (w : World) (side : Nat → Bool) (t : Nat)
    {s u : State} {m h : Nat} : LegalTrace w s u m h → Nat
  | .nil _ => 0
  | @LegalTrace.cons _ s v u a b m h st tail =>
    truckIn side t s v + traceTruckIn w side t tail

theorem traceTruckIn_complement (w : World) (side : Nat → Bool) (t : Nat)
    {s u : State} {m h : Nat} (tr : LegalTrace w s u m h) :
    traceTruckIn w (fun x => !(!side x)) t tr = traceTruckIn w side t tr := by
  have he : (fun x => !(!side x)) = side := by
    funext x; cases side x <;> rfl
  rw [he]

theorem truck_crossing_group (w : World) (side : Nat → Bool) (t : Nat)
    {s v u : State} {a b m h : Nat} (st : Step w s v a b)
    (tail : LegalTrace w v u m h)
    (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (ht : t < w.trucks) (sel : Nat → Bool)
    (owners : ∀ p, p < w.parcels → sel p = true →
      traceCarrier w (LegalTrace.cons st tail) p = some t)
    (moves : ∀ p, p < w.parcels → sel p = true →
      side (physicalParcel s p) = false ∧ side (physicalParcel v p) = true) :
    ∃ groups : List (List Nat),
      List.Perm (selectedWeights w sel) groups.flatten ∧
      (∀ g ∈ groups, g.sum ≤ w.capacity t) ∧
      groups.length = truckIn side t s v := by
  have holds : ∀ p, p < w.parcels → sel p = true →
      s.parcel p = .onTruck t ∧ v.parcel p = .onTruck t := by
    intro p hp hs
    have d := moves p hp hs
    have hd : side (physicalParcel s p) ≠ side (physicalParcel v p) := by
      rw [d.1,d.2]; decide
    obtain ⟨q,hq,he,hv⟩ := parcel_side_change_carrier w side st vp p hp hd
    have hown := traceCarrier_held w (LegalTrace.cons st tail) p q he
    rw [owners p hp hs] at hown
    have eq := Option.some.inj hown
    subst q
    exact ⟨he,hv⟩
  by_cases hc : truckIn side t s v = 1
  · refine ⟨[selectedWeights w sel],by simp,?_,by simp [hc]⟩
    intro g hg
    have eq : g = selectedWeights w sel := by simpa using hg
    subst g
    exact Nat.le_trans (selectedWeight_carrier_le w s t sel (fun p hp hs => (holds p hp hs).1)) (vl t ht)
  · have hz : truckIn side t s v = 0 := by
      unfold truckIn at *
      cases h1 : side (physicalTruck s t) <;> cases h2 : side (physicalTruck v t) <;> simp_all
    have hzero : ∀ p, p < w.parcels → sel p = false := by
      intro p hp
      cases hs : sel p with
      | false => rfl
      | true =>
        have h := holds p hp hs
        have d := moves p hp hs
        have ho : side (physicalTruck s t) = false := by simpa [physicalParcel,h.1] using d.1
        have hi : side (physicalTruck v t) = true := by simpa [physicalParcel,h.2] using d.2
        simp [truckIn,ho,hi] at hc
    exact ⟨[],by simp [selectedWeight_empty w sel hzero],by simp,by simp [hz]⟩

-- Every inward-demand direct job assigned to t is placed in a group
-- corresponding to an actual inward crossing of t on THIS trace.
theorem trace_assigned_groups (w : World) (side : Nat → Bool) (t : Nat)
    {s u : State} {m h : Nat} (tr : LegalTrace w s u m h)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (ht : t < w.trucks) (sel : Nat → Bool)
    (owners : ∀ p, p < w.parcels → sel p = true →
      traceCarrier w tr p = some t ∧ traceSafe w tr p)
    (needs : ∀ p, p < w.parcels → sel p = true →
      side (physicalParcel s p) = false ∧ side (w.goal p) = true) :
    ∃ groups : List (List Nat),
      List.Perm (selectedWeights w sel) groups.flatten ∧
      (∀ g ∈ groups, g.sum ≤ w.capacity t) ∧
      groups.length = traceTruckIn w side t tr := by
  induction tr generalizing sel with
  | nil s =>
    have hfalse : ∀ p, p < w.parcels → sel p = false := by
      intro p hp
      cases hs : sel p with
      | false => rfl
      | true =>
        have hh := needs p hp hs
        have hd := done p hp
        simp [physicalParcel,hd,hh.2] at hh
    exact ⟨[],by simp [selectedWeight_empty w sel hfalse],by simp,rfl⟩
  | @cons s v u a b m h st tail ih =>
    let moved : Nat → Bool := fun p => sel p && side (physicalParcel v p)
    let remain : Nat → Bool := fun p => sel p && !side (physicalParcel v p)
    have moveCond : ∀ p, p < w.parcels → moved p = true →
        side (physicalParcel s p) = false ∧ side (physicalParcel v p) = true := by
      intro p hp hs
      have hh : sel p = true ∧ side (physicalParcel v p) = true := by simpa [moved] using hs
      exact ⟨(needs p hp hh.1).1,hh.2⟩
    have remCond : ∀ p, p < w.parcels → remain p = true →
        side (physicalParcel v p) = false ∧ side (w.goal p) = true := by
      intro p hp hs
      have hh : sel p = true ∧ side (physicalParcel v p) = false := by simpa [remain] using hs
      exact ⟨hh.2,(needs p hp hh.1).2⟩
    have remOwn : ∀ p, p < w.parcels → remain p = true →
        traceCarrier w tail p = some t ∧ traceSafe w tail p := by
      intro p hp hs
      have hh : sel p = true ∧ side (physicalParcel v p) = false := by simpa [remain] using hs
      have own := owners p hp hh.1
      have hsafe := own.2
      change extraOne w s v p = 0 ∧ traceSafe w tail p at hsafe
      have active : v.parcel p ≠ .ground (w.goal p) := by
        intro eq
        have hr := remCond p hp hs
        simp [physicalParcel,eq,hr.2] at hr
      have eq := traceCarrier_tail_active w st tail p hsafe.1 active
      exact ⟨eq.symm.trans own.1,hsafe.2⟩
    obtain ⟨gs,pg,fg,lg⟩ := truck_crossing_group w side t st tail vl vp ht moved
      (by
        intro p hp hs
        have hh : sel p = true ∧ side (physicalParcel v p) = true := by simpa [moved] using hs
        exact (owners p hp hh.1).1) moveCond
    obtain ⟨rs,pr,fr,lr⟩ := ih done (step_valid_load w st vl)
      (step_valid_parcel_carriers w st vp) remain remOwn remCond
    refine ⟨gs++rs,?_,?_,?_⟩
    · have spl := selectedWeight_split w sel (fun p => side (physicalParcel v p))
      rw [flatten_append_nat]
      exact spl.trans (List.Perm.append pg pr)
    · intro g hg
      rcases List.mem_append.mp hg with left | right
      · exact fg g left
      · exact fr g right
    · simp [traceTruckIn,lg,lr]

theorem trace_assigned_bin_bound (w : World) (side : Nat → Bool) (t : Nat)
    {s u : State} {m h : Nat} (tr : LegalTrace w s u m h)
    (done : Goal w u) (vl : ValidTruckLoad w s) (vp : ValidParcelCarriers w s)
    (ht : t < w.trucks) (sel : Nat → Bool)
    (owners : ∀ p, p < w.parcels → sel p = true →
      traceCarrier w tr p = some t ∧ traceSafe w tr p)
    (needs : ∀ p, p < w.parcels → sel p = true →
      side (physicalParcel s p) = false ∧ side (w.goal p) = true)
    (seed : BinState) :
    (binDP (w.capacity t) seed (selectedWeights w sel).length (selectedWeights w sel)).1 ≤
      traceTruckIn w side t tr := by
  obtain ⟨gs,pg,fg,lg⟩ := trace_assigned_groups w side t tr done vl vp ht sel owners needs
  have h := binDP_le_feasible_groups (w.capacity t) seed _ gs pg fg
  rw [lg] at h
  exact h

#print axioms traceCarrier_tail_active
#print axioms truck_crossing_group
#print axioms trace_assigned_groups
#print axioms trace_assigned_bin_bound
end IslandLogistics
