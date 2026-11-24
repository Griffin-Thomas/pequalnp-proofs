import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma opMono_rev : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma and_false_of (l : List ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i ∈ l) (hf : f i = false) :
    GateOp.and.eval (l.map f) = false := by
  simp only [GateOp.eval]
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
  simp [hf] at this

lemma ofFn_getD {n : ℕ} (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

open PEqualNP.EdgeOwnership in
lemma cones_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (i : ℕ) (hi : i < cs.length) :
    (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n cs g).length := by simp [coneStep]; omega
    rw [ih (coneStep n cs g) hlt]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

open PEqualNP.EdgeOwnership in
lemma cones_mem (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length)
    (w : ℕ) (hw : w ∈ (gs[j]).inputs) (hw1 : n ≤ w) (hw2 : w < n + (cs.length + j)) (t : ℕ)
    (ht : t = w - n ∨ t ∈ (gs.foldl (coneStep n) cs).getD (w - n) []) :
    t ∈ (gs.foldl (coneStep n) cs).getD (cs.length + j) [] := by
  induction gs generalizing cs j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons] at ht ⊢
    cases j with
    | zero =>
      have hlt : cs.length < (coneStep n cs g).length := by simp [coneStep]
      rw [Nat.add_zero, cones_getD_lt n gs (coneStep n cs g) cs.length hlt]
      have hwl : w - n < cs.length := by omega
      rw [cones_getD_lt n gs (coneStep n cs g) (w - n) (by simp [coneStep]; omega)] at ht
      have e1 : (coneStep n cs g).getD (w - n) [] = cs.getD (w - n) [] := by
        simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwl]
      have e2 : (coneStep n cs g).getD cs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp [coneStep, List.getD_eq_getElem?_getD]
      rw [e2]
      rw [e1] at ht
      simp only [List.getElem_cons_zero] at hw
      rw [List.mem_flatMap]
      refine ⟨w, ?_, ?_⟩
      · rw [List.mem_filter]; exact ⟨hw, by simp; omega⟩
      · rcases ht with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hl : (coneStep n cs g).length = cs.length + 1 := by simp [coneStep]
      have := ih (coneStep n cs g) j hj' (by simpa using hw) (by rw [hl]; omega) ht
      rw [hl] at this
      have e : cs.length + (j + 1) = cs.length + 1 + j := by omega
      rw [e]; exact this

open PEqualNP.EdgeOwnership in
lemma inCone_of_read {n : ℕ} {C : Circuit} {r s : ℕ} (hr : r < C.gates.length) (hs : s < r)
    (hin : n + s ∈ (gateAt C r).inputs) : InCone n C s r := by
  unfold InCone cones
  have := cones_mem n C.gates [] r hr (n + s) (by rwa [← gateAt_eq hr]) (by omega)
    (by simp; omega) s (Or.inl (by omega))
  simpa using this

open PEqualNP.EdgeOwnership in
lemma inCone_trans_read {n : ℕ} {C : Circuit} {r s t : ℕ} (hr : r < C.gates.length) (hs : s < r)
    (hin : n + s ∈ (gateAt C r).inputs) (ht : InCone n C t s) : InCone n C t r := by
  unfold InCone cones at *
  have := cones_mem n C.gates [] r hr (n + s) (by rwa [← gateAt_eq hr]) (by omega)
    (by simp; omega) t (Or.inr (by simpa using ht))
  simpa using this

lemma monoC {n : ℕ} {C : Circuit} (hA : PEqualNP.EdgeOwnership.AndOrOnly C)
    (y y' : Fin n → Bool) (hy : ∀ j, y j = true → y' j = true) :
    ∀ i, val C (List.ofFn y) i = true → val C (List.ofFn y') i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < n
    · rw [val_input (by simp) hi, ofFn_getD y i hi] at h
      rw [val_input (by simp) hi, ofFn_getD y' i hi]
      exact hy _ h
    · by_cases hg : i < n + C.gates.length
      · obtain ⟨r, rfl⟩ : ∃ r, i = n + r := ⟨i - n, by omega⟩
        have hr : r < C.gates.length := by omega
        rw [val_gate (by simp) hr] at h ⊢
        have hop := hA _ (gateAt_mem hr)
        refine opMono_imp _ hop _ _ _ ?_ h
        intro j _
        by_cases hj : j < n + r
        · rw [if_pos hj, if_pos hj]; exact ih j hj
        · rw [if_neg hj, if_neg hj]; exact id
      · rw [val_ge (n := n) (by simp) (by omega)] at h; cases h

end PEqualNP.Outside.L_meta_3545

open PEqualNP.Outside.L_meta_3545 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hqH hAO hC hNR hP hk2 hk3 hk45 hG0 hD hrho8 hrho9
  obtain ⟨hAnd, hRB, -⟩ := hAO
  have hDlen : D.gates.length = G0.length + C.gates.length := by rw [hD]; simp
  have hDo : D.output = if C.output < n then C.output else C.output + G0.length := by rw [hD]
  have hDgate : ∀ r < C.gates.length, gateAt D (G0.length + r) =
      ⟨(gateAt C r).op, (gateAt C r).inputs.map (rho r)⟩ := by
    intro r hr
    rw [gateAt_eq (by rw [hDlen]; omega), gateAt_eq hr]
    simp only [hD]
    rw [List.getElem_append_right (by omega)]
    simp [List.getElem_mapIdx]
  have hDpre : ∀ (y : Fin n → Bool) (i : ℕ), i < n + G0.length →
      val D (List.ofFn y) i = PEqualNP.CleanedNonEdge.wireVal n ⟨G0, 0⟩ i y := by
    intro y i hi
    unfold val PEqualNP.CleanedNonEdge.wireVal
    rw [wires_eq_foldl, wires_eq_foldl]
    simp only [hD, List.foldl_append]
    exact foldl_getD_lt _ _ _ (by rw [foldl_length]; simp; omega)
  have hDval : ∀ (y : Fin n → Bool) (r : ℕ), r < C.gates.length →
      val D (List.ofFn y) (n + (G0.length + r)) = (gateAt C r).op.eval ((gateAt C r).inputs.map
        fun i => if rho r i < n + (G0.length + r) then val D (List.ofFn y) (rho r i) else false) := by
    intro y r hr
    rw [val_gate (by simp) (by rw [hDlen]; omega : G0.length + r < D.gates.length), hDgate r hr]
    simp only [List.map_map, Function.comp_def]
  have hCval : ∀ (y : Fin n → Bool) (r : ℕ), r < C.gates.length →
      val C (List.ofFn y) (n + r) =
        (gateAt C r).op.eval ((gateAt C r).inputs.map fun i => val C (List.ofFn y) i) := by
    intro y r hr
    rw [val_gate (by simp) hr]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [if_pos (hRB r hr i hi)]
  have hnon : ∀ (y : Fin n → Bool) (r : ℕ), r < C.gates.length → ∀ i ∈ (gateAt C r).inputs,
      (∀ k < m, ¬ (NR k r ∧ i = n + u k)) →
      (if rho r i < n + (G0.length + r) then val D (List.ofFn y) (rho r i) else false) =
        if i < n then val C (List.ofFn y) i
        else val D (List.ofFn y) (n + (G0.length + (i - n))) := by
    intro y r hr i hi hni
    have hib := hRB r hr i hi
    rw [hrho8 r hr i hi hni]
    by_cases h : i < n
    · rw [if_pos h, if_pos h, if_pos (by omega), val_input (by simp) h,
        val_input (by simp) h]
    · rw [if_neg h, if_neg h, if_pos (by omega)]
      congr 1; omega
  have hunaff : ∀ (y : Fin n → Bool) (r : ℕ), r < C.gates.length →
      (∀ k < m, ∀ t, NR k t → t ≠ r ∧ ¬ PEqualNP.EdgeOwnership.InCone n C t r) →
      val D (List.ofFn y) (n + (G0.length + r)) = val C (List.ofFn y) (n + r) := by
    intro y r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hfree
      rw [hDval y r hr, hCval y r hr]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hni : ∀ k < m, ¬ (NR k r ∧ i = n + u k) := fun k hk h => (hfree k hk r h.1).1 rfl
      rw [hnon y r hr i hi hni]
      by_cases h : i < n
      · rw [if_pos h]
      · rw [if_neg h]
        have hib := hRB r hr i hi
        obtain ⟨s, rfl⟩ : ∃ s, i = n + s := ⟨i - n, by omega⟩
        have hs : s < r := by omega
        rw [show n + s - n = s by omega]
        refine ih s hs (by omega) ?_
        intro k hk t ht
        have := hfree k hk t ht
        refine ⟨?_, ?_⟩
        · rintro rfl; exact this.2 (inCone_of_read hr hs hi)
        · intro hc; exact this.2 (inCone_trans_read hr hs hi hc)
  have hnr : ∀ (y : Fin n → Bool) (r k : ℕ), r < C.gates.length → k < m → NR k r →
      (if rho r (n + u k) < n + (G0.length + r) then val D (List.ofFn y) (rho r (n + u k))
        else false) = P k y := by
    intro y r k hr hk hnrk
    rcases hrho9 r k hk hnrk with ⟨h1, h2⟩ | ⟨g9, hg9, h1, h2, h3⟩ | ⟨h1, h2⟩
    · rw [if_pos (by omega), hDpre y _ h1, h2]
    · rw [h1, if_pos (by omega), show n + G0.length + g9 = n + (G0.length + g9) by omega,
        hunaff y g9 (by omega) h3]
      exact h2 y
    · rw [if_neg (by omega), h1]
  have hTfalse : ∀ (y : Fin n → Bool) (k : ℕ), k < m → (List.ofFn y).getD (z k) false = false →
      val C (List.ofFn y) (n + T k) = false ∧
        val D (List.ofFn y) (n + (G0.length + T k)) = false := by
    intro y k hk hz
    obtain ⟨-, hT, hop, hzn, hin, -, -⟩ := hk2 k hk
    have hzin : z k ∈ (gateAt C (T k)).inputs := by rcases hin with h | h <;> rw [h] <;> simp
    have hzval : val C (List.ofFn y) (z k) = false := by rw [val_input (by simp) hzn]; exact hz
    constructor
    · rw [hCval y _ hT, hop]
      exact and_false_of _ _ (z k) hzin hzval
    · rw [hDval y _ hT, hop]
      refine and_false_of _ _ (z k) hzin ?_
      have hni : ∀ k' < m, ¬ (NR k' (T k) ∧ z k = n + u k') := fun k' _ h => by omega
      rw [hnon y (T k) hT (z k) hzin hni, if_pos hzn]
      exact hzval
  have hinv : ∀ (R : Bool → Bool → Prop), OpMono R → (∀ b, R b b) → ∀ (y : Fin n → Bool),
      (∀ k < m, (List.ofFn y).getD (z k) false = true →
        R (val C (List.ofFn y) (n + u k)) (P k y)) →
      ∀ r, r < C.gates.length →
      (∀ k < m, PEqualNP.CleanedNonEdge.OrReaches n C (W k) r → (gateAt C r).op = GateOp.or →
        PEqualNP.EdgeOwnership.InCone n C (u k) r → (List.ofFn y).getD (z k) false = true) →
      R (val C (List.ofFn y) (n + r)) (val D (List.ofFn y) (n + (G0.length + r))) := by
    intro R hR hrefl y hPR r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr hmod
      by_cases hex : ∃ k < m, r = T k ∧ (List.ofFn y).getD (z k) false = false
      · obtain ⟨k, hk, rfl, hz⟩ := hex
        obtain ⟨h1, h2⟩ := hTfalse y k hk hz
        rw [h1, h2]; exact hrefl false
      · have hT' : ∀ k < m, r = T k → (List.ofFn y).getD (z k) false = true := by
          intro k hk hrT
          by_contra hc
          exact hex ⟨k, hk, hrT, by simpa using hc⟩
        rw [hCval y r hr, hDval y r hr]
        refine hR _ (hAnd _ (gateAt_mem hr)) _ _ _ ?_
        intro i hi
        have hib := hRB r hr i hi
        by_cases hn : ∃ k < m, NR k r ∧ i = n + u k
        · obtain ⟨k, hk, hnrk, rfl⟩ := hn
          rw [hnr y r k hr hk hnrk]
          apply hPR k hk
          rcases (hNR k r).1 hnrk with ⟨-, -, hrT | ⟨hor, hop⟩⟩
          · exact hT' k hk hrT
          · exact hmod k hk hor hop (inCone_of_read hr (by omega) hi)
        · have hni : ∀ k < m, ¬ (NR k r ∧ i = n + u k) := fun k hk h => hn ⟨k, hk, h⟩
          rw [hnon y r hr i hi hni]
          by_cases h : i < n
          · rw [if_pos h]; exact hrefl _
          · rw [if_neg h]
            obtain ⟨s, rfl⟩ : ∃ s, i = n + s := ⟨i - n, by omega⟩
            have hs : s < r := by omega
            rw [show n + s - n = s by omega]
            refine ih s hs (by omega) ?_
            intro k hk hor hop hc
            obtain ⟨-, hread⟩ := hk3 k hk s (by omega) hor hop hc
            rcases hread r hr hi with hrT | ⟨hor', hop'⟩
            · exact hT' k hk hrT
            · exact hmod k hk hor' hop' (inCone_trans_read hr hs hi hc)
  have hout : ∀ (R : Bool → Bool → Prop), OpMono R → (∀ b, R b b) → ∀ (y : Fin n → Bool),
      (∀ k < m, (List.ofFn y).getD (z k) false = true →
        R (val C (List.ofFn y) (n + u k)) (P k y)) →
      R (C.eval (List.ofFn y)) (D.eval (List.ofFn y)) := by
    intro R hR hrefl y hPR
    rw [eval_eq_val, eval_eq_val, hDo]
    by_cases h1 : C.output < n
    · rw [if_pos h1, val_input (by simp) h1, val_input (by simp) h1]; exact hrefl _
    · rw [if_neg h1]
      by_cases h2 : C.output < n + C.gates.length
      · obtain ⟨r, hr⟩ : ∃ r, C.output = n + r := ⟨C.output - n, by omega⟩
        rw [hr, show n + r + G0.length = n + (G0.length + r) by omega]
        refine hinv R hR hrefl y hPR r (by omega) ?_
        intro k hk hor hop hc
        exact absurd hr (hk3 k hk r (by omega) hor hop hc).1
      · rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by rw [hDlen]; omega)]
        exact hrefl _
  have hmonoD : ∀ (y y' : Fin n → Bool), (∀ j, y j = true → y' j = true) →
      ∀ r, r < C.gates.length → val D (List.ofFn y) (n + (G0.length + r)) = true →
        val D (List.ofFn y') (n + (G0.length + r)) = true := by
    intro y y' hy r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr
      rw [hDval y r hr, hDval y' r hr]
      refine opMono_imp _ (hAnd _ (gateAt_mem hr)) _ _ _ ?_
      intro i hi
      have hib := hRB r hr i hi
      by_cases hn : ∃ k < m, NR k r ∧ i = n + u k
      · obtain ⟨k, hk, hnrk, rfl⟩ := hn
        rw [hnr y r k hr hk hnrk, hnr y' r k hr hk hnrk, hP k y, hP k y']
        simp only [decide_eq_true_eq]
        rintro ⟨w, hw1, hw2⟩
        exact ⟨w, hy w hw1, hw2⟩
      · have hni : ∀ k < m, ¬ (NR k r ∧ i = n + u k) := fun k hk h => hn ⟨k, hk, h⟩
        rw [hnon y r hr i hi hni, hnon y' r hr i hi hni]
        by_cases h : i < n
        · rw [if_pos h, if_pos h]; exact monoC hAnd y y' hy i
        · rw [if_neg h, if_neg h]; exact ih (i - n) (by omega) (by omega)
  have hmonoDeval : ∀ (y y' : Fin n → Bool), (∀ j, y j = true → y' j = true) →
      D.eval (List.ofFn y) = true → D.eval (List.ofFn y') = true := by
    intro y y' hy
    rw [eval_eq_val, eval_eq_val, hDo]
    by_cases h1 : C.output < n
    · rw [if_pos h1, val_input (by simp) h1, val_input (by simp) h1, ofFn_getD y _ h1,
        ofFn_getD y' _ h1]
      exact hy _
    · rw [if_neg h1]
      by_cases h2 : C.output < n + C.gates.length
      · obtain ⟨r, hr⟩ : ∃ r, C.output = n + r := ⟨C.output - n, by omega⟩
        rw [hr, show n + r + G0.length = n + (G0.length + r) by omega]
        exact hmonoD y y' hy r (by omega)
      · rw [val_ge (n := n) (by simp) (by rw [hDlen]; omega)]
        intro h; cases h
  intro y
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hD1
    have h := hout (fun a b => b = true → a = true) opMono_rev (fun b h => h) y ?_ hD1
    · rw [hC y] at h; exact h
    · intro k hk hz hPk
      rw [hP k y] at hPk
      simp only [decide_eq_true_eq] at hPk
      obtain ⟨w, hw, hwv⟩ := hPk
      refine monoC hAnd _ y ?_ _ hwv
      intro j hj
      simp only [decide_eq_true_eq] at hj
      rcases hj with rfl | hj
      · exact hw
      · have hzn := (hk2 k hk).2.2.2.1
        rw [ofFn_getD y _ hzn] at hz
        have hj' : j = ⟨z k, hzn⟩ := Fin.ext hj
        rw [hj']; exact hz
  · intro hq
    obtain ⟨a, b, hab, ha, hb⟩ := (hqH y).1 hq
    let e : Fin n → Bool := fun j => decide (j = a ∨ j = b)
    have hea : e a = true := by simp [e]
    have heb : e b = true := by simp [e]
    have hqe : qH e = true := (hqH e).2 ⟨a, b, hab, hea, heb⟩
    have hCe : C.eval (List.ofFn e) = true := by rw [hC e]; exact hqe
    have hDe := hout (fun a b => a = true → b = true) opMono_imp (fun b h => h) e ?_ hCe
    · refine hmonoDeval e y ?_ hDe
      intro j hj
      simp only [e, decide_eq_true_eq] at hj
      rcases hj with rfl | rfl
      · exact ha
      · exact hb
    · intro k hk hz hu
      have hzn := (hk2 k hk).2.2.2.1
      rw [ofFn_getD e _ hzn] at hz
      have hz' : (⟨z k, hzn⟩ : Fin n) = a ∨ (⟨z k, hzn⟩ : Fin n) = b := by
        simpa [e] using hz
      rw [hP k e]
      simp only [decide_eq_true_eq]
      rcases hz' with hza | hzb
      · refine ⟨b, heb, ?_⟩
        have hfun : (fun j1 : Fin n => decide (j1 = b ∨ (j1 : ℕ) = z k)) = e := by
          funext j
          have hj : ((j : ℕ) = z k) ↔ j = a := by
            rw [← hza, Fin.ext_iff]
          simp only [e, hj]
          exact decide_eq_decide.mpr or_comm
        rw [hfun]; exact hu
      · refine ⟨a, hea, ?_⟩
        have hfun : (fun j1 : Fin n => decide (j1 = a ∨ (j1 : ℕ) = z k)) = e := by
          funext j
          have hj : ((j : ℕ) = z k) ↔ j = b := by
            rw [← hzb, Fin.ext_iff]
          simp only [e, hj]
        rw [hfun]; exact hu
