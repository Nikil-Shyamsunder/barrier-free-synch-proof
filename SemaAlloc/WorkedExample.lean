import SemaAlloc.Main

/-! # A Worked Two-Engine Example

This example is reminiscent of Figure 8. It uses the following program.

Engine 0                Engine 1
[r̂_A := 0]              [r̂_A := 0]
loop A:                 loop A:
  [r_A++, r̂_A++]          [r_A++, r̂_A++]
  I₀  {s₀++}              [w := isGT(r̂_A, 0) * (2 * r_A)]
  I₁  {s₀++}              {s₀ >= w} I₂ {s₁++}

Both engines execute loop `A` (scope ID `0`). Engine `0` executes `I₀` and
`I₁`; engine `1` executes `I₂`, which depends on `I₁` in the same loop
iteration. We construct the specification, implementation, allocation witness,
and all static hypotheses, then apply `perScope_bisimulation`
(`workedExample_bisimulation`, line 224).
-/

namespace WorkedExample

def engines : List EngineId := [0, 1]

def block : EngineId → List DataPathInstrId
  | 0 => [0, 1]
  | 1 => [2]
  | _ => []

/-- An injective pairing function used to allocate globally unique semaphores.
`PerScopeAllocR` requires the semaphore assignment to be injective for every
`(scope, engine)` pair. This function encodes each such pair as a distinct
natural-number semaphore ID. -/
def pair : Nat → Nat → Nat
  | 0, b => 2 * b
  | a + 1, b => 2 * pair a b + 1

theorem pair_injective {a₁ b₁ a₂ b₂ : Nat}
    (h : pair a₁ b₁ = pair a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  induction a₁ generalizing a₂ b₁ b₂ with
  | zero =>
      cases a₂ with
      | zero => simp [pair] at h ⊢; omega
      | succ a₂ => simp [pair] at h; omega
  | succ a₁ ih =>
      cases a₂ with
      | zero => simp [pair] at h; omega
      | succ a₂ =>
          simp only [pair] at h
          have h' : pair a₁ b₁ = pair a₂ b₂ := by omega
          obtain ⟨rfl, rfl⟩ := ih h'
          exact ⟨rfl, rfl⟩

def scopeCode : Option ScopeId → Nat
  | none => 0
  | some scope => scope + 1

theorem scopeCode_injective {s₁ s₂ : Option ScopeId}
    (h : scopeCode s₁ = scopeCode s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> simp [scopeCode] at h ⊢
  omega

def perScopeSema (scope : Option ScopeId) (engine : EngineId) : SemaId :=
  pair (scopeCode scope) engine

theorem perScopeSema_injective {s₁ s₂ : Option ScopeId} {e₁ e₂ : EngineId}
    (h : perScopeSema s₁ e₁ = perScopeSema s₂ e₂) : s₁ = s₂ ∧ e₁ = e₂ := by
  obtain ⟨hs, he⟩ := pair_injective h
  exact ⟨scopeCode_injective hs, he⟩

/-- Register families corresponding to `r_A`, `r̂_A`, the gate, and `w`.
The residue classes modulo four make the four families disjoint. -/
def monotoneReg : EngineId → ScopeId → RegId := fun _ scope => 4 * scope
def tripReg : EngineId → ScopeId → RegId := fun _ scope => 4 * scope + 1
def gateReg : EngineId → RegId := fun _ => 2
def waitReg : EngineId → RegId := fun _ => 3

def spec : Program where
  engines := engines
  instrOp := fun _ state => state
  guard := fun _ _ _ => true
  controlOp := fun _ _ state => state
  body := [.loop 0 [.block block]]
  depGraph := fun
    | 2 => .dep 1 0
    | _ => .none

def impl : ImplProgram where
  engines := spec.engines
  instrOp := spec.instrOp
  guard := spec.guard
  controlOp := spec.controlOp
  body := [.loop 0
    [.regOp (scopeEntryOps monotoneReg tripReg [.block block] · 0),
     .block block]]
  regOps := fun engine instr =>
    wrapWithGate spec (gateReg engine) (waitReg engine) tripReg engine instr
      (perScopeExpectedRegOps spec (waitReg engine) monotoneReg engine instr)
  waitReg := fun engine _ => waitReg engine
  waitOf := fun instr => match depProducer (spec.depGraph instr) with
    | some producer => perScopeSema
        (innermostParentScope spec.engines spec.body producer)
        ((instrEngine spec.engines spec.body producer).getD 0)
    | none => 0
  updateOf := fun instr => perScopeSema
    (innermostParentScope spec.engines spec.body instr)
    ((instrEngine spec.engines spec.body instr).getD 0)

/-- The compact program expression
`w := isGT(r̂_A, 0) * (2 * r_A)` lowered to the model's primitive register
operations. Identity and subtraction-by-zero operations are retained because
the formal allocation relation specifies the unoptimized lowering. -/
example : impl.regOps 1 2 =
    [(3, 3, .const 0),
     (2, 1, .isGT 0),
     (3, 0, .id),
     (3, 3, .subConst 0),
     (3, 3, .mulConst 2),
     (3, 3, .subConst 0),
     (3, 2, .mulSrc)] := by
  simp [impl, spec, engines, block, gateReg, waitReg, tripReg, monotoneReg,
    wrapWithGate, perScopeExpectedRegOps, innermostSharedScope,
    innermostParentScope, instrInBody, findInBlock, instrEngine]
  decide

def allocation : PerScopeAllocR spec impl where
  monotoneReg := monotoneReg
  monotoneRegInj := by
    intro _ l₁ l₂ h
    change 4 * l₁ = 4 * l₂ at h
    exact Nat.mul_left_cancel (by decide) h
  tripReg := tripReg
  tripRegInj := by
    intro _ l₁ l₂ h
    change 4 * l₁ + 1 = 4 * l₂ + 1 at h
    exact Nat.mul_left_cancel (by decide) (Nat.add_right_cancel h)
  gateReg := gateReg
  waitReg := waitReg
  noClob := by
    intro _ lid
    change 3 ≠ 4 * lid
    intro h
    have hmod := congrArg (fun n => n % 4) h
    simp at hmod
  noClob_trip_wait := by
    intro _ lid
    change 3 ≠ 4 * lid + 1
    intro h
    have hmod := congrArg (fun n => n % 4) h
    simp at hmod
  noClob_trip_loop := by
    intro _ l₁ l₂
    change 4 * l₁ + 1 ≠ 4 * l₂
    intro h
    have hmod := congrArg (fun n => n % 4) h
    simp at hmod
  noClob_gate_wait := by simp [gateReg, waitReg]
  noClob_gate_loop := by
    intro _ lid
    change 2 ≠ 4 * lid
    intro h
    have hmod := congrArg (fun n => n % 4) h
    simp at hmod
  noClob_gate_trip := by
    intro _ lid
    change 2 ≠ 4 * lid + 1
    intro h
    have hmod := congrArg (fun n => n % 4) h
    simp at hmod
  waitRegEq := by simp [impl]
  baseEq := by rfl
  bodyMatch := by
    exact .loop 0 [.block block] [.block block] [] []
      (.block block [] [] .nil) .nil
  perScopeSema := perScopeSema
  perScopeSemaInj := by
    intro s₁ e₁ s₂ e₂ h
    exact perScopeSema_injective h
  updateEq := by simp [impl]
  waitOfEq := by
    intro instr
    simp only [impl]
    split <;> simp_all
  regOpsEq := by simp [impl]

theorem allocatable : Allocatable spec := by
  intro instr
  rcases instr with _ | _ | _ | instr <;>
    simp [spec, engines, block, instrInBody, findInBlock,
      innermostParentScope, innermostSharedScope]

theorem uniqueScopes : UniqueScopeIds spec.body := by
  rw [show spec.body = [.loop 0 [.block block]] from rfl]
  exact .loop 0 [.block block] []
    (by simp [scopeIdsOf])
    (by simp [scopeIdsOf])
    (by simp [scopeIdsOf])
    (.block block [] .nil)
    .nil

theorem uniqueInstructions : UniqueInstrIds spec.engines spec.body := by
  rw [show spec.engines = [0, 1] from rfl]
  rw [show spec.body = [.loop 0 [.block block]] from rfl]
  apply UniqueInstrIds.loop
  · simp [instrInBody]
  · apply UniqueInstrIds.block
    · intro engine
      rcases engine with _ | _ | engine <;> simp [block]
    · intro instr e₁ e₂ he₁ he₂ hi₁ hi₂
      simp at he₁ he₂
      rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;>
        simp [block] at hi₁ hi₂ ⊢ <;> aesop
    · simp [instrInBody]
    · exact .nil
  · exact .nil

def setup (initialData : DataPathState) (initialControl : EngineId → ControlState) :
    PerScopeBisimSetup spec where
  hWf := allocatable
  hUniq := uniqueScopes
  hUniqueInstr := uniqueInstructions
  initDataPath := initialData
  initControl := initialControl

/-- Theorem 7.1 fully instantiated for the program and allocation above.
Only values of the model's intentionally opaque initial-state types remain as
parameters. -/
theorem workedExample_bisimulation
    (initialData : DataPathState)
    (initialControl : EngineId → ControlState) :
    Bisimulation spec impl (BisimRel spec impl allocation)
      (setup initialData initialControl).specInit
      ((setup initialData initialControl).implInit impl) :=
  perScope_bisimulation spec impl allocation (setup initialData initialControl)

end WorkedExample
