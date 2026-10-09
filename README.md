A Barrier-Free Synchronization Algorithm for Multi-Engine AI Accelerators
========================================================================

Getting Started
---------------

This artifact accompanies the paper:

> Chungha Sung, Nikil V. Shyamsunder, Hanliang Zhang, Daniel Kroening, and Joonwon Choi.
> *A Barrier-Free Synchronization Algorithm for Multi-Engine AI Accelerators*.
> ACM/IEEE International Symposium on Code Generation and Optimization (CGO '27), 2027.

It contains the Lean 4 development that proves the paper's per-loop semaphore allocation correct. Every section, equation, and theorem reference below points into that paper.

This code is being released solely for academic and scientific reproducibility purposes, in support of the methods and findings described in the associated publication. Pull requests are not being accepted in order to maintain the code exactly as it was used in the paper.

### Directory Content

- `SemaAlloc`: 
  + **`Main.lean`: Definition of bisimulation and the top-level bisimulation result.**
  + `Spec.lean`: specification state and step semantics for the SCFG model
    * Note that Section 7.1 says a conditional is just "a loop of trip count 0 or 1"; for brevity of explanation in the paper, we use the word "loop" to refer to both loops and conditionals from there on. The Lean code keeps that distinction explicit by using "scope" to refer to more general structure of loops and conditionals, and `Stmt.loop/Stmt.cond` to refer to the control flow constructs. Every construct in the SCFG has `Some(sid) : Option ScopeId`, with the implicit "top-level" scope representing the program itself having value `None : Option ScopeId`.  
  + `Impl.lean`: implementation machine and inserted control / `regOp` structure 
  + `PerInstrAlloc.lean`: per-instruction allocation and wait-value computation 
  + `PerScopeAlloc.lean`: per-scope allocation (referred to as "per-loop" in the paper body) and wait-value computation 
  + `Allocatable.lean`: the supported dependency cases (Section 5.2) and the lemma that under them the monotone register equals the cumulative count of Equation (1)
  + `MatchStates.lean`: simulation relation and proof-side invariants 
  + `SpecInv.lean`: specification-side invariant machinery 
  + `PerScopeInv.lean`: per-scope bookkeeping invariants used in the bisimulation proof 
  + `Init.lean`: initial specification and implementation states, and the lemmas establishing that they are related
  + `ForwardSim.lean` and `BackwardSim.lean`: forward and backward simulation proofs 
  + `PerScopeIssue.lean`: proof that a passing semaphore check implies the dependency is satisfied, plus supporting lemmas
  + `PerScopeForwardSim.lean`, `PerScopeBackwardSim.lean`, `PerScopeInvStep.lean`, and `PerScopeLemmas.lean`: supporting proof steps and lemmas
  + `PCBound.lean`: lemmas relating a program-counter position to its index in a scope's instruction list
  + `Utilities.lean`: shared helpers
  + `WorkedExample.lean`: a two-engine, one-loop producer/consumer program and a concrete application of `perScope_bisimulation`

### Requirements

- Lean 4, version `leanprover/lean4:v4.29.0` (pinned in `lean-toolchain`)
- Lake (ships with the Lean toolchain)

If you have [`elan`](https://github.com/leanprover/elan) installed, it reads `lean-toolchain` and fetches the correct Lean version automatically; no manual version selection is needed.

**Network access.** `lake build` resolves two dependencies from GitHub at the revisions pinned in `lake-manifest.json`:

- `aesop` (`https://github.com/leanprover-community/aesop`)
- `batteries` (`https://github.com/leanprover-community/batteries`)

The first build therefore requires network access. Subsequent builds are offline, as the dependencies and build products are cached under `.lake/`.

### Build Instructions

From the repository root (the directory containing `lakefile.lean`), run:

1. `lake build`

To run the source-integrity checks and print the axioms used by the two
top-level results, run:

1. `bash scripts/check-integrity.sh`

- Tested on an Apple M1 Max and an Apple M3 Pro, both with at least 32 GB of RAM. `lake build` reports `Build completed successfully` with no errors and no warnings.

### What Is and Is Not Proved

The scope of the proof follows Sections 7.7 and 9 of the paper:

- **Proved.** The per-loop allocation (`PerScopeAllocR` in `PerScopeAlloc.lean`) is bisimilar to the specification, via `perScope_bisimulation` in `Main.lean`. The development contains no `sorry`, no `admit`, and no added axioms, so the result depends only on Lean's kernel.
- **Defined but not proved.** The per-instruction allocation (`PerInstrAlloc.lean`) is formalized because the per-loop allocation is presented as a refinement of it. As in the paper, only the per-loop allocation is proved.
- **Not modeled.** The resource optimizations of Section 6 (per-engine allocation, LICM, CSE) are outside the scope of the formalization, as Section 9 notes.
- **Trusted.** Section 7.7 lists the trusted assumptions: that the two transition systems faithfully model multi-engine execution, that the datapath, control, and allocation registers are disjoint, that `PerScopeAllocR` reflects the allocation of Section 5.5, and the syntactic hypotheses on the specification program.

### Worked Example

`SemaAlloc/WorkedExample.lean` defines a program with two engines sharing one loop. Engine `0` executes `I₀` and `I₁`; engine `1` executes `I₂`, which depends on `I₁` in the same loop iteration. The loop-entry and per-scope wait-value register operations are reminiscent of Figure 8. `WorkedExample.workedExample_bisimulation` instantiates `perScope_bisimulation` for this program. 

Proof Artifact Structure
------------------------

We provide the main correspondences between the paper and the artifact source code.

- Section 7.1 / Appendix A.1, specification state: `SpecState` `Spec.lean:336`.
  + The paper writes the state as the tuple $(\mathit{ds}, \mathit{cs}, \kappa, \mathit{ifl}, H, R)$. The Lean structure carries the same six components under the names `dataPathState`, `controlState`, `pc`, `inflight`, `scopeEntryHistory`, and `rc`; only the declaration order differs.
- Section 4.2, producer retirements and loop-entry counts: `scopeEntryHistory` `Spec.lean:346`, `totalEntries` `Spec.lean:360`, `cumExecs` `Spec.lean:370`, and `incrScopeEntryHistory` `Spec.lean:386`.
  + The Lean code specializes `H` to a single offset on the shared loop, as Appendix A.1 describes; for the shared-loop case this is equivalent to the iteration-vector presentation in the paper body.
  + The type also differs from Appendix A.1, which writes `H : EngineId -> LoopId -> Nat -> LoopId -> Nat`. The Lean version is `EngineId -> ScopeId -> Option ScopeId -> Nat -> Nat`: the arguments are reordered, and the outer scope is optional so that `none` can stand for the implicit top-level scope.
  + Read the Lean type left to right as: engine `e`, inner scope `il`, enclosing/outer scope `ol` (or `none` for top level), and entry index `k`.
- Section 4.2, Equation (1): `depSatisfied` `Spec.lean:410`.
  + The paper's Equation (1) writes the dependency check as a summation over the shared loop's entry history. As described in Appendix A.1 (see above), the Lean code specializes that to a single offset, so the summation over all iteration vectors becomes a simpler summation over one loop's history variable rather than the paper's full vector notation.
- Appendix A.2 and A.5, step rules: `SpecStep` `Spec.lean:426` (Appendix A.2) and `ImplStep` `Impl.lean:82` (Appendix A.5).
- Section 5.3, Equation (2): the masked wait-value computation in `wrapWithGate` `PerInstrAlloc.lean:101` together with `perInstrExpectedRegOps` `PerInstrAlloc.lean:11`.
- Section 5.2, The Allocatable Cases: `Allocatable` `Allocatable.lean:21`.
  + The three disjuncts correspond one-to-one with the paper's three cases: producer in $S$ at any offset, producer nested and forward at offset 0, and producer nested and backward at offset 1.
- Section 5.4, Equation (3): `PerInstrAllocR` `PerInstrAlloc.lean:127`.
- Section 5.5, Equations (4)--(5): `scopeInstrs` `PerScopeAlloc.lean:23`, `scopeRetireSum` `PerScopeAlloc.lean:78`, `perScopeExpectedRegOps` `PerScopeAlloc.lean:84`, and `PerScopeAllocR` `PerScopeAlloc.lean:118`.
- Section 7.3, the allocation relation $\mathcal{R}_{\mathrm{alloc}}$: `PerScopeAllocR` `PerScopeAlloc.lean:118`.
- Section 7.4, Theorem 7.1: `perScope_bisimulation` `Main.lean:95`, with `Bisimulation` `Main.lean:29`, `BisimRel` `Main.lean:44`, `MatchStates` `MatchStates.lean:505`, `ImplInv` `MatchStates.lean:231`, `PerScopeInv` `PerScopeInv.lean:200`, `forward_sim` `ForwardSim.lean:1186`, and `backward_sim` `BackwardSim.lean:1546`.
  + Beyond the two programs, the theorem takes two arguments. `alloc` is `PerScopeAllocR` (the paper's $\mathcal{R}_{\mathrm{alloc}}$). `hPSBS` is `PerScopeBisimSetup` `Main.lean:60`, whose `hWf`, `hUniq` and `hUniqueInstr` fields carry the other three hypotheses of Section 7.4: `Allocatable`, `UniqueScopeIds` (the paper's $\mathsf{UniqueLoopIds}$) and `UniqueInstrIds`. It also supplies the initial datapath and control states shared by both systems, through `specInit` `Main.lean:70` and `implInit` `Main.lean:74`.
  + The paper states the simulation relation as `MatchStates ∧ SpecInv ∧ ImplInv`. The proof has an extra `PerScopeInv`, which is simply extra invariants separated for organizational purposes.
- Section 7, "the register check coincides with the dependency satisfaction condition": `perScope_issue_depSat` `PerScopeIssue.lean:7`. If the implementation's semaphore check passes, `depSatisfied` holds, which is what ties Equation (5) back to Equation (1).
- Appendix A.3, implementation program components: `ImplStmt` `Impl.lean:39` with its `regOp` constructor `Impl.lean:43`, and `ImplProgram` `Impl.lean:46`.
  + The paper's Appendix A.3 describes the implementation block stream as interleaving datapath instructions and `RegOp`s. The Lean code represents this in two places: explicit `ImplStmt.regOp` statements inside block streams, and per-instruction `ImplProgram.regOps` lists that execute before the associated datapath instruction issues.
- Appendix A.4, implementation state: `ImplPC` `Impl.lean:66` and `ImplState` `Impl.lean:73`.
- Appendix A.6, initial states: the zero-initialized specification and implementation states are built from `SpecState` `Spec.lean:336` and `ImplState` `Impl.lean:73`, with the initial-state lemmas in `Init.lean`.

Security
--------

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

License
-------

This project is licensed under the Creative Commons Attribution-NonCommercial 4.0 International License. See the [LICENSE](LICENSE) file.
