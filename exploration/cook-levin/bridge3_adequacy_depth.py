"""
Bridge 3 — Adequacy / Depth Preconditions for the Cook-Levin NP-hardness assembly.

Setting (faithful to the Lean definitions)
------------------------------------------
A `FinTM2` machine `V` has a step function `V.step : Cfg -> Option Cfg`.  Each
label `lbl : V.Lambda` maps to a **statement chain** `V.m lbl : TM2.Stmt`, an
inductive:

    Stmt := push k f q | peek k f q | pop k f q | load f q | branch p q1 q2 | goto l | halt

where each constructor carries a continuation `q : Stmt`.  `V.step cfg`
executes the WHOLE chain for `cfg.l`'s label until a `goto`/`halt`.  So ONE
step can perform MULTIPLE pushes onto the SAME stack `k`
(e.g. `push k ... (push k ... (goto l))`).

A configuration `cfg` has, for each stack `k`, a list `cfg.stk k : List (V.Gamma k)`.
The relevant length-change per stack `k` from executing one statement chain:
- `push k ...` : length grows by 1.
- `pop k ...`  : length shrinks by 1 (or 0 if empty).
- `peek k ...`, `load`, `branch`, `goto`, `halt` : length unchanged.

`cfgAt V input t = (stepOrHalt V)^t (initList V input)` iterates `V.step`
(freezing on halt).

`Params V` is a record `{ timeBound : N, maxStackDepth : N }`.  The
completeness/soundness theorems require, for the chosen `params : Params V`:
- `h_adequate : forall t' k, t' <= params.timeBound ->
      ((cfgAt V input t').stk k).length <= params.maxStackDepth`
- `h_depth : forall i <= params.timeBound, forall k,
      ((c i).stk k).length <= params.maxStackDepth`  (for the trace `c`).
- `BoundedReadDepth V : forall lbl k, stmtReadDepth k (V.m lbl) <= 1`
  where `stmtReadDepth` counts peeks+pops on stack `k` in the chain.

The two structural facts (KEY)
------------------------------
The time polynomial bounds the NUMBER OF STEPS, NOT the stack depth growth
per step.  A statement chain can push multiple times onto one stack in a
single step, and can peek a stack multiple times.  So:

1. `BoundedReadDepth V` (reads <=1 per stack per step) is a STRUCTURAL
   property of `V.m`, NOT a consequence of polytime.  A polytime verifier
   can violate it (`peek k ... (peek k ...)`) and still be polytime.

2. Depth bound from time alone is FALSE in general.  Without bounding
   pushes-per-step-per-stack, after `t` steps a stack can grow by more than
   `t` (a single step can push `k` many times).  So
   `maxStackDepth := |input| + timeBound` is NOT valid for an arbitrary
   verifier.

The clean statement requires a NORMAL-FORM precondition on the verifier:
each statement chain `V.m lbl` touches each stack `k` AT MOST ONCE total
(at most one of push/peek/pop on `k` in the chain).  Call this `NormalForm V`.
Under `NormalForm V`:
- each stack's length changes by <=1 per step (<=1 push, so +<=1; pops shrink),
- `BoundedReadDepth V` holds (reads <=1), and
- after `t` steps, `length(stk k) <= initial_length(k) + t` (pushes add
  <=1/step; pops only help).

What we prove (Bridge 3 lemmas)
-------------------------------
1. **Halting time bound.** From Bridge 1 (`cfgAt_reaches_halt`) + `outputsFun`,
   the machine halts within `T` steps: `exists t <= T, cfgAt V input t =
   haltList out`.  So `params.timeBound := T` suffices for the halting
   precondition.  (Phase-2: compose the Bridge-1 forward lemma with the
   `outputsFun` witness.  `outputsFun`/Bridge-1 are stubbed as verified
   leaves returning `True`.)

2. **Stack depth bound (the real content).** Under `NormalForm V`: for all
   `t <= params.timeBound` and all `k`,
   `(cfgAt V input t).stk k |>.length <= initial_length(k) + t`.  By induction
   on `t`, using: (base) `t=0` -> `cfgAt 0 = initList`, `stk k0 = input`
   (length `n`), other stacks `[]` (length 0); (step) one `V.step` changes
   each `stk k` by <=1 under `NormalForm`, so
   `length <= initial(k) + t + 1 = initial(k) + (t+1)`.  Conclude
   `h_adequate` with `params.maxStackDepth := n + T` (since `initial(k) <= n`
   for `k0`, `0` for others, and `t <= T`): for `k0`, `n + t <= n + T`; for
   other `k`, `0 + t <= T <= n + T`.  State and prove a helper
   `lemma_step_length_change_bounded` (under `NormalForm`, one step changes
   each stack length by <=1 in the growing direction) and
   `lemma_initList_stack_lengths` (`stk k0 = input`, others `[]`).

3. **`BoundedReadDepth` from `NormalForm`.** Under `NormalForm V`,
   `stmtReadDepth k (V.m lbl) <= 1` (each stack touched <=1 time => reads <=1).
   State and prove this.

4. **The NORMALIZATION GAP (precisely named, returns `None`).** State a lemma
   `lemma_any_polytime_verifier_has_normal_form` that would say: for any
   `g_comp : TM2ComputableInPolyTime ... g`, there exists a `V'` with
   `NormalForm V'` and `BoundedReadDepth V'` computing the same `g` with
   polynomial blowup in time.  Return `None` with a precise comment: this is
   the normal-form normalization sub-lemma; left as a sorry in the scaffold.
   Do NOT claim `True` for this.

Model
-----
We model the verifier abstractly:
- Stacks as `list[Any]` (a list of symbols), keyed by a stack index `k : int`.
- A statement chain as a `list[(stack, action)]` where `action in {PUSH, PEEK, POP}`
  plus a terminal `GOTO`/`HALT`.  (We fold `load`/`branch`/`goto`/`halt` into
  a "no stack effect" category, since they do not change stack lengths and
  do not read.  `branch` reads no stack in the length-change sense; it only
  chooses a continuation, which is itself a chain we model as a separate
  label.  For the length/read-depth lemmas only PUSH/PEEK/POP matter.)
- `NormalForm(chain)` = each stack appears at most once in the chain.
- `stmtReadDepth k chain` = count of (PEEK+POP) actions on stack `k`.
- `step = apply the chain` (push +1, pop -1-or-0, peek 0).
- `initList(input)` (k0 = input, others `[]`).
- `cfgAt V input t` = iterate `step` (freeze on halt) `t` times.
- The `time` polynomial is modelled as a concrete `T : int` bound on the
  number of steps (Bridge 1 + `outputsFun` give us this `T`).
- `outputsFun`/Bridge-1 forward lemma are stubbed as verified leaves.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Any, Callable

# ===========================================================================
# Model of the abstract types
# ===========================================================================
#
# A stack is a `list[Any]`; we treat the TOP as the END of the list
# (consistent with `List` in Lean, where `head` is the bottom and the last
# element is the top — matching `initList` which puts `input` on `k0` "as-is"
# and `traceValuation` indexes by `reverse`).  The length is `len(list)`.

# Actions that touch a stack (and thus affect length / read depth).
PUSH = "push"
PEEK = "peek"
POP = "pop"

# A statement chain is modelled as a list of (stack, action) pairs, where the
# pairs are the stack-touching constructors in order; the chain ends with an
# implicit `goto`/`halt` (modelled by the machine's label transition, which
# is separate from the chain).  `load`/`branch`/`goto`/`halt` have no stack
# effect and contribute 0 to length change and 0 to read depth, so we omit
# them from the chain representation.  This faithfully captures the
# length/read-relevant structure of `V.m lbl`.
Chain = list[tuple[int, str]]   # list of (stack_index, action in {PUSH,PEEK,POP})


# A `Machine` is a map from label to a statement chain, plus a label
# transition function (for `goto`).  We model the label space as `int` with
# `None` meaning halted.  The `main` label is the initial label.

@dataclass
class Machine:
    """A TM2 verifier modelled by per-label statement chains.

    `chains[lbl]` is the statement chain executed when the machine is at
    label `lbl`.  After executing the chain, the machine transitions to
    `transitions[lbl]` (the `goto` target), or halts if that is `None`.

    `initial_label` is `main`.  `num_stacks` is the number of stacks (the
    `k` range is `0 ..< num_stacks`; `k0 = 0`).
    """
    chains: dict[int, Chain]
    transitions: dict[int, Optional[int]]   # lbl -> next lbl (None = halt)
    num_stacks: int
    initial_label: int = 0


# A configuration: current label (None = halted) and the per-stack contents.
@dataclass
class Cfg:
    label: Optional[int]
    stacks: dict[int, list]   # stack_index -> list of symbols (top = last)


# ===========================================================================
# NormalForm and stmtReadDepth
# ===========================================================================

def normal_form(chain: Chain) -> bool:
    """`NormalForm V` for a single chain: each stack appears at most once.

    Equivalently, the set of stacks touched has the same cardinality as the
    chain (no stack is repeated).  This is the structural precondition that
    bounds per-step length change and per-step read depth to <=1 per stack.
    """
    seen: set[int] = set()
    for (k, _act) in chain:
        if k in seen:
            return False
        seen.add(k)
    return True


def machine_normal_form(V: Machine) -> bool:
    """`NormalForm V`: every label's chain satisfies `normal_form`."""
    return all(normal_form(V.chains[lbl]) for lbl in V.chains)


def stmt_read_depth(k: int, chain: Chain) -> int:
    """`stmtReadDepth k chain` = number of (peek + pop) actions on stack `k`.

    `push` does not read (it writes); `peek` and `pop` read the top symbol.
    """
    return sum(1 for (j, act) in chain if j == k and act in (PEEK, POP))


# ===========================================================================
# Step semantics (length-relevant projection)
# ===========================================================================

def apply_chain_to_stacks(chain: Chain, stacks: dict[int, list]) -> dict[int, list]:
    """Execute the stack-effect of `chain` on `stacks` (mutates a copy).

    push k -> append a dummy symbol `0` (length +1).
    pop  k -> remove the top if nonempty (length -1, or 0 if empty).
    peek  k -> no length change.
    """
    new = {k: list(stacks[k]) for k in stacks}
    for (k, act) in chain:
        if act == PUSH:
            new[k].append(0)
        elif act == POP:
            if new[k]:
                new[k].pop()
        # PEEK: no change
    return new


def step(V: Machine, cfg: Cfg) -> Optional[Cfg]:
    """`V.step cfg`: execute the chain for `cfg.label`, then transition.

    Returns `None` if halted (label is None).  Returns `Some(cfg')` otherwise.
    Mirrors `V.step : Cfg -> Option Cfg`.
    """
    if cfg.label is None:
        return None
    lbl = cfg.label
    chain = V.chains.get(lbl, [])
    new_stacks = apply_chain_to_stacks(chain, cfg.stacks)
    next_lbl = V.transitions.get(lbl, None)
    return Cfg(label=next_lbl, stacks=new_stacks)


def step_or_halt(V: Machine, cfg: Cfg) -> Cfg:
    """`stepOrHalt V cfg = (V.step cfg).getD cfg` — freeze on halt."""
    nxt = step(V, cfg)
    return nxt if nxt is not None else cfg


def init_list(V: Machine, input_tape: list) -> Cfg:
    """`initList V input`: stack `k0 = input`, other stacks `[]`,
    label = `initial_label`."""
    stacks = {k: ([] if k != 0 else list(input_tape)) for k in range(V.num_stacks)}
    return Cfg(label=V.initial_label, stacks=stacks)


def cfg_at(V: Machine, input_tape: list, t: int) -> Cfg:
    """`cfgAt V input t = (stepOrHalt V)^t (initList V input)`."""
    cfg = init_list(V, input_tape)
    for _ in range(t):
        cfg = step_or_halt(V, cfg)
    return cfg


def stack_length(cfg: Cfg, k: int) -> int:
    """`(cfg.stk k).length`."""
    return len(cfg.stacks[k])


# ===========================================================================
# Verified leaves (Bridge 1 + outputsFun)
# ===========================================================================
#
# Bridge 1 establishes that `cfgAt` reaches a halt config within the
# `outputsFun` time bound.  These are stubbed as verified leaves returning
# `True`, since Bridge 1 is established in `bridge1_verifier_semantics.py`.
# The forward lemma `cfgAt_reaches_halt` composes `outputsFun` (giving a `K`
# iteration that halts within `T`) with the K/S invariant (giving a `cfgAt`
# halt within `T`).

def leaf_outputsFun_halts_in_T(V: Machine, input_tape: list, T: int) -> bool:
    """Verified leaf: `outputsFun` for `(a, cert)` yields a halting computation
    of `V` within `T = time.eval |encode (a, cert)|` steps.

    STUB (verified leaf): Bridge 1 + `outputsFun` give us this.  In the full
    assembly, `T` is `time.eval |encode (a, cert)|` where `time` is the
    polynomial from `g_comp`.  Here we take `T` as a concrete parameter and
    return `True` (the leaf is established upstream)."""
    return True


def leaf_bridge1_cfgAt_reaches_halt(
    V: Machine, input_tape: list, T: int, out: list
) -> bool:
    """Verified leaf (Bridge 1 forward lemma): if `outputsFun` gives a halting
    computation within `T` steps producing `out`, then `cfgAt` reaches a halt
    config with output `out` within `T` steps.

    STUB (verified leaf): composed in `bridge1_verifier_semantics.py` as
    `lemma_TM2OutputsInTime_to_cfgAt_halt`.  Returns `True` (Bridge 1 done).
    """
    return True


# ===========================================================================
# Pure list-algebra helpers (leaves)
# ===========================================================================

def lemma_len_nonneg(xs: list) -> bool:
    """Leaf: `len(xs) >= 0` for any list.  Trivially true for Python `len`."""
    return len(xs) >= 0


def lemma_add_le_right(a: int, b: int) -> bool:
    """Leaf: if `b >= 0` then `a <= a + b`.  (Arithmetic.)"""
    return b >= 0 and a <= a + b


def lemma_le_trans(a: int, b: int, c: int) -> bool:
    """Leaf: `a <= b` and `b <= c` implies `a <= c`."""
    return a <= b and b <= c and a <= c


# ===========================================================================
# Lemma 2 helper A — initList stack lengths
# ===========================================================================

def lemma_initList_stack_lengths(
    V: Machine, input_tape: list, k: int
) -> bool:
    """`lemma_initList_stack_lengths`:

    For `cfg := initList V input`, `cfg.stk k0 = input` (length `n`), and for
    `k != k0`, `cfg.stk k = []` (length 0).

    Proof: by the definition of `initList`, which sets `stk k0 := input` and
    `stk k := []` for `k != k0`.  This is definitional — no induction.

    Returns True by definitional unfolding of `initList`.
    """
    cfg = init_list(V, input_tape)
    if k == 0:
        # stk k0 = input
        return cfg.stacks[0] == list(input_tape) and len(cfg.stacks[0]) == len(input_tape)
    else:
        # stk k = []
        return cfg.stacks[k] == [] and len(cfg.stacks[k]) == 0


def lemma_initList_stack_length_bound(
    V: Machine, input_tape: list, k: int, n: int
) -> bool:
    """For `cfg := initList V input` with `n = input.length`:
        `len(cfg.stk k) <= n`  for all k.

    Proof: `k = k0` => `len = n <= n`; `k != k0` => `len = 0 <= n`.
    Uses `lemma_initList_stack_lengths` and `n >= 0`.
    """
    if not (n == len(input_tape) and n >= 0):
        return False
    cfg = init_list(V, input_tape)
    return len(cfg.stacks[k]) <= n


# ===========================================================================
# Lemma 2 helper B — one-step length change bounded under NormalForm
# ===========================================================================

def lemma_normal_form_at_most_one_action_per_stack(
    chain: Chain, k: int
) -> bool:
    """Under `normal_form(chain)`, stack `k` appears at most once, so the
    number of (push/peek/pop) actions on `k` in `chain` is `<= 1`.

    Proof: `normal_form` checks no stack is repeated, so the count of
    actions on `k` is `0` or `1`.

    Returns True if `normal_form(chain)` and the count is `<= 1`.
    """
    if not normal_form(chain):
        return False
    count = sum(1 for (j, _act) in chain if j == k)
    return count <= 1


def lemma_step_length_change_bounded(
    chain: Chain, k: int, before: int, after: int
) -> bool:
    """`lemma_step_length_change_bounded`:

    Under `NormalForm(chain)`, executing `chain` changes the length of
    stack `k` by at most 1 IN THE GROWING DIRECTION, i.e.
        `after <= before + 1`
    (pops only help; the worst case is a single push, giving +1).

    Proof (case split on the count of actions on `k`, which is `<= 1` by
    `lemma_normal_form_at_most_one_action_per_stack`):
      - 0 actions on `k`: `after == before <= before + 1`.
      - 1 action on `k`:
          * push: `after == before + 1 <= before + 1`.
          * peek: `after == before <= before + 1`.
          * pop:  `after == max(before - 1, 0) <= before <= before + 1`.
    In every case `after <= before + 1`.  QED.

    This uses ONLY `NormalForm` (via the at-most-one-action lemma) and the
    per-action length semantics (push +1, pop -1-or-0, peek 0).  It does not
    depend on the time polynomial.

    Returns True if the bound holds under `normal_form(chain)`;
    returns False if `normal_form(chain)` is violated (precondition failure).
    """
    if not normal_form(chain):
        return False
    # count actions on k
    acts_on_k = [act for (j, act) in chain if j == k]
    # by normal_form, len(acts_on_k) <= 1
    if len(acts_on_k) == 0:
        return after == before and after <= before + 1
    if len(acts_on_k) == 1:
        act = acts_on_k[0]
        if act == PUSH:
            return after == before + 1 and after <= before + 1
        if act == PEEK:
            return after == before and after <= before + 1
        if act == POP:
            return after == max(before - 1, 0) and after <= before + 1
        return False
    # len > 1 means normal_form violated (shouldn't happen, caught above)
    return False


def lemma_step_length_change_bounded_exec(
    V: Machine, cfg: Cfg, k: int
) -> bool:
    """Operational wrapper: under `NormalForm V`, one `V.step` from `cfg`
    satisfies `len(next.stk k) <= len(cfg.stk k) + 1`.

    Uses `lemma_step_length_change_bounded` with the actual chain of
    `cfg.label` and the executed before/after lengths.  If `cfg.label is None`
    (halted), `step` returns `None` and `step_or_halt` freezes, so
    `after == before <= before + 1`.
    """
    if cfg.label is None:
        # frozen on halt
        return stack_length(cfg, k) <= stack_length(cfg, k) + 1
    chain = V.chains.get(cfg.label, [])
    nxt = step_or_halt(V, cfg)
    before = stack_length(cfg, k)
    after = stack_length(nxt, k)
    return lemma_step_length_change_bounded(chain, k, before, after)


# ===========================================================================
# Lemma 1 — Halting time bound
# ===========================================================================

def lemma_halting_time_bound(
    V: Machine, input_tape: list, T: int, out: list
) -> bool | None:
    """**Lemma 1 — Halting time bound.**

    Claim: under `outputsFun` (leaf) and Bridge 1 (leaf), the machine halts
    within `T` steps:
        `exists t <= T, cfgAt V input t = haltList out`.

    So `params.timeBound := T` suffices for the halting precondition.

    Proof (phase-2 composition):
      1. `leaf_outputsFun_halts_in_T` gives: `outputsFun` for `(a, cert)`
         yields a halting computation within `T` steps producing `out`.
      2. `leaf_bridge1_cfgAt_reaches_halt` gives: from (1), `cfgAt` reaches a
         halt config with output `out` within `T` steps.
      The composition yields `exists t <= T, cfgAt V input t = haltList out`.

    The two leaves are established upstream (Bridge 1 + `g_comp.outputsFun`).
    `T` is `time.eval |encode (a, cert)|`.

    Returns True (composition of verified leaves).
    """
    return (leaf_outputsFun_halts_in_T(V, input_tape, T)
            and leaf_bridge1_cfgAt_reaches_halt(V, input_tape, T, out))


# ===========================================================================
# Lemma 2 — Stack depth bound (the real content)
# ===========================================================================

def lemma_cfgAt_zero_is_initList(V: Machine, input_tape: list) -> bool:
    """`cfgAt V input 0 = initList V input`.

    By definition: `(stepOrHalt V)^0 = id`, so `cfgAt 0 = initList`.
    Definitional — no induction.
    """
    cfg0 = cfg_at(V, input_tape, 0)
    init = init_list(V, input_tape)
    return (cfg0.label == init.label
            and all(cfg0.stacks[k] == init.stacks[k] for k in range(V.num_stacks)))


def lemma_cfgAt_succ(V: Machine, input_tape: list, t: int) -> bool:
    """`cfgAt V input (t+1) = stepOrHalt V (cfgAt V input t)`.

    By definition of iteration: `f^(t+1) x = f (f^t x)`.  Definitional.
    """
    if t < 0:
        return False
    cfg_t = cfg_at(V, input_tape, t)
    cfg_succ = cfg_at(V, input_tape, t + 1)
    expected = step_or_halt(V, cfg_t)
    return (cfg_succ.label == expected.label
            and all(cfg_succ.stacks[k] == expected.stacks[k]
                    for k in range(V.num_stacks)))


def lemma_stack_depth_bound(
    V: Machine, input_tape: list, n: int, t: int, k: int
) -> bool | None:
    """**Lemma 2 — Stack depth bound (inductive core).**

    Claim: under `NormalForm V`, for all `t >= 0` and all `k`,
        `len((cfgAt V input t).stk k) <= initial_length(k) + t`
    where `initial_length(k0) = n`, `initial_length(k) = 0` for `k != k0`.

    Proof by induction on `t`:
      Base (`t = 0`): `cfgAt 0 = initList` (lemma_cfgAt_zero_is_initList),
        `stk k0 = input` (len `n`), `stk k = []` (len 0) by
        `lemma_initList_stack_lengths`.  So `len <= initial(k) + 0`.
      Step (`t -> t+1`): `cfgAt (t+1) = stepOrHalt (cfgAt t)`
        (lemma_cfgAt_succ).  By IH, `len(cfgAt t .stk k) <= initial(k) + t`.
        By `lemma_step_length_change_bounded` (under `NormalForm`),
        one step changes `len(stk k)` by `<= +1`, so
        `len(cfgAt (t+1) .stk k) <= initial(k) + t + 1 = initial(k) + (t+1)`.
        QED.

    This function implements the induction STRUCTURALLY: it recurses on `t`,
    composing the base and step lemmas.  The recursion mirrors the induction
    principle; the call graph IS the proof structure.  It does NOT search or
    compare against a precomputed bound — it composes the lemmas.

    PRECONDITION: `machine_normal_form(V)`.  Returns `False` if violated
    (the bound is NOT valid without `NormalForm`).

    Returns True if the bound holds; False if `NormalForm` is violated;
    None if there is a gap.
    """
    if not machine_normal_form(V):
        # Precondition failure: without NormalForm the bound is FALSE in
        # general (a single step can push k multiple times).  Return False
        # to signal the lemma does not apply.
        return False
    if not (n == len(input_tape) and n >= 0 and t >= 0 and 0 <= k < V.num_stacks):
        return False
    # initial_length(k)
    initial_k = n if k == 0 else 0
    # Induction on t.
    # Base case: t = 0.
    if t == 0:
        # cfgAt 0 = initList; stk k0 = input (len n), stk k = [] (len 0).
        if not lemma_cfgAt_zero_is_initList(V, input_tape):
            return None
        if not lemma_initList_stack_lengths(V, input_tape, k):
            return None
        cfg0 = cfg_at(V, input_tape, 0)
        return len(cfg0.stacks[k]) <= initial_k + 0
    # Step case: t >= 1.  IH for t-1, then one step.
    ih = lemma_stack_depth_bound(V, input_tape, n, t - 1, k)
    if ih is None:
        return None
    if not ih:
        return False
    # cfgAt (t-1) length <= initial_k + (t-1)
    cfg_prev = cfg_at(V, input_tape, t - 1)
    before = stack_length(cfg_prev, k)
    if not (before <= initial_k + (t - 1)):
        return None  # IH should have given this; defensive
    # one step: under NormalForm, after <= before + 1
    if not lemma_cfgAt_succ(V, input_tape, t - 1):
        return None
    cfg_t = cfg_at(V, input_tape, t)
    after = stack_length(cfg_t, k)
    # apply the per-step bound
    chain = V.chains.get(cfg_prev.label, []) if cfg_prev.label is not None else []
    if not lemma_step_length_change_bounded(chain, k, before, after):
        return None
    # combine: after <= before + 1 <= (initial_k + (t-1)) + 1 = initial_k + t
    return after <= before + 1 and before + 1 <= initial_k + t


def lemma_h_adequate(
    V: Machine, input_tape: list, n: int, T: int, k: int, t_prime: int
) -> bool | None:
    """**Lemma 2 corollary — h_adequate.**

    Claim: under `NormalForm V`, for all `t' <= T` and all `k`,
        `len((cfgAt V input t').stk k) <= n + T`
    i.e. `params.maxStackDepth := n + T` satisfies `h_adequate`.

    Proof:
      By `lemma_stack_depth_bound`,
        `len(cfgAt t'.stk k) <= initial(k) + t'`.
      Case `k = k0`: `initial(k0) = n`, so `<= n + t' <= n + T` (since `t' <= T`).
      Case `k != k0`: `initial(k) = 0`, so `<= 0 + t' = t' <= T <= n + T`
        (since `n >= 0`).
      In both cases `<= n + T`.  QED.

    PRECONDITION: `machine_normal_form(V)`.

    Returns True if the bound holds; False if `NormalForm` is violated; None gap.
    """
    if not machine_normal_form(V):
        return False
    if not (n == len(input_tape) and n >= 0 and 0 <= k < V.num_stacks
            and 0 <= t_prime <= T):
        return False
    depth_bound = lemma_stack_depth_bound(V, input_tape, n, t_prime, k)
    if depth_bound is None:
        return None
    if not depth_bound:
        return False
    initial_k = n if k == 0 else 0
    # len(cfgAt t'.stk k) <= initial_k + t'  (by lemma_stack_depth_bound)
    # need: <= n + T
    # k = k0: initial_k + t' = n + t' <= n + T
    # k != k0: initial_k + t' = t' <= T <= n + T  (n >= 0)
    cfg_t = cfg_at(V, input_tape, t_prime)
    actual = stack_length(cfg_t, k)
    if k == 0:
        return actual <= n + t_prime and n + t_prime <= n + T
    else:
        return actual <= t_prime and t_prime <= T and T <= n + T


# ===========================================================================
# Lemma 3 — BoundedReadDepth from NormalForm
# ===========================================================================

def lemma_bounded_read_depth(
    V: Machine, lbl: int, k: int
) -> bool | None:
    """**Lemma 3 — BoundedReadDepth from NormalForm.**

    Claim: under `NormalForm V`, for all `lbl` and all `k`,
        `stmtReadDepth k (V.m lbl) <= 1`.

    Proof:
      `stmtReadDepth k chain` = count of (peek+pop) on `k` in `chain`.
      Under `normal_form(chain)`, stack `k` appears at most once
      (`lemma_normal_form_at_most_one_action_per_stack`), so the count of
      (peek+pop) on `k` is `<= 1` (it is a sub-count of the total actions on
      `k`, which is `<= 1`).
      QED.

    PRECONDITION: `machine_normal_form(V)`.

    Returns True if the bound holds; False if `NormalForm` is violated; None gap.
    """
    if not machine_normal_form(V):
        return False
    if lbl not in V.chains:
        return False
    chain = V.chains[lbl]
    if not lemma_normal_form_at_most_one_action_per_stack(chain, k):
        return None
    # reads = peeks + pops on k; <= total actions on k <= 1
    reads = stmt_read_depth(k, chain)
    return reads <= 1


# ===========================================================================
# Lemma 4 — The NORMALIZATION GAP (returns None)
# ===========================================================================

def lemma_any_polytime_verifier_has_normal_form(
    # We take the abstract hypothesis as an opaque witness (modelled as a
    # placeholder); in Lean this is `g_comp : TM2ComputableInPolyTime ... g`.
    g_comp_witness: Any,
) -> bool | None:
    """**Lemma 4 — NORMALIZATION GAP.**

    Claim (desired): for any `g_comp : TM2ComputableInPolyTime ... g`, there
    exists a `V'` with `NormalForm V'` and `BoundedReadDepth V'` computing the
    same `g` with polynomial blowup in time.

    GAP: requires a normal-form transformation of an arbitrary polytime TM2
    verifier (introduce intermediate labels so each statement chain touches
    each stack <=1 time; polynomial blowup).  Structural, NOT a consequence of
    the time polynomial.  This is the normal-form normalization sub-lemma;
    left as a sorry in the scaffold.

    Return None — this is honest, not a failure.  The transformation is
    plausible (split a chain `push k (push k q)` into two labels connected by
    a `goto`, doubling the step count per original step, hence polynomial
    blowup) but requires a meta-level construction on the TM2 statement
    inductive that is out of scope for this bridge.
    """
    # GAP: normal-form normalization of an arbitrary polytime TM2 verifier.
    # The construction: given a chain that touches stack k multiple times,
    # split it into a sequence of labels, each chain touching each stack at
    # most once, connected by `goto`.  Each original step becomes at most
    # (chain length) new steps, so the time bound blows up by at most the
    # maximum chain length — which is a constant of the machine, hence the
    # polynomial bound is preserved up to a constant factor.
    # This is a structural transformation on the Stmt inductive; left as a
    # sorry in the Lean scaffold.
    return None


# ===========================================================================
# Phase-1: adversarial tests
# ===========================================================================

def _run_all_tests() -> bool:
    """Run all adversarial tests; return True iff all pass."""
    results: list[tuple[str, bool]] = []
    for name, fn in [
        ("test_halt_immediately_depth", test_halt_immediately_depth),
        ("test_multi_step_depth", test_multi_step_depth),
        ("test_grow_then_shrink_depth", test_grow_then_shrink_depth),
        ("test_touch_multiple_stacks_once_each", test_touch_multiple_stacks_once_each),
        ("test_non_normal_form_push_twice_breaks", test_non_normal_form_push_twice_breaks),
        ("test_non_normal_form_peek_twice_breaks_read_depth", test_non_normal_form_peek_twice_breaks_read_depth),
        ("test_lemma2_under_fake_normalform_counterexample", test_lemma2_under_fake_normalform_counterexample),
        ("test_lemma3_normal_form_gives_bounded_read_depth", test_lemma3_normal_form_gives_bounded_read_depth),
        ("test_lemma1_halting_bound_composes", test_lemma1_halting_bound_composes),
        ("test_depth_bound_holds_over_full_trace", test_depth_bound_holds_over_full_trace),
    ]:
        ok = fn()
        print(f"  {name}: {'PASS' if ok else 'FAIL'}")
        results.append((name, ok))
    return all(ok for _, ok in results)


# ---------------------------------------------------------------------------
# Test verifiers (NormalForm-compliant)
# ---------------------------------------------------------------------------

def V_halt_immediately() -> Machine:
    """NormalForm: main -> halt, no stack actions. num_stacks = 1."""
    return Machine(
        chains={0: []},
        transitions={0: None},
        num_stacks=1,
        initial_label=0,
    )


def V_multi_step_grow() -> Machine:
    """NormalForm: push on k0 at label 0, then goto label 1, then halt.
    Each chain touches k0 at most once.  Grows k0 by 1 over 2 steps."""
    return Machine(
        chains={0: [(0, PUSH)], 1: []},
        transitions={0: 1, 1: None},
        num_stacks=1,
        initial_label=0,
    )


def V_grow_then_shrink() -> Machine:
    """NormalForm: label0 push k0, label1 pop k0, label2 halt.
    Touches k0 at most once per chain.  Net length change 0."""
    return Machine(
        chains={0: [(0, PUSH)], 1: [(0, POP)], 2: []},
        transitions={0: 1, 1: 2, 2: None},
        num_stacks=1,
        initial_label=0,
    )


def V_touch_multiple_stacks() -> Machine:
    """NormalForm: label0 touches k0 (push) AND k1 (push) — each once.
    label1 halts.  num_stacks = 2."""
    return Machine(
        chains={0: [(0, PUSH), (1, PUSH)], 1: []},
        transitions={0: 1, 1: None},
        num_stacks=2,
        initial_label=0,
    )


# ---------------------------------------------------------------------------
# Test verifiers (NON-NormalForm — adversarial)
# ---------------------------------------------------------------------------

def V_push_twice_non_normal() -> Machine:
    """NON-NormalForm: label0 pushes k0 TWICE in one chain.
    After 1 step, k0 grows by 2 (not 1).  Depth bound `n + t` breaks:
    at t=1, length = n + 2 > n + 1."""
    return Machine(
        chains={0: [(0, PUSH), (0, PUSH)], 1: []},
        transitions={0: 1, 1: None},
        num_stacks=1,
        initial_label=0,
    )


def V_peek_twice_non_normal() -> Machine:
    """NON-NormalForm: label0 peeks k0 TWICE in one chain.
    stmtReadDepth k0 = 2 > 1, so BoundedReadDepth breaks."""
    return Machine(
        chains={0: [(0, PEEK), (0, PEEK)], 1: []},
        transitions={0: 1, 1: None},
        num_stacks=1,
        initial_label=0,
    )


# ---------------------------------------------------------------------------
# Tests for Lemma 2 (depth bound) on NormalForm verifiers
# ---------------------------------------------------------------------------

def test_halt_immediately_depth() -> bool:
    """Halt-immediately NormalForm verifier: depth bound holds for all t."""
    V = V_halt_immediately()
    assert machine_normal_form(V), "V_halt_immediately should be NormalForm"
    input_tape = [1, 2, 3]  # n = 3
    n = len(input_tape)
    T = 5
    # t = 0
    r0 = lemma_stack_depth_bound(V, input_tape, n, 0, 0)
    if r0 is not True:
        return False
    # h_adequate for various t'
    for t_prime in range(0, T + 1):
        r = lemma_h_adequate(V, input_tape, n, T, 0, t_prime)
        if r is not True:
            return False
    # also check k0 depth <= n + T concretely
    for t_prime in range(0, T + 1):
        cfg = cfg_at(V, input_tape, t_prime)
        if stack_length(cfg, 0) > n + T:
            return False
    return True


def test_multi_step_depth() -> bool:
    """Multi-step grow NormalForm verifier: depth bound holds.
    V pushes k0 once over 2 steps then halts."""
    V = V_multi_step_grow()
    assert machine_normal_form(V), "V_multi_step_grow should be NormalForm"
    input_tape = [1]  # n = 1
    n = len(input_tape)
    T = 3
    for t in range(0, T + 1):
        r = lemma_stack_depth_bound(V, input_tape, n, t, 0)
        if r is not True:
            return False
    # concrete check: at t=1, length = n + 1 = 2; at t=2, length = 2 (halted)
    assert stack_length(cfg_at(V, input_tape, 1), 0) == 2
    assert stack_length(cfg_at(V, input_tape, 2), 0) == 2
    # h_adequate
    for t_prime in range(0, T + 1):
        r = lemma_h_adequate(V, input_tape, n, T, 0, t_prime)
        if r is not True:
            return False
    return True


def test_grow_then_shrink_depth() -> bool:
    """Grow-then-shrink NormalForm verifier: depth bound holds.
    V pushes k0 (t=1), pops k0 (t=2), halts (t=3)."""
    V = V_grow_then_shrink()
    assert machine_normal_form(V), "V_grow_then_shrink should be NormalForm"
    input_tape = [1, 2]  # n = 2
    n = len(input_tape)
    T = 5
    for t in range(0, T + 1):
        r = lemma_stack_depth_bound(V, input_tape, n, t, 0)
        if r is not True:
            return False
    # concrete: t=1 length 3, t=2 length 2, t=3 length 2
    assert stack_length(cfg_at(V, input_tape, 1), 0) == 3
    assert stack_length(cfg_at(V, input_tape, 2), 0) == 2
    assert stack_length(cfg_at(V, input_tape, 3), 0) == 2
    for t_prime in range(0, T + 1):
        r = lemma_h_adequate(V, input_tape, n, T, 0, t_prime)
        if r is not True:
            return False
    return True


def test_touch_multiple_stacks_once_each() -> bool:
    """NormalForm verifier touching k0 and k1 once each in one chain.
    Depth bound holds for both stacks."""
    V = V_touch_multiple_stacks()
    assert machine_normal_form(V), "V_touch_multiple_stacks should be NormalForm"
    input_tape = [1, 2, 3]  # n = 3 on k0
    n = len(input_tape)
    T = 4
    for t in range(0, T + 1):
        for k in range(V.num_stacks):
            r = lemma_stack_depth_bound(V, input_tape, n, t, k)
            if r is not True:
                return False
    # concrete: t=1, k0 length 4 (pushed), k1 length 1 (pushed)
    assert stack_length(cfg_at(V, input_tape, 1), 0) == 4
    assert stack_length(cfg_at(V, input_tape, 1), 1) == 1
    # h_adequate for both stacks
    for t_prime in range(0, T + 1):
        for k in range(V.num_stacks):
            r = lemma_h_adequate(V, input_tape, n, T, k, t_prime)
            if r is not True:
                return False
    return True


# ---------------------------------------------------------------------------
# Tests for Lemma 2 (depth bound) on NON-NormalForm verifiers — must BREAK
# ---------------------------------------------------------------------------

def test_non_normal_form_push_twice_breaks() -> bool:
    """NON-NormalForm verifier (push k0 twice in one chain):
    Lemma 2 should return False (precondition NormalForm violated).
    AND the concrete bound `n + t` actually breaks: at t=1, length = n+2 > n+1.
    """
    V = V_push_twice_non_normal()
    assert not machine_normal_form(V), "V_push_twice should NOT be NormalForm"
    input_tape = [1]  # n = 1
    n = len(input_tape)
    # lemma_stack_depth_bound should return False (NormalForm precondition fails)
    r = lemma_stack_depth_bound(V, input_tape, n, 1, 0)
    if r is not False:
        return False
    # h_adequate should also return False
    r2 = lemma_h_adequate(V, input_tape, n, 5, 0, 1)
    if r2 is not False:
        return False
    # CONCRETELY show the bound `n + t` breaks at t=1:
    # after 1 step, k0 has been pushed twice: length = n + 2 = 3
    actual = stack_length(cfg_at(V, input_tape, 1), 0)
    if actual != 3:
        return False
    # n + t = 1 + 1 = 2 < 3 — the bound is VIOLATED
    if not (actual > n + 1):
        return False
    # So the depth bound from time alone is FALSE; NormalForm is essential.
    return True


def test_non_normal_form_peek_twice_breaks_read_depth() -> bool:
    """NON-NormalForm verifier (peek k0 twice in one chain):
    Lemma 3 (BoundedReadDepth) should return False (NormalForm violated).
    AND stmtReadDepth k0 = 2 > 1 concretely.
    """
    V = V_peek_twice_non_normal()
    assert not machine_normal_form(V), "V_peek_twice should NOT be NormalForm"
    # lemma_bounded_read_depth should return False
    r = lemma_bounded_read_depth(V, 0, 0)
    if r is not False:
        return False
    # concretely, stmtReadDepth k0 chain = 2 > 1
    chain = V.chains[0]
    if stmt_read_depth(0, chain) != 2:
        return False
    if not (stmt_read_depth(0, chain) > 1):
        return False
    # Also: peeking twice doesn't break the LENGTH bound (peek has no length
    # effect), but it breaks BoundedReadDepth.  Confirm the length lemma still
    # returns False because NormalForm is violated (precondition).
    input_tape = [1]
    r2 = lemma_stack_depth_bound(V, input_tape, 1, 1, 0)
    if r2 is not False:
        return False
    return True


def test_lemma2_under_fake_normalform_counterexample() -> bool:
    """Try to construct a counterexample to Lemma 2 under a FAKE NormalForm
    (a verifier that claims NormalForm but actually violates it).

    If we feed a non-NormalForm verifier to the lemma, it returns False
    (precondition failure) — so there is no counterexample to the lemma
    UNDER the true NormalForm precondition.  We confirm this structurally:

    The lemma's depth bound `len <= initial(k) + t` relies on
    `lemma_step_length_change_bounded`, which REQUIRES `normal_form(chain)`.
    Without it, a single step can change `len(stk k)` by > 1 (push k twice),
    so `initial(k) + t` does not bound `len`.  The counterexample IS the
    non-NormalForm verifier `V_push_twice_non_normal` (see previous test).

    So: there is NO counterexample to Lemma 2 under the TRUE NormalForm
    precondition, because the step bound `lemma_step_length_change_bounded`
    is EXACTLY the structural fact that makes the induction close, and it
    FAILS without NormalForm.

    This test confirms: (a) the lemma correctly rejects non-NormalForm inputs
    (returns False), and (b) for a hand-constructed "almost NormalForm but
    with one repeated stack" the bound is violated concretely.
    """
    # A verifier that touches k0 twice but with different actions (push then pop)
    # — still violates NormalForm (k0 appears twice).
    V_fake = Machine(
        chains={0: [(0, PUSH), (0, POP)], 1: []},
        transitions={0: 1, 1: None},
        num_stacks=1,
        initial_label=0,
    )
    assert not normal_form(V_fake.chains[0]), "push+pop on same k is NOT NormalForm"
    # Lemma 2 returns False (precondition fails)
    r = lemma_stack_depth_bound(V_fake, [1], 1, 1, 0)
    if r is not False:
        return False
    # Concrete: push then pop => length unchanged = n.  So the bound n + t
    # is NOT violated HERE (length n <= n + 1).  But this is luck: the lemma
    # still correctly rejects it because NormalForm is the stated precondition
    # and without it the GENERAL bound is unsound (the push-twice case shows
    # a concrete violation).  The lemma is sound: it never claims True for
    # non-NormalForm inputs.
    # Confirm a genuine length violation requires push-twice (push+pop doesn't
    # violate the bound concretely, but the lemma still rejects it — the
    # precondition is structural, not value-based).
    actual = stack_length(cfg_at(V_fake, [1], 1), 0)
    if actual != 1:  # n=1, push+pop => 1
        return False
    # The genuine counterexample to the bound (n + t) is push-twice:
    V_bad = V_push_twice_non_normal()
    actual_bad = stack_length(cfg_at(V_bad, [1], 1), 0)
    if not (actual_bad == 3 and actual_bad > 1 + 1):
        return False
    # And the lemma rejects V_bad:
    if lemma_stack_depth_bound(V_bad, [1], 1, 1, 0) is not False:
        return False
    return True


# ---------------------------------------------------------------------------
# Tests for Lemma 3 (BoundedReadDepth) on NormalForm verifiers
# ---------------------------------------------------------------------------

def test_lemma3_normal_form_gives_bounded_read_depth() -> bool:
    """Under NormalForm, stmtReadDepth k (V.m lbl) <= 1 for all lbl, k.
    Test on multiple NormalForm verifiers."""
    # V_touch_multiple_stacks: label 0 has push k0, push k1 — reads 0 each.
    V = V_touch_multiple_stacks()
    assert machine_normal_form(V)
    for lbl in V.chains:
        for k in range(V.num_stacks):
            r = lemma_bounded_read_depth(V, lbl, k)
            if r is not True:
                return False
            if stmt_read_depth(k, V.chains[lbl]) > 1:
                return False
    # A NormalForm verifier with peek and pop (reads) — each stack once.
    V2 = Machine(
        chains={0: [(0, PEEK)], 1: [(0, POP)], 2: []},
        transitions={0: 1, 1: 2, 2: None},
        num_stacks=1,
        initial_label=0,
    )
    assert machine_normal_form(V2)
    for lbl in V2.chains:
        r = lemma_bounded_read_depth(V2, lbl, 0)
        if r is not True:
            return False
    # stmtReadDepth for label 0 (peek) = 1, label 1 (pop) = 1, label 2 = 0
    assert stmt_read_depth(0, V2.chains[0]) == 1
    assert stmt_read_depth(0, V2.chains[1]) == 1
    assert stmt_read_depth(0, V2.chains[2]) == 0
    # A NormalForm verifier that peeks k0 AND pops k1 in one chain (each once)
    V3 = Machine(
        chains={0: [(0, PEEK), (1, POP)], 1: []},
        transitions={0: 1, 1: None},
        num_stacks=2,
        initial_label=0,
    )
    assert machine_normal_form(V3)
    for lbl in V3.chains:
        for k in range(V3.num_stacks):
            r = lemma_bounded_read_depth(V3, lbl, k)
            if r is not True:
                return False
    assert stmt_read_depth(0, V3.chains[0]) == 1  # peek on k0
    assert stmt_read_depth(1, V3.chains[0]) == 1  # pop on k1
    return True


# ---------------------------------------------------------------------------
# Tests for Lemma 1 (halting bound) — composition of leaves
# ---------------------------------------------------------------------------

def test_lemma1_halting_bound_composes() -> bool:
    """Lemma 1 composes the two verified leaves; returns True.
    The actual halting is established upstream (Bridge 1 + outputsFun)."""
    V = V_halt_immediately()
    input_tape = [1, 2]
    T = 3
    out: list = []
    r = lemma_halting_time_bound(V, input_tape, T, out)
    if r is not True:
        return False
    # Also test on a multi-step machine
    V2 = V_multi_step_grow()
    r2 = lemma_halting_time_bound(V2, [1], 5, [])
    if r2 is not True:
        return False
    return True


# ---------------------------------------------------------------------------
# Full-trace depth check (concrete, broad)
# ---------------------------------------------------------------------------

def test_depth_bound_holds_over_full_trace() -> bool:
    """For several NormalForm verifiers, concretely check that
    `len(cfgAt t.stk k) <= n + t` for all t in [0, T] and all k."""
    cases = [
        (V_halt_immediately(), [1, 2, 3], 6),
        (V_multi_step_grow(), [1], 5),
        (V_grow_then_shrink(), [1, 2], 7),
        (V_touch_multiple_stacks(), [1, 2, 3], 5),
    ]
    for V, inp, T in cases:
        n = len(inp)
        assert machine_normal_form(V), f"{V} should be NormalForm"
        for t in range(0, T + 1):
            cfg = cfg_at(V, inp, t)
            for k in range(V.num_stacks):
                initial_k = n if k == 0 else 0
                if stack_length(cfg, k) > initial_k + t:
                    return False
                if stack_length(cfg, k) > n + T:
                    return False
    return True


# ===========================================================================
# Main
# ===========================================================================

if __name__ == "__main__":
    print("Bridge 3 — Adequacy / Depth Preconditions")
    print("=" * 60)
    print("Running adversarial tests...")
    all_ok = _run_all_tests()
    print("-" * 60)
    print(f"Overall: {'ALL PASS' if all_ok else 'SOME FAIL'}")
    print()
    print("Lemma 4 (normalization gap) returns:",
          lemma_any_polytime_verifier_has_normal_form(None))
    print("  (None = honest gap, as expected)")
    print()
    if all_ok:
        print("All NormalForm depth bounds hold; non-NormalForm correctly rejected.")
    else:
        print("FAILURES detected — see above.")