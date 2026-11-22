#!/usr/bin/env python3
"""Arena instance model for the Highest Minimal Axis program, Deliverable 3(c).

Implements the phase-2 arena semantics as briefed, as an executable
miniature, standalone (no demo / Space code is touched):

  - Grid platformer, 24 columns (0..23), ground row y=0 solid everywhere,
    agent start column 1, goal column 21.
  - Primitives: move +-1, jump +-1, jump-over +-2, plus wait when the
    motion axis is on. Landing = fall until supported (gravity).
  - Material slide on landing (extra columns in the direction of motion,
    stopped early by a block or the grid edge):
        stone 0, mud 0, rubber 1, ice 2.
  - Planner: Dijkstra over three fixed weight profiles producing
    candidate plans, Pareto frontier over (steps, specials), then
    selection by the axis weight vector (see build_episode).
  - Execution: apply the selected plan through the same successor
    function. Reversibility: apply inverse primitives in reverse order
    through the same successor function, compare the state hash
    (canonical state string) with the initial state's.

Pinned interpretation choices (also in the lane report):
  1. Steps = total primitive count of a plan; specials = count of jump
     and jump-over primitives. A plan's weighted cost is
     wsteps*steps + wspecials*specials, so one primitive costs
     wsteps + (wspecials if it is a jump or jump-over else 0); wait
     costs wsteps and is not special.
  2. The three planner profiles are (wsteps, wspecials) =
     (1, 0.05) fewest steps, (0.4, 1) fewest specials, (1, 1) balanced,
     in that enumeration order. Candidate plans are deduped preserving
     that order; the Pareto frontier filters dominated candidates
     preserving that order; the "plan" behavior component is the
     frontier candidate set, serialized sorted (canonical), while
     selection tie-breaking uses the enumeration order.
  3. Selection = the frontier candidate minimizing
     wsteps*steps + wspecials*specials with the instance's axis weights.
     Ties: wentropy 0 -> first in enumeration order; wentropy 1 ->
     maximal Shannon entropy (bits) of the plan's primitive-label
     distribution, further ties -> first in enumeration order.
  4. Block heights: scatter blocks at y=1 on the ground; stacked columns
     hold blocks at y=1 and y=2; floating blocks at y=2 (one air cell
     beneath, above the ground row). Jump rise is 2 cells, so a jump
     can land on any block top in this arena. Move is blocked when the
     target cell at the agent's feet height is solid; jumps are not
     blocked that way (the arc clears it and gravity lands the agent).
  5. Layout generation is a deterministic function of
     (seed, count, placement): a seeded shuffle of candidate columns
     4..19, greedily keeping columns at least 3 apart. Layout values
     serialize block positions only (material is not part of layout;
     it acts through the successor function). Under motion, the layout
     serializes the solids at each of the 4 phases.
  6. Motion: stacked top blocks (y=2 of a stack) and floating blocks
     oscillate horizontally with period 4 ticks; the offset by phase
     (tick mod 4) is [0, +1, 0, -1]. Scatter blocks do not move. A
     successor is computed against next-tick block positions; the
     successor state's phase is (tick+1) mod 4. Wait is available only
     when motion is on, and a waiting agent is not carried by a moving
     block: its support is re-evaluated at the next tick (it falls if
     its block moved away).
  7. Goal = a state whose column is 21 (any height). The state hash
     for reversibility includes the phase when motion is on.
  8. A no-plan episode serializes plan as an empty list, selection as
     "none", execution as goal=no at the start cell, and reversibility
     passes vacuously (the empty plan reverses to the initial state).

The behavior function is computed per full axis vector; graph and
candidate-plan results are cached per (seed, count, placement,
material, motion) because the weight and entropy axes act only at
selection time. Cached values are exactly the per-episode values.

Python 3, standard library only.
"""

import hashlib
import itertools
import json
import math
import random
from heapq import heappop, heappush

COLUMNS = 24
START_COLUMN = 1
GOAL_COLUMN = 21
GROUND_Y = 0

SLIDE = {"stone": 0, "mud": 0, "rubber": 1, "ice": 2}

# Primitive labels, in the fixed successor enumeration order.
MOVE_LEFT = "move_left"
MOVE_RIGHT = "move_right"
JUMP_LEFT = "jump_left"
JUMP_RIGHT = "jump_right"
JUMP_OVER_LEFT = "jump_over_left"
JUMP_OVER_RIGHT = "jump_over_right"
WAIT = "wait"

# (label, dx, kind) with kind in {"move", "jump", "jumpover", "wait"}.
PRIMITIVES = [
    (MOVE_LEFT, -1, "move"),
    (MOVE_RIGHT, 1, "move"),
    (JUMP_LEFT, -1, "jump"),
    (JUMP_RIGHT, 1, "jump"),
    (JUMP_OVER_LEFT, -2, "jumpover"),
    (JUMP_OVER_RIGHT, 2, "jumpover"),
]
SPECIAL_KINDS = {"jump", "jumpover"}

INVERSE = {
    MOVE_LEFT: MOVE_RIGHT,
    MOVE_RIGHT: MOVE_LEFT,
    JUMP_LEFT: JUMP_RIGHT,
    JUMP_RIGHT: JUMP_LEFT,
    JUMP_OVER_LEFT: JUMP_OVER_RIGHT,
    JUMP_OVER_RIGHT: JUMP_OVER_LEFT,
    WAIT: WAIT,
}

PROFILES = [  # enumeration order: fewest steps, fewest specials, balanced
    (1.0, 0.05),
    (0.4, 1.0),
    (1.0, 1.0),
]

PHASE_OFFSET = [0, 1, 0, -1]

AXES = [
    {"name": "count", "values": [0, 2, 4]},
    {"name": "placement", "values": ["scatter", "stacked", "floating"]},
    {"name": "material", "values": ["stone", "ice", "rubber", "mud"]},
    {"name": "wsteps", "values": [0.4, 1]},
    {"name": "wspecials", "values": [0.05, 1]},
    {"name": "wentropy", "values": [0, 1]},
    {"name": "motion", "values": ["off", "on"]},
]
COMPONENTS = ["layout", "successors", "plan", "selection", "execution"]
HYPEREDGES = [
    {"components": ["layout", "successors", "plan"], "weight": 1},
    {"components": ["successors", "plan", "execution"], "weight": 1},
    {"components": ["plan", "selection", "execution"], "weight": 1},
    {"components": ["successors", "execution"], "weight": 1},
]


def base_blocks(seed, count, placement):
    """Deterministic block list [(x, y), ...] at phase 0 (before any
    motion offset), a function of (seed, count, placement) only."""
    if count == 0:
        return []
    placement_index = ["scatter", "stacked", "floating"].index(placement)
    rng = random.Random(seed * 1000003 + count * 101 + placement_index * 17)
    candidates = list(range(4, 20))
    rng.shuffle(candidates)
    need = count if placement != "stacked" else count // 2
    chosen = []
    for col in candidates:
        if all(abs(col - kept) >= 3 for kept in chosen):
            chosen.append(col)
        if len(chosen) == need:
            break
    chosen.sort()
    blocks = []
    for col in chosen:
        if placement == "scatter":
            blocks.append((col, 1))
        elif placement == "stacked":
            blocks.append((col, 1))
            blocks.append((col, 2))
        else:  # floating
            blocks.append((col, 2))
    return sorted(blocks)


def is_moving_block(placement, block):
    """Blocks that oscillate under the motion axis: floating blocks and
    stacked top blocks. Scatter blocks never move."""
    if placement == "floating":
        return True
    if placement == "stacked" and block[1] == 2:
        return True
    return False


def solids_at(seed, count, placement, motion, phase):
    """Set of solid (x, y) block cells at the given phase. The ground
    row is handled separately (always solid at y=0, every column)."""
    blocks = base_blocks(seed, count, placement)
    if motion == "on":
        offset = PHASE_OFFSET[phase]
        moved = []
        for block in blocks:
            if is_moving_block(placement, block):
                moved.append((block[0] + offset, block[1]))
            else:
                moved.append(block)
        blocks = moved
    return set(blocks)


def is_solid(solids, x, y):
    if y == GROUND_Y and 0 <= x < COLUMNS:
        return True
    return (x, y) in solids


def fall(solids, x, feet_y):
    """Fall from feet_y in column x until the cell below the feet is
    solid. Returns the resting feet height."""
    feet = feet_y
    while feet > GROUND_Y + 1 or not is_solid(solids, x, feet - 1):
        if is_solid(solids, x, feet - 1):
            break
        feet -= 1
    return feet


def state_string(state, motion):
    x, y, phase = state
    if motion == "on":
        return "%d,%d,%d" % (x, y, phase)
    return "%d,%d" % (x, y)


def start_state(seed, count, placement, motion):
    solids = solids_at(seed, count, placement, motion, 0)
    feet = fall(solids, START_COLUMN, GROUND_Y + 1)
    return (START_COLUMN, feet, 0)


def successor(seed, count, placement, material, motion, state, label):
    """One successor step, or None when the primitive is unavailable
    or blocked. Computed against next-tick block positions."""
    x, y, phase = state
    next_phase = (phase + 1) % 4 if motion == "on" else 0
    solids_now = solids_at(seed, count, placement, motion, phase)
    solids_next = solids_at(seed, count, placement, motion, next_phase)
    slide = SLIDE[material]

    if label == WAIT:
        if motion != "on":
            return None
        feet = fall(solids_next, x, y)
        return (x, feet, next_phase)

    dx, kind = next((d, k) for lab, d, k in PRIMITIVES if lab == label)
    target_x = x + dx
    if not (0 <= target_x < COLUMNS):
        return None
    if kind == "move":
        if is_solid(solids_next, target_x, y):
            return None
        feet = fall(solids_next, target_x, y)
    else:  # jump / jump-over: arc rises 2, then gravity lands the agent
        feet = fall(solids_next, target_x, y + 2)

    # Slide on landing, in the direction of motion, stopped early by a
    # block at feet height or by the grid edge; gravity re-applies
    # after each slid column.
    direction = 1 if dx > 0 else -1
    landed_x = target_x
    for _ in range(slide):
        slide_x = landed_x + direction
        if not (0 <= slide_x < COLUMNS):
            break
        if is_solid(solids_next, slide_x, feet):
            break
        landed_x = slide_x
        feet = fall(solids_next, landed_x, feet)
    return (landed_x, feet, next_phase)


def reachable_edges(seed, count, placement, material, motion):
    """The full reachable successor relation from the start state.
    Returns (start, sorted list of (state, label, next_state) string
    triples)."""
    start = start_state(seed, count, placement, motion)
    labels = [lab for lab, _, _ in PRIMITIVES]
    if motion == "on":
        labels = labels + [WAIT]
    visited = {start}
    stack = [start]
    edges = []
    while stack:
        state = stack.pop()
        for label in labels:
            nxt = successor(seed, count, placement, material, motion,
                            state, label)
            if nxt is None:
                continue
            edges.append((state_string(state, motion), label,
                          state_string(nxt, motion)))
            if nxt not in visited:
                visited.add(nxt)
                stack.append(nxt)
    edges.sort()
    return start, edges


def dijkstra_plan(seed, count, placement, material, motion, profile):
    """Cheapest plan (label tuple) to any goal-column state under one
    weight profile, or None. Heap key (cost, steps, specials, labels)
    makes the result deterministic."""
    w_step, w_special = profile
    start = start_state(seed, count, placement, motion)
    labels = [lab for lab, _, _ in PRIMITIVES]
    if motion == "on":
        labels = labels + [WAIT]
    kind_of = {lab: kind for lab, _, kind in PRIMITIVES}
    kind_of[WAIT] = "wait"

    def action_cost(label):
        cost = w_step
        if kind_of[label] in SPECIAL_KINDS:
            cost += w_special
        return cost

    heap = [(0.0, 0, 0, (), start)]
    best_seen = {start: (0.0, 0, 0, ())}
    while heap:
        cost, steps, specials, path, state = heappop(heap)
        if best_seen.get(state) != (cost, steps, specials, path):
            continue
        if state[0] == GOAL_COLUMN:
            return path
        for label in labels:
            nxt = successor(seed, count, placement, material, motion,
                            state, label)
            if nxt is None:
                continue
            entry = (cost + action_cost(label), steps + 1,
                     specials + (1 if kind_of[label] in SPECIAL_KINDS
                                 else 0),
                     path + (label,))
            if nxt not in best_seen or entry < best_seen[nxt]:
                best_seen[nxt] = entry
                heappush(heap, entry + (nxt,))
    return None


def plan_counts(path):
    steps = len(path)
    kind_of = {lab: kind for lab, _, kind in PRIMITIVES}
    specials = sum(1 for lab in path if kind_of[lab] in SPECIAL_KINDS)
    return steps, specials


def label_entropy(path):
    if not path:
        return 0.0
    counts = {}
    for lab in path:
        counts[lab] = counts.get(lab, 0) + 1
    total = len(path)
    return -sum((c / total) * math.log2(c / total)
                for c in counts.values())


def candidate_frontier(seed, count, placement, material, motion):
    """Candidate plans from the three profiles (deduped, enumeration
    order), filtered to the Pareto frontier over (steps, specials),
    enumeration order preserved."""
    candidates = []
    for profile in PROFILES:
        path = dijkstra_plan(seed, count, placement, material, motion,
                             profile)
        if path is not None and path not in candidates:
            candidates.append(path)
    frontier = []
    for path in candidates:
        steps, specials = plan_counts(path)
        dominated = False
        for other in candidates:
            if other is path:
                continue
            o_steps, o_specials = plan_counts(other)
            if (o_steps <= steps and o_specials <= specials
                    and (o_steps < steps or o_specials < specials)):
                dominated = True
                break
        if not dominated:
            frontier.append(path)
    return frontier


def select_plan(frontier, wsteps, wspecials, wentropy):
    """The selected frontier candidate, or None. Minimizes
    wsteps*steps + wspecials*specials; ties per the wentropy axis."""
    if not frontier:
        return None
    scored = []
    for path in frontier:
        steps, specials = plan_counts(path)
        scored.append((wsteps * steps + wspecials * specials, path))
    best_score = min(score for score, _ in scored)
    tied = [path for score, path in scored if score == best_score]
    if len(tied) == 1:
        return tied[0]
    if wentropy == 0:
        return tied[0]
    best_entropy = max(label_entropy(path) for path in tied)
    for path in tied:
        if label_entropy(path) == best_entropy:
            return path
    return tied[0]  # unreachable; keeps the function total


def execute(seed, count, placement, material, motion, selected):
    """Apply the selected plan, then its inverses in reverse order.
    Returns (goal_reached, final_x, final_y, reversibility_pass)."""
    start = start_state(seed, count, placement, motion)
    if selected is None:
        return (False, start[0], start[1], True)
    state = start
    for label in selected:
        nxt = successor(seed, count, placement, material, motion,
                        state, label)
        if nxt is None:
            return (False, state[0], state[1], False)
        state = nxt
    goal = state[0] == GOAL_COLUMN
    final_x, final_y = state[0], state[1]
    reverse_state = state
    reversible = True
    for label in reversed(selected):
        nxt = successor(seed, count, placement, material, motion,
                        reverse_state, INVERSE[label])
        if nxt is None:
            reversible = False
            break
        reverse_state = nxt
    if reversible:
        reversible = (state_string(reverse_state, motion)
                      == state_string(start, motion))
    return (goal, final_x, final_y, reversible)


_graph_cache = {}


def graph_data(seed, count, placement, material, motion):
    """Layout value, successors value, and frontier for one physics
    combination (cached; the values are the per-episode values)."""
    key = (seed, count, placement, material, motion)
    if key in _graph_cache:
        return _graph_cache[key]

    if motion == "on":
        layout_value = json.dumps(
            {"phases": {
                str(phase): sorted(
                    solids_at(seed, count, placement, motion, phase))
                for phase in range(4)},
             "ground_row": GROUND_Y, "columns": COLUMNS},
            sort_keys=True)
    else:
        layout_value = json.dumps(
            {"blocks": sorted(
                solids_at(seed, count, placement, motion, 0)),
             "ground_row": GROUND_Y, "columns": COLUMNS},
            sort_keys=True)

    _, edges = reachable_edges(seed, count, placement, material, motion)
    successors_value = json.dumps(edges)
    frontier = candidate_frontier(seed, count, placement, material,
                                  motion)
    data = (layout_value, successors_value, frontier)
    _graph_cache[key] = data
    return data


def episode(seed, config):
    """The five behavior component values at one full axis vector.
    config is a dict keyed by axis name."""
    count = config["count"]
    placement = config["placement"]
    material = config["material"]
    motion = config["motion"]
    layout_value, successors_value, frontier = graph_data(
        seed, count, placement, material, motion)
    plan_value = json.dumps(sorted(list(path) for path in frontier))
    selected = select_plan(frontier, config["wsteps"],
                           config["wspecials"], config["wentropy"])
    selection_value = (json.dumps(list(selected))
                       if selected is not None else "none")
    goal, final_x, final_y, reversible = execute(
        seed, count, placement, material, motion, selected)
    execution_value = "goal=%s;final=%d,%d;rev=%s" % (
        "yes" if goal else "no", final_x, final_y,
        "yes" if reversible else "no")
    return {
        "layout": layout_value,
        "successors": successors_value,
        "plan": plan_value,
        "selection": selection_value,
        "execution": execution_value,
    }


def build_instance(seed):
    """The full solver instance for one seed: the contract is the full
    product of the axis ranges (every combination allowed)."""
    axis_values = [axis["values"] for axis in AXES]
    contract = [list(row) for row in itertools.product(*axis_values)]
    behavior = {comp: [] for comp in COMPONENTS}
    for row in contract:
        config = {axis["name"]: value
                  for axis, value in zip(AXES, row)}
        values = episode(seed, config)
        for comp in COMPONENTS:
            behavior[comp].append(values[comp])
    return {
        "name": "arena-seed-%d" % seed,
        "axes": AXES,
        "contract": contract,
        "components": COMPONENTS,
        "behavior": behavior,
        "hyperedges": HYPEREDGES,
    }


def state_hash(state, motion):
    return hashlib.sha256(
        state_string(state, motion).encode("utf-8")).hexdigest()


if __name__ == "__main__":
    import sys
    seed = int(sys.argv[1])
    out_path = sys.argv[2]
    instance = build_instance(seed)
    with open(out_path, "w", encoding="utf-8") as handle:
        json.dump(instance, handle)
    print("seed %d: %d contract rows written to %s"
          % (seed, len(instance["contract"]), out_path))
