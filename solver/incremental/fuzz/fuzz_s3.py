#!/usr/bin/env python3
"""Randomized differential test: axis.AxisEngine against the HMA solver's
solve(), unmodified, on random tables (2-4 axes, 2-3 values, 2-4 components,
random edges), after every operation of random sequences: join batches,
refused batches (duplicate or changed row: must leave state unchanged),
withdrawals, changed cells as withdrawal plus join. The reference table is
built from this script's own record of the contract, not from the engine.
usage: fuzz_s3.py <solver dir> [seeds] [steps]"""
import itertools, json, os, random, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import axis as AX


def rand_doc(rng):
    n = rng.randint(2, 4)
    axes = [{"name": "a%d" % i, "values": list(range(rng.randint(2, 3)))} for i in range(n)]
    comps = ["p%d" % i for i in range(rng.randint(2, 4))]
    edges, seen = [], set()
    for _ in range(rng.randint(1, 3)):
        k = rng.randint(1, len(comps))
        cs = tuple(sorted(rng.sample(comps, k)))
        if cs not in seen:
            seen.add(cs)
            edges.append({"components": list(cs), "weight": rng.randint(1, 3)})
    return {"format": "hma-table-v1", "name": "F", "axes": axes, "components": comps,
            "contract": [], "edges": edges}


def load(model, doc, tmp):
    p = os.path.join(tmp, "t.json")
    with open(p, "w") as f:
        json.dump(doc, f)
    return model.load_table(p)


def snapshot(e):
    return (list(e.rows), dict(e.dc), dict(e.cnt), dict(e.live), dict(e.measure))


def fuzz(model, solver, seed, steps, tmp):
    rng = random.Random(seed)
    doc = rand_doc(rng)
    space = list(itertools.product(*[a["values"] for a in doc["axes"]]))
    names = [a["name"] for a in doc["axes"]]
    cur = {}  # config tuple -> behavior dict
    e = AX.AxisEngine(model, load(model, doc, tmp))
    refusals = 0
    for step in range(steps):
        free = [c for c in space if c not in cur]
        op = rng.random()
        rowdoc = lambda c, b: {"configuration": dict(zip(names, c)), "behavior": b}
        beh = lambda: {k: rng.randint(0, 2) for k in doc["components"]}
        if op < 0.5 and free:
            batch = [(c, beh()) for c in rng.sample(free, rng.randint(1, min(4, len(free))))]
            rows = load(model, dict(doc, contract=[rowdoc(c, b) for c, b in batch]), tmp).contract
            e.join(list(rows))
            cur.update(batch)
        elif op < 0.62 and cur:
            # refused batch: new rows (if any) then a duplicate or a changed existing row
            c0 = rng.choice(list(cur))
            bad = dict(cur[c0]) if rng.random() < 0.5 else {k: (v + 1) % 3 for k, v in cur[c0].items()}
            batch = [(c, beh()) for c in rng.sample(free, min(len(free), rng.randint(0, 2)))]
            rows = load(model, dict(doc, contract=[rowdoc(c, b) for c, b in batch]), tmp).contract
            badrow = load(model, dict(doc, contract=[rowdoc(c0, bad)]), tmp).contract[0]
            snap = snapshot(e)
            try:
                e.join(list(rows) + [badrow])
                return "seed %d step %d: bad batch not refused" % (seed, step)
            except AX.NotAJoin:
                refusals += 1
            if snapshot(e) != snap:
                return "seed %d step %d: refused batch changed carried state" % (seed, step)
        elif op < 0.85 and cur:
            gone = rng.sample(list(cur), rng.randint(1, min(3, len(cur))))
            e.withdraw([dict(zip(names, c)) for c in gone])
            for c in gone:
                del cur[c]
        elif cur:
            c0 = rng.choice(list(cur))
            nb = beh()
            e.withdraw([dict(zip(names, c0))])
            e.join(list(load(model, dict(doc, contract=[rowdoc(c0, nb)]), tmp).contract))
            cur[c0] = nb
        ref_doc = dict(doc, contract=[rowdoc(c, b) for c, b in sorted(cur.items())])
        try:
            want = solver.solve(load(model, ref_doc, tmp))
        except model.InputError as x:
            return "seed %d step %d: solver refused the reference table: %s" % (seed, step, x)
        if e.result() != want:
            return "seed %d step %d: engine result differs from solver.solve (%d rows)" % (seed, step, len(cur))
    return None


def main():
    model, solver = AX.load_solver(sys.argv[1])
    seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    bad = []
    with tempfile.TemporaryDirectory() as tmp:
        for s in range(seeds):
            r = fuzz(model, solver, s, steps, tmp)
            if r:
                bad.append(r)
    print("axis: %d random tables x %d operations, compared with solver.solve after every operation" % (seeds, steps))
    for b in bad[:10]:
        print("DISAGREE", b)
    print("FUZZ s3: %s (%d disagreements)" % ("PASS" if not bad else "FAIL", len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
