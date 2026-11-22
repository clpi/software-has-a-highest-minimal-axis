#!/usr/bin/env python3
"""System 3: incremental highest-minimal-axis solve under row joins.

Wraps the finite HMA table solver (software-has-a-highest-minimal-axis,
solver/ at b12fdb2) as the checker, unmodified, and reuses its strict
input model (model.load_table) so the engine reads exactly the tables the
solver reads.

Rule (SPEC.md, system 3, the difference-set cone): for a row pair, its
difference set is the set of axes on which the two configurations differ.
A component is live in subset S exactly when some row pair whose
difference set is contained in S has different behavior on that
component. So subset S depends exactly on the pairs whose difference set
lies inside S. Carried state: per difference set m, the components some
pair with difference set m distinguishes (dc[m]); per subset, its live
set, engaged edges and rho. A join appends contract rows and creates only
pairs involving a new row. A new pair (m, comps) changes subset S only if
m is inside S and comps adds a component not yet in dc[m]-closure of S;
only those subsets re-measure. Minimality and the highest selection are
re-derived from carried per-subset measures (arithmetic over 2^n carried
states, no pair is rescanned). A withdrawn row or a changed behavior cell
is not a join: it is refused here, by name.

Counts are the claims: pairs computed, subsets re-measured.
"""
from __future__ import annotations

import importlib
import os
import sys
from itertools import combinations


def load_solver(solver_dir):
    sys.path.insert(0, solver_dir)
    model = importlib.import_module("model")
    solver = importlib.import_module("solver")
    return model, solver


class NotAJoin(Exception):
    pass


class AxisEngine:
    def __init__(self, model, table, superset_mutant=False):
        """Start from the table's axes, components and edges with no rows,
        then join the table's rows. (Joining from empty is the build.)"""
        self.model = model
        self.name = table.name
        self.axes_decl = table.axes
        self.components = table.components
        self.edges_decl = table.edges
        self.axis_names = tuple(sorted(a.name for a in table.axes))
        self.n = len(self.axis_names)
        self.comp_index = {c: i for i, c in enumerate(self.components)}
        self.edges = [(tuple(self.comp_index[c] for c in e.components), e.weight)
                      for e in table.edges]
        self.rows = []          # (config tuple of canonical values, behavior tuple of canonical)
        self.raw_rows = []      # model.Row objects, for building the checker's table
        self.dc = {}            # difference mask -> frozenset of components
        self.cnt = {}           # (mask, component) -> number of supporting pairs
        self.pairs_released = 0
        self.live = {S: frozenset() for S in range(1 << self.n)}
        self.measure = {S: self._measure(frozenset()) for S in range(1 << self.n)}
        self.pairs_computed = 0
        self.remeasured = set()
        self._mutant = superset_mutant
        self.join(table.contract)

    def _measure(self, live):
        engaged = tuple(i for i, (edge, w) in enumerate(self.edges)
                        if len(edge) >= 2 and all(c in live for c in edge))
        mu = sum(self.edges[i][1] for i in engaged)
        return engaged, mu, len(live)

    def _encode(self, row):
        c = self.model.canonical
        cfg = tuple(c(row.configuration[a]) for a in self.axis_names)
        beh = tuple(c(row.behavior[comp]) for comp in self.components)
        return cfg, beh

    def join(self, new_rows):
        """Append contract rows. Returns (pairs computed, subsets re-measured)."""
        # Validate the whole batch before any carried state changes, so a
        # refused join leaves the engine exactly as it was.
        encoded = []
        seen = {r[0]: r[1] for r in self.rows}
        for row in new_rows:
            cfg, beh = self._encode(row)
            if cfg in seen:
                if seen[cfg] == beh:
                    raise NotAJoin("duplicate row: not a join (the solver rejects it)")
                raise NotAJoin("changed behavior at an existing configuration: "
                               "a withdrawal plus a join, invalidating every pair "
                               "touching that row; not handled as a join")
            seen[cfg] = beh
            encoded.append((row, cfg, beh))
        before = self.pairs_computed
        self.remeasured = set()
        added = {}  # mask -> components newly added to dc[mask]
        for row, cfg, beh in encoded:
            for ocfg, obeh in self.rows:
                self.pairs_computed += 1
                mask = 0
                for i in range(self.n):
                    if cfg[i] != ocfg[i]:
                        mask |= 1 << i
                comps = frozenset(k for k in range(len(beh)) if beh[k] != obeh[k])
                for k in comps:
                    self.cnt[(mask, k)] = self.cnt.get((mask, k), 0) + 1
                new = comps - self.dc.get(mask, frozenset())
                if new:
                    self.dc[mask] = self.dc.get(mask, frozenset()) | new
                    added[mask] = added.get(mask, frozenset()) | new
            self.rows.append((cfg, beh))
            self.raw_rows.append(row)
        # scope: only subsets containing a mask whose dc grew
        for mask, comps in added.items():
            targets = [mask] if self._mutant else \
                [S for S in range(1 << self.n) if S & mask == mask]
            for S in targets:
                grown = self.live[S] | comps
                if grown != self.live[S]:
                    self.live[S] = grown
                    self.remeasured.add(S)
        for S in self.remeasured:
            self.measure[S] = self._measure(self.live[S])
        return self.pairs_computed - before, len(self.remeasured)

    def withdraw(self, configurations, count_mutant=False):
        """Remove contract rows by configuration (dicts axis -> value).

        Deletion keeps every alternate support: a component leaves dc[m]
        only when its support count (pairs with difference set m that
        distinguish it) reaches zero. Each subset containing such an m has
        its live set rebuilt from the carried dc table (no pair rescan).
        There are no cycles: liveness is one non-recursive layer over
        pairs, so counting is complete. count_mutant drops a component at
        its first lost support (overdelete with no rederive).
        Returns (pairs released, subsets re-measured)."""
        c = self.model.canonical
        gone = {tuple(c(cfg[a]) for a in self.axis_names) for cfg in configurations}
        idx = [i for i, r in enumerate(self.rows) if r[0] in gone]
        if len(idx) != len(gone):
            raise NotAJoin("withdrawal of a configuration that is not in the contract")
        before = self.pairs_released
        self.remeasured = set()
        shrunk = set()
        removed = set(idx)
        for i in idx:
            cfg, beh = self.rows[i]
            for j, (ocfg, obeh) in enumerate(self.rows):
                if j == i or (j in removed and j < i):
                    continue  # each pair released once
                self.pairs_released += 1
                mask = 0
                for a in range(self.n):
                    if cfg[a] != ocfg[a]:
                        mask |= 1 << a
                for k in range(len(beh)):
                    if beh[k] != obeh[k]:
                        self.cnt[(mask, k)] -= 1
                        if count_mutant:
                            self.cnt[(mask, k)] = 0  # MUTANT: alternate supports ignored
                        if self.cnt[(mask, k)] == 0:
                            self.dc[mask] = self.dc.get(mask, frozenset()) - {k}
                            shrunk.add(mask)
        self.rows = [r for i, r in enumerate(self.rows) if i not in removed]
        self.raw_rows = [r for i, r in enumerate(self.raw_rows) if i not in removed]
        for S in range(1 << self.n):
            if not any(S & m == m for m in shrunk):
                continue  # outside every shrunk difference set's cone
            live = frozenset().union(*[d for m, d in self.dc.items() if S & m == m]) \
                if self.dc else frozenset()
            if live != self.live[S]:
                self.live[S] = live
                self.remeasured.add(S)
        for S in self.remeasured:
            self.measure[S] = self._measure(self.live[S])
        return self.pairs_released - before, len(self.remeasured)

    def result(self):
        """Selection re-derived from carried per-subset measures, in the
        solver's output format."""
        axes = self.axis_names
        full = (1 << self.n) - 1
        mu_all = self.measure[full][1]
        def members(S):
            return tuple(i for i in range(self.n) if S >> i & 1)
        suff = [S for S in range(1 << self.n) if self.measure[S][1] == mu_all]
        minimal = [S for S in suff
                   if not any(T != S and T & S == T for T in suff)]
        rho = {S: (self.measure[S][1], self.measure[S][2]) for S in minimal}
        top = max(rho.values())
        chosen = min((S for S in minimal if rho[S] == top),
                     key=lambda S: tuple(axes[i] for i in members(S)))
        ordered = sorted(minimal, key=lambda S: (-rho[S][0], -rho[S][1],
                                                 tuple(axes[i] for i in members(S))))
        live_all = [self.components[i] for i in sorted(self.live[full])]
        engaged_all = [{"components": [self.components[i] for i in self.edges[e][0]],
                        "weight": self.edges[e][1]} for e in self.measure[full][0]]
        disp = {}
        for i, a in enumerate(axes):
            if chosen >> i & 1:
                m = "in-selected"
            elif any(S >> i & 1 for S in minimal):
                m = "in-other-minimal"
            else:
                m = "in-none"
            disp[a] = {"membership": m,
                       "emergent_dead": self.live[full & ~(1 << i)] == self.live[full]}
        n = len(self.rows)
        return {
            "format": "hma-result-v1",
            "instance": self.name,
            "selected": [axes[i] for i in members(chosen)],
            "selected_rho": {"mu": rho[chosen][0], "lambda": rho[chosen][1]},
            "mu_all": mu_all,
            "live_all": live_all,
            "engaged_all": engaged_all,
            "minimal_sufficient": [{"axes": [axes[i] for i in members(S)],
                                    "rho": {"mu": rho[S][0], "lambda": rho[S][1]}}
                                   for S in ordered],
            "axis_dispositions": disp,
            "counts": {"axes": self.n, "contract_rows": n,
                       "behavior_cells": n * len(self.components),
                       "hyperedges": len(self.edges), "subsets": 1 << self.n,
                       "contract_row_pairs": n * (n - 1) // 2},
        }

    def table(self):
        """The joined instance as a solver Table (for the checker)."""
        return self.model.Table(self.name, self.axes_decl, self.components,
                                tuple(self.raw_rows), self.edges_decl)
