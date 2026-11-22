#!/usr/bin/env node
// Reproduce the finite table from the pinned arena's original pure functions.
// Usage: node generate-arena.cjs [--raw] > arena.json
// Without --raw, exact observation strings are interned independently per component.
// An optional --dictionary PATH preserves every original observation string.
const fs = require('node:fs');
const { hmaBuildInstance } = require('./arena-model.cjs');
const args = process.argv.slice(2);
let raw = false;
let dictionaryPath = null;
for (let i = 0; i < args.length; i++) {
  if (args[i] === '--raw') raw = true;
  else if (args[i] === '--dictionary' && args[i + 1]) dictionaryPath = args[++i];
  else throw new Error('Usage: generate-arena.cjs [--raw] [--dictionary PATH]');
}
const inst = hmaBuildInstance(11, 8);
const label = value => typeof value === 'number' && !Number.isInteger(value) ? String(value) : value;
const dictionaries = {};
for (const component of inst.components) {
  const values = Array.from(new Set(inst.behavior[component])).sort();
  dictionaries[component] = values;
  if (!raw) {
    const index = new Map(values.map((value, i) => [value, i]));
    inst.behavior[component] = inst.behavior[component].map(value => {
      const id = index.get(value);
      if (values[id] !== value) throw new Error('Observation interning changed equality');
      return id;
    });
  }
}
const table = {
  schema: 1,
  name: 'arena',
  axes: inst.axes.map(axis => ({name: axis.name, values: axis.values.map(label)})),
  components: inst.components,
  contract: inst.contract.map((axes, i) => ({
    axes: axes.map(label),
    behavior: inst.components.map(component => inst.behavior[component][i]),
  })),
  hyperedges: inst.hyperedges,
};
if (dictionaryPath !== null) fs.writeFileSync(dictionaryPath, JSON.stringify(dictionaries) + '\n');
process.stdout.write(JSON.stringify(table) + '\n');
