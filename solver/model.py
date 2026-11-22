"""Strict input model for the finite HMA table solver.

The Lean bridge encodes axis and component names by finite indices and table
values by natural-number tags. These tags preserve equality within each
coordinate; they do not claim a cross-coordinate value interpretation.
"""
from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any


class InputError(ValueError):
    """The input table is malformed or outside the supported table contract."""


def _object_without_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise InputError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise InputError(f"non-JSON numeric constant is not supported: {value}")


def canonical(value: Any) -> str:
    """Stable, type-preserving key for JSON values."""
    try:
        return json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise InputError(f"value is not valid canonical JSON: {exc}") from exc


def _require_keys(value: dict[str, Any], required: set[str], where: str) -> None:
    actual = set(value)
    missing = required - actual
    extra = actual - required
    if missing or extra:
        details = []
        if missing:
            details.append(f"missing {sorted(missing)!r}")
        if extra:
            details.append(f"unknown {sorted(extra)!r}")
        raise InputError(f"{where}: " + "; ".join(details))


def _name(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise InputError(f"{where} must be a non-empty string")
    return value


def _list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise InputError(f"{where} must be a JSON array")
    return value


@dataclass(frozen=True)
class Axis:
    name: str
    values: tuple[Any, ...]


@dataclass(frozen=True)
class Row:
    configuration: dict[str, Any]
    behavior: dict[str, Any]


@dataclass(frozen=True)
class Edge:
    components: tuple[str, ...]
    weight: int


@dataclass(frozen=True)
class Table:
    name: str
    axes: tuple[Axis, ...]
    components: tuple[str, ...]
    contract: tuple[Row, ...]
    edges: tuple[Edge, ...]

    @property
    def axis_names(self) -> tuple[str, ...]:
        # This order is the tie-break order named by SPEC.md.
        return tuple(sorted(axis.name for axis in self.axes))

    @property
    def axis_by_name(self) -> dict[str, Axis]:
        return {axis.name: axis for axis in self.axes}


@dataclass(frozen=True)
class EncodedTable:
    axis_names: tuple[str, ...]
    component_names: tuple[str, ...]
    configurations: tuple[tuple[int, ...], ...]
    behaviors: tuple[tuple[int, ...], ...]
    edges: tuple[tuple[tuple[int, ...], int], ...]


def load_table(path: str | Path) -> Table:
    try:
        raw = json.loads(
            Path(path).read_text(encoding="utf-8"),
            object_pairs_hook=_object_without_duplicate_keys,
            parse_constant=_reject_constant,
        )
    except InputError:
        raise
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise InputError(f"cannot read JSON table {path}: {exc}") from exc

    if not isinstance(raw, dict):
        raise InputError("root must be a JSON object")
    _require_keys(raw, {"format", "name", "axes", "components", "contract", "edges"}, "root")
    if raw["format"] != "hma-table-v1":
        raise InputError("format must be 'hma-table-v1'")
    name = _name(raw["name"], "name")

    axes: list[Axis] = []
    axis_names: set[str] = set()
    for index, item in enumerate(_list(raw["axes"], "axes")):
        where = f"axes[{index}]"
        if not isinstance(item, dict):
            raise InputError(f"{where} must be a JSON object")
        _require_keys(item, {"name", "values"}, where)
        axis_name = _name(item["name"], f"{where}.name")
        if axis_name in axis_names:
            raise InputError(f"duplicate axis name: {axis_name!r}")
        axis_names.add(axis_name)
        values = _list(item["values"], f"{where}.values")
        value_keys = [canonical(value) for value in values]
        if len(value_keys) != len(set(value_keys)):
            raise InputError(f"{where}.values contains a duplicate value")
        axes.append(Axis(axis_name, tuple(values)))

    components_list = _list(raw["components"], "components")
    components = tuple(_name(value, f"components[{i}]") for i, value in enumerate(components_list))
    if len(components) != len(set(components)):
        raise InputError("components contains a duplicate name")
    component_set = set(components)

    contract: list[Row] = []
    configuration_keys: set[str] = set()
    axes_by_name = {axis.name: axis for axis in axes}
    axis_name_set = set(axes_by_name)
    allowed_values = {
        axis.name: {canonical(value) for value in axis.values}
        for axis in axes
    }
    for index, item in enumerate(_list(raw["contract"], "contract")):
        where = f"contract[{index}]"
        if not isinstance(item, dict):
            raise InputError(f"{where} must be a JSON object")
        _require_keys(item, {"configuration", "behavior"}, where)
        configuration = item["configuration"]
        behavior = item["behavior"]
        if not isinstance(configuration, dict):
            raise InputError(f"{where}.configuration must be a JSON object")
        if set(configuration) != axis_name_set:
            missing = sorted(axis_name_set - set(configuration))
            extra = sorted(set(configuration) - axis_name_set)
            raise InputError(f"{where}.configuration axis mismatch (missing={missing!r}, unknown={extra!r})")
        for axis_name, value in configuration.items():
            if canonical(value) not in allowed_values[axis_name]:
                raise InputError(f"{where}.configuration value is outside axis {axis_name!r}'s domain")
        configuration_key = canonical(configuration)
        if configuration_key in configuration_keys:
            raise InputError(f"duplicate contract configuration at {where}")
        configuration_keys.add(configuration_key)
        if not isinstance(behavior, dict):
            raise InputError(f"{where}.behavior must be a JSON object")
        if set(behavior) != component_set:
            missing = sorted(component_set - set(behavior))
            extra = sorted(set(behavior) - component_set)
            raise InputError(f"{where}.behavior component mismatch (missing={missing!r}, unknown={extra!r})")
        contract.append(Row(dict(configuration), dict(behavior)))

    edges: list[Edge] = []
    edge_keys: set[tuple[str, ...]] = set()
    for index, item in enumerate(_list(raw["edges"], "edges")):
        where = f"edges[{index}]"
        if not isinstance(item, dict):
            raise InputError(f"{where} must be a JSON object")
        _require_keys(item, {"components", "weight"}, where)
        edge_components = tuple(_name(value, f"{where}.components[{i}]")
                                for i, value in enumerate(_list(item["components"], f"{where}.components")))
        if len(edge_components) != len(set(edge_components)):
            raise InputError(f"{where}.components contains a duplicate vertex")
        unknown_components = set(edge_components) - component_set
        if unknown_components:
            raise InputError(f"{where} references unknown components: {sorted(unknown_components)!r}")
        edge_key = tuple(sorted(edge_components))
        if edge_key in edge_keys:
            raise InputError(f"duplicate hyperedge as a set at {where}")
        edge_keys.add(edge_key)
        weight = item["weight"]
        if isinstance(weight, bool) or not isinstance(weight, int) or weight < 0:
            raise InputError(f"{where}.weight must be a natural number")
        if len(edge_components) >= 2 and weight == 0:
            raise InputError(f"{where}.weight must be positive for a hyperedge of size at least two")
        edges.append(Edge(edge_components, weight))

    return Table(name, tuple(axes), components, tuple(contract), tuple(edges))


def encode_table(table: Table) -> EncodedTable:
    axis_names = table.axis_names
    axes_by_name = table.axis_by_name
    axis_value_ids = {
        axis_name: {canonical(value): i for i, value in enumerate(axes_by_name[axis_name].values)}
        for axis_name in axis_names
    }
    configurations: list[tuple[int, ...]] = []
    for row in table.contract:
        configurations.append(tuple(
            axis_value_ids[axis_name][canonical(row.configuration[axis_name])]
            for axis_name in axis_names
        ))

    behavior_value_ids: dict[str, int] = {}
    behaviors: list[tuple[int, ...]] = []
    for row in table.contract:
        encoded_row: list[int] = []
        for component in table.components:
            key = canonical(row.behavior[component])
            if key not in behavior_value_ids:
                behavior_value_ids[key] = len(behavior_value_ids)
            encoded_row.append(behavior_value_ids[key])
        behaviors.append(tuple(encoded_row))

    component_ids = {component: i for i, component in enumerate(table.components)}
    edges = tuple((tuple(component_ids[name] for name in edge.components), edge.weight)
                  for edge in table.edges)
    return EncodedTable(axis_names, table.components, tuple(configurations), tuple(behaviors), edges)
