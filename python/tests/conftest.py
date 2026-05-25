"""Shared pytest fixtures."""

from __future__ import annotations

import pytest


@pytest.fixture
def sample_report() -> dict:
    """A minimal JSON payload matching the §8.1 schema."""
    return {
        "version": "0.1.0",
        "spec_file": "specs/sorting/sort.fol",
        "parameters": {
            "model_bound": 2,
            "quantifier_rank": 1,
            "epsilon": 0.5,
            "seed": 42,
            "models_enumerated": 4096,
        },
        "signature": {
            "sorts": ["Elem"],
            "relations": [
                {"name": "leq", "arity": ["Elem", "Elem"]},
                {"name": "sorted_seq", "arity": ["Elem"]},
            ],
            "functions": [
                {"name": "output", "domain": ["Elem"], "codomain": "Elem"}
            ],
        },
        "decomposition": [
            {"index": 0, "formula": "forall x:Elem . sorted_seq(output(x))"},
            {"index": 1, "formula": "forall x:Elem . leq(x, output(x))"},
        ],
        "tightness": {
            "score": 0.642,
            "confidence_interval": [0.642, 0.642],
            "exhaustive": True,
            "neighborhood_size": 14,
            "killed": 9,
            "alive": 5,
        },
        "alive_mutants": [
            {
                "index": 3,
                "class": "weakening",
                "perturbed_component": 0,
                "distance": 0.083,
                "formula_summary": "removed: sorted_seq(output(x))",
            },
            {
                "index": 7,
                "class": "replacement",
                "perturbed_component": 1,
                "distance": 0.125,
                "formula_summary": "replaced leq with ¬leq",
            },
        ],
        "timing": {
            "parse_ms": 0,
            "enumeration_ms": 15,
            "mutation_ms": 1200,
            "tightness_ms": 12,
            "total_ms": 1230,
        },
        "evaluator": "exhaustive",
        "smt": False,
        "smt_fallback_count": 0,
    }
