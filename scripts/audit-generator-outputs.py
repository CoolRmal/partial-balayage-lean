#!/usr/bin/env python3
"""Audit the actual restored square proofs together; Python proves no mathematics."""
import importlib.util
from pathlib import Path


spec = importlib.util.spec_from_file_location(
    "numerical_driver", Path.cwd() / "scripts/validate-generator-blocks.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
snapshot = driver.inspect(runtime=True)
lines = [f"import {driver.PREFIX}{block}" for block in range(106)]
lines.extend(["", "open PartialBalayage.Maximal.Square", "namespace SquareNumericalAudit"])
expected = []
for block in range(106):
    name = f"generatorLeafBlocks{block}"
    valid = f"{driver.NAMESPACE}.{name}_valid"
    numerical = f"SquareNumericalAudit.block{block}_numericalValid"
    positive = f"SquareNumericalAudit.block{block}_pointwise_positive"
    lines.extend([
        f"theorem block{block}_numericalValid (i : Fin 64) :",
        f"    ({name} i).NumericalValid := ({name}_valid i).2.2.2",
        f"theorem block{block}_pointwise_positive (i : Fin 64) {{u v : ℝ}}",
        f"    (h : ({name} i).rectangle.Contains u v)",
        "    (hu : 0 < u) (hv : 0 < v) (hr : u + v < 28) :",
        "    0 < generatorInteriorDensity u v :=",
        f"  GeneratorLeafData.positivity ({name}_valid i) h hu hv hr",
        *(f"#print axioms {n}" for n in (valid, numerical, positive)),
    ])
    expected.extend([valid, numerical, positive])
lines.extend(["end SquareNumericalAudit", ""])
path = driver.OUT / "combined-audit.lean"
path.write_text("\n".join(lines))
report = {"snapshot": snapshot, "status": "checking", "blocks": 106,
          "expected_endpoints": len(expected)}
driver.save_json("combined-report.json", report)
report["audit"] = driver.audit(path, expected, "combined-audit")
driver.check_immutable(snapshot)
report["status"] = "pass"
driver.save_json("combined-report.json", report)
