"""Compare the replay with the theorem-level axiom reports in the reference runs."""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]+)\]|does not depend on any axioms)$")

def reports(lines):
    result = {}
    for line in lines:
        if not line.strip() or line.startswith(("Lean (version ", "Checking ")):
            continue
        match = REPORT.fullmatch(line)
        if not match:
            raise SystemExit(f"Unexpected checker output: {line}")
        name, axioms = match.groups()
        used = frozenset(axioms.split(", ") if axioms else [])
        if not used <= ALLOWED or result.setdefault(name, used) != used:
            raise SystemExit(f"Unexpected axiom report for {name}: {used}")
    return result

references = Path(__file__).parent / "verification"
expected = reports(line for file in sorted(references.glob("*.txt")) for line in file.read_text().splitlines())
actual = reports(Path(sys.argv[1]).read_text().splitlines())
if not expected or expected != actual:
    raise SystemExit("The replay differs from the reference theorem reports.")
print(f"Verified axiom reports for {len(actual)} declarations.")
