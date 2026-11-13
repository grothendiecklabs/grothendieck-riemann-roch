#!/usr/bin/env python3
"""Compare what Lean reports with what each Formal card of the map claims.

Usage: python3 check.py verify-output.txt

Prints a short verdict, writes the full record to verification.json, and exits
with 1 if any declaration fails: missing, resting on an axiom beyond Lean's
standard three, or leaving out an assumption its card declares.
"""

import json
import re
import sys
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def strip_positions(output):
    """Drop the 'Verify.lean:line:col: info:' prefix Lean puts on each message."""
    prefix = r"^.*?Verify\.lean:\d+:\d+: (?:info|warning|error): ?"
    return re.sub(prefix, "", output, flags=re.MULTILINE)


def axioms_of(name, output):
    """The axioms '#print axioms' reports for a declaration, or None if absent."""
    pattern = (
        rf"^'{re.escape(name)}'"
        r"(?: depends on axioms: \[([^\]]*)\]| does not depend on any axioms)"
    )
    found = re.search(pattern, output, re.MULTILINE | re.DOTALL)
    if not found:
        return None
    listed = found.group(1) or ""
    return sorted(axiom.strip() for axiom in listed.split(",") if axiom.strip())


def signature_of(name, output):
    """The statement '#check' prints for a declaration, on one line, or None."""
    found = re.search(rf"^@?{re.escape(name)} :(.*?)(?=^\S|\Z)", output, re.MULTILINE | re.DOTALL)
    return " ".join(found.group(1).split()) if found else None


def check_declaration(name, assumes, output):
    axioms = axioms_of(name, output)
    signature = signature_of(name, output)
    if axioms is None or signature is None:
        return {"name": name, "ok": False, "problem": "not found in Lean's output"}

    problems = []
    extra = sorted(set(axioms) - STANDARD_AXIOMS)
    if extra:
        problems.append("axioms beyond the standard three: " + ", ".join(extra))
    missing = [assumption for assumption in assumes if assumption not in signature]
    if missing:
        problems.append("assumptions not in the signature: " + ", ".join(missing))

    result = {"name": name, "ok": not problems, "axioms": axioms, "signature": signature}
    if problems:
        result["problem"] = "; ".join(problems)
    return result


def main():
    expected = json.loads(Path("expected.json").read_text(encoding="utf8"))
    output = strip_positions(Path(sys.argv[1]).read_text(encoding="utf8"))

    cards = [
        {
            "title": card["title"],
            "assumes": card["assumes"],
            "declarations": [
                check_declaration(name, card["assumes"], output) for name in card["decls"]
            ],
        }
        for card in expected["cards"]
    ]
    declarations = [result for card in cards for result in card["declarations"]]
    failed = [result for result in declarations if not result["ok"]]
    goal = expected.get("goal")
    goal_result = next(
        (result for result in declarations if goal and result["name"] == goal["decl"]), None
    )

    report = {
        "ok": not failed,
        "goal": goal_result and {"title": goal["title"], **goal_result},
        "checked": len(declarations),
        "failed": len(failed),
        "cards": cards,
        "fromMathlib": expected["fromMathlib"],
        "notFormal": expected["notFormal"],
    }
    record = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    Path("verification.json").write_text(record, encoding="utf8")

    print("PASSED" if not failed else "FAILED")
    if goal_result:
        print()
        print(f"  {goal['title']}")
        print(f"  {goal_result['name']}")
        if goal_result["ok"]:
            print(f"  axioms: {', '.join(goal_result['axioms']) or 'none'}")
    print()
    print(
        f"{len(declarations)} declarations behind {len(cards)} Formal cards checked, "
        f"{len(failed)} failed."
    )
    for result in failed:
        print(f"  {result['name']}: {result['problem']}")
    if expected["fromMathlib"]:
        print(f"{len(expected['fromMathlib'])} results taken from Stacks, compiled with the build.")
    if expected["notFormal"]:
        print(f"{len(expected['notFormal'])} cards not proved in Lean: see verification.json.")
    print()
    print("Lean checks each proof; it does not check that a statement says what is claimed.")
    print("Read the statement in README.md for that.")
    print("Full record: verification.json")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
