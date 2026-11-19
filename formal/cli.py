"""ワークフローが呼ぶ入口。宣言ファイルと claims を読んで実行する。

  python formal/cli.py run full|sanity     宣言された実験を実行し、artifact にするものを run-output/ に集める
  python formal/cli.py verify full|sanity  変数の値を検証器から取り、Lean で各 claim を判定し、結果を書く
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import urllib.request
from pathlib import Path

FORMAL = Path(__file__).parent
RUN_OUTPUT = Path("run-output")


def run(mode: str) -> None:
    declaration = json.loads((FORMAL / "declaration.json").read_text(encoding="utf-8"))
    subprocess.run(declaration["command"] + (declaration["sanity_arguments"] if mode == "sanity" else []), check=True)
    # 実験の出力は outputs/ の下に写す。取得の記録と同じ場所に書かせない
    shutil.rmtree(RUN_OUTPUT, ignore_errors=True)
    for path in declaration["outputs"]:
        target = RUN_OUTPUT / "outputs" / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    # 取得の記録は実験の後に、実験コードとは別に書く
    fetched = {url: hashlib.sha256(urllib.request.urlopen(url).read()).hexdigest()
               for url in declaration["fetch_urls"]}
    (RUN_OUTPUT / "fetched_urls.json").write_text(json.dumps(fetched, indent=2) + "\n", encoding="utf-8")


def verify(mode: str) -> None:
    import parse_claims
    repository = os.environ.get("GITHUB_REPOSITORY") or subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner"],
        check=True, capture_output=True, text=True).stdout.strip()
    lean = FORMAL / "lean"
    record = parse_claims.read_claims()
    values, errors = parse_claims.write_values(repository, mode)
    # 引用した claims を引用先の commit から取り出し、公理として書く
    citations = parse_claims.write_references(record)
    for name, reason in errors.items():
        print(f"値が取れない {name}: {reason}")
    subprocess.run(["lake", "build", "Values", "Claims"], cwd=lean, check=True)

    # 値が揃った claim だけを Lean に渡す。真か偽かは、通った定理で決まる
    judgeable = [claim for claim in record["claims"] if not set(claim["formalization"]["arguments"]) & set(errors)]
    candidates = parse_claims.write_candidates(judgeable)
    output = subprocess.run(["lake", "env", "lean", candidates.name], cwd=lean, capture_output=True, text=True).stdout
    candidates.unlink()
    axioms = parse_claims.read_axioms(output)
    # 検証器が無い claims の公理は、依存してよい公理に加える
    allowed = ({axiom["name"] for axiom in record["axioms"]} | {f"{claim['id']}_axiom" for claim in record["claims"] if "unverifiable" in claim}
               | {citation["axiom"] for citation in citations})

    results = {}
    for claim in record["claims"]:
        lacking = sorted(set(claim["formalization"]["arguments"]) & set(errors))
        if "unverifiable" in claim:
            name = f"{claim['id']}_axiom"
            results[claim["id"]] = {"status": "unverifiable", "reason": claim["unverifiable"],
                                    "axiom": name if axioms.get(name) is not None else None}
        elif lacking:
            results[claim["id"]] = {"status": "unverified", "reason": "値が取れない: " + "、".join(f"{n}（{errors[n]}）" for n in lacking)}
        else:
            results[claim["id"]] = {"status": "verified"} | parse_claims.judge(claim, allowed, axioms)
    parse_claims.write_theorems(record["claims"], results)
    (FORMAL / "results.json").write_text(json.dumps(
        {"repository": repository, "mode": mode, "claims": results, "citations": citations, "values": values},
        ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    for name, result in results.items():
        print(f"{name}: {result['status']} {result.get('verdict', '')}" + (f"（{result['reason']}）" if "reason" in result else ""))
    # 真か偽かは研究の結果。検証として失敗なのは、未検証か判定できずの claim か、公理が宣言されていない claim があるときだけ
    if any(result["status"] == "unverified" or result.get("verdict") == "判定できず"
           or (result["status"] == "unverifiable" and result["axiom"] is None) for result in results.values()):
        sys.exit(1)


if __name__ == "__main__":
    {"run": run, "verify": verify}[sys.argv[1]](sys.argv[2])
