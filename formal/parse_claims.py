"""パーサー。claims.json を読み、検証器を呼び、Lean の値と定理のファイルを書き、Lean の出力から判定を読む。"""
import json
import re
import subprocess
from fractions import Fraction
from pathlib import Path

from verifiers import QUERIES

FORMAL = Path(__file__).parent
# 型ごとの、Lean での書き方
LITERAL = {
    "String": json.dumps,
    "Bool": lambda value: str(bool(value)).lower(),
    "ℕ": lambda value: str(int(value)),
    "ℚ": lambda value: f"(({Fraction(value).numerator} : ℚ) / {Fraction(value).denominator})",
}
HEADER = ["import Values", "import Claims", "open Claims"]
# 引用先の状態ごとに、受け取る命題。ここに無い状態は引用しても前提として受け取らない
RECEIVES = {("verified", "真"): "P", ("verified", "偽"): "¬P", ("unverifiable", None): "P"}


def lean_literal(lean_type: str, value) -> str:
    if lean_type.startswith("List "):
        return "[" + ", ".join(lean_literal(lean_type.removeprefix("List "), item) for item in value) + "]"
    return LITERAL[lean_type](value)


def read_claims() -> dict:
    record = json.loads((FORMAL / "claims.json").read_text(encoding="utf-8"))
    unknown = [claim["id"] for claim in record["claims"] if claim["sentence"] not in record["sentences"]]
    if unknown:
        raise ValueError(f"存在しない文を指している: {unknown}")
    # 分解器が付けた印と、形式化の形を突き合わせる。定義は値を受けず、それ以外は値を受けるか、検証器が無い
    mismatched = [claim["id"] for claim in record["claims"]
                  if claim.get("definition", False) == bool(claim["formalization"]["arguments"]) and "unverifiable" not in claim]
    if mismatched:
        raise ValueError(f"定義の印と、値の引数が食い違っている: {mismatched}")
    return record


def write_values(repository: str, mode: str) -> tuple[dict[str, str], dict[str, str]]:
    """変数ごとに、宣言した値を読むか、検証器に問い合わせて、Values.lean を書く。(値, 取れなかった理由) を返す。"""
    values, errors = {}, {}
    for name, variable in read_claims()["variables"].items():
        try:
            if "declared" in variable:
                value = variable["declared"]
            else:
                query = QUERIES[variable["verifier"]][variable["query"]]
                value = query(repository, mode, name, **variable.get("args", {}))
            values[name] = lean_literal(variable["type"], value)
        except Exception as error:  # 取れなかった値を使う claim だけを、判定できずにする
            errors[name] = str(error)
    lines = ["import Mathlib", "/-! 検証器が返した値と、宣言した値。parse_claims.py が生成する。手で編集しない。 -/", "namespace Values"]
    lines += [f"def {name} : {read_claims()['variables'][name]['type']} := {literal}" for name, literal in values.items()]
    (FORMAL / "lean" / "Values.lean").write_text("\n".join(lines + ["end Values", ""]), encoding="utf-8")
    return values, errors


def proposition(claim: dict) -> str:
    """命題名に、値を名前付きの引数として付ける。"""
    formalization = claim["formalization"]
    return " ".join([formalization["proposition_name"]] + [f"({name} := Values.{name})" for name in formalization["arguments"]])


def candidates(claim: dict) -> list[str]:
    """命題が真である定理と、偽である（否定の）定理。通ったほうが判定になる。有理数の比較は decide では簡約が止まるので、kernel に評価させる。"""
    name, statement = claim["id"], proposition(claim)
    # 検証器が無い claims は、公理が宣言されていることだけを見る
    if "unverifiable" in claim:
        return [f"#print axioms {name}_axiom"]
    # 引用した公理を使う claims は、宣言で証明した補題に、値の条件を decide で渡す
    if "proof" in claim["formalization"]:
        values = " ".join(f"Values.{argument}" for argument in claim["formalization"]["arguments"])
        proof = claim["formalization"]["proof"]
        return [f"theorem {name}_holds : {statement} := {proof['holds']} {values} (by decide +kernel)",
                f"theorem {name}_fails : ¬ ({statement}) := {proof['fails']} {values} (by decide +kernel)",
                f"#print axioms {name}_holds", f"#print axioms {name}_fails"]
    # 定義は、定義を展開すれば両辺が一致する等式（とその連言）だけを通す
    if claim.get("definition"):
        return [f"theorem {name}_holds : {statement} := by unfold {statement}; intros; and_intros <;> rfl",
                f"#print axioms {name}_holds"]
    return [f"theorem {name}_holds : {statement} := by decide +kernel",
            f"theorem {name}_fails : ¬ ({statement}) := by decide +kernel",
            f"#print axioms {name}_holds", f"#print axioms {name}_fails"]


def write_candidates(claims: list[dict]) -> Path:
    """claims の定理の候補と公理の確認を、1 つのファイルに書く。Lean の起動を 1 回で済ませる。"""
    lines = HEADER + [line for claim in claims for line in candidates(claim)]
    path = FORMAL / "lean" / "Candidates.lean"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def read_axioms(lean_output: str) -> dict[str, list[str] | None]:
    """定理ごとの、依存する公理。証明が通らなかった定理は sorryAx に依存する。出力に無い定理は None。名前の Claims. は外す。"""
    flat = re.sub(r"\s+", " ", lean_output)
    short = lambda name: name.removeprefix("Claims.")
    axioms = {short(name): [] for name in re.findall(r"'([\w.]+)' does not depend on any axioms", flat)}
    axioms |= {short(name): [short(axiom) for axiom in listed.split(", ")]
               for name, listed in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", flat)}
    return axioms


def judge(claim: dict, allowed_axioms: set[str], axioms: dict) -> dict:
    """真か偽か判定できずか。通った定理が、宣言した公理の外に依存していたら、判定できずにする。"""
    for verdict, suffix in (("真", "holds"), ("偽", "fails")):
        used = axioms.get(f"{claim['id']}_{suffix}")
        if used is not None and "sorryAx" not in used:
            if set(used) <= allowed_axioms:
                return {"verdict": verdict, "axioms": sorted(used)}
            return {"verdict": "判定できず", "reason": f"宣言した公理の外に依存している: {sorted(set(used) - allowed_axioms)}"}
    return {"verdict": "判定できず", "reason": "真の定理も偽の定理も通らなかった"}


def write_theorems(claims: list[dict], results: dict) -> None:
    """判定が付いた命題を、真なら定理、偽なら否定の定理として Theorems.lean に書く。"""
    lines = HEADER + ["/-! 各命題の判定。parse_claims.py が生成する。 -/"]
    lines += [candidates(claim)[results[claim["id"]]["verdict"] == "偽"] for claim in claims
              if results[claim["id"]].get("verdict") in ("真", "偽")]
    (FORMAL / "lean" / "Theorems.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")


def _file_at(repository: str, commit: str, path: str) -> str:
    owner_repo = repository.removeprefix("https://github.com/")
    return subprocess.run(["gh", "api", f"repos/{owner_repo}/contents/{path}?ref={commit}", "-H", "Accept: application/vnd.github.raw"],
                          check=True, capture_output=True, text=True).stdout


def _declaration(lean: str, keyword: str, name: str) -> str:
    """Lean のファイルから、その名前の宣言を、次の宣言の手前まで取り出す。"""
    match = re.search(rf"^{keyword} {name}\b.*?(?=\n(?:abbrev |/-|def |noncomputable |theorem |axiom |opaque |namespace |end |open )|\n\n)", lean, re.M | re.S)
    if not match:
        raise ValueError(f"引用先に {name} が無い")
    return match.group(0)


def _binders(signature: str) -> list[tuple[str, str]]:
    """明示の引数 (a b : T) を、(名前, 型) の組にする。"""
    return [(name, binder_type.strip()) for names, binder_type in re.findall(r"\(([^():]+):([^()]+)\)", signature) for name in names.split()]


def write_references(record: dict) -> list[dict]:
    """引用先の claims を、その commit から取り出し、公理として References.lean に書く。引用の記録を返す。

    受け取る命題は、引用先の状態で決まる（RECEIVES）。命題に出てくる引用先の値は opaque な定数として置き、
    引用先の定義（def）は、その定義の claims も引用していることを確かめたうえで、opaque な定数として置く。
    """
    lines = ["import Mathlib", "/-! 引用した claims の公理。parse_claims.py が引用先から生成する。手で編集しない。 -/"]
    citations = []
    for reference in record.get("references", []):
        repository, commit, namespace = reference["repository"], reference["commit"], reference["id"].capitalize()
        cited_lean = _file_at(repository, commit, "formal/lean/Claims.lean")
        cited_claims = {claim["id"]: claim for claim in json.loads(_file_at(repository, commit, "formal/claims.json"))["claims"]}
        cited_results = json.loads(_file_at(repository, commit, "formal/results.json"))["claims"]
        definitions = {name: declaration for declaration, name in
                       ((d, re.match(r"(?:noncomputable )?def (\w+)", d).group(1)) for d in
                        re.findall(r"^(?:noncomputable )?def \w+.*?(?=\n(?:/-|abbrev |noncomputable |def |\n))", cited_lean, re.M | re.S))}
        opaques, abbrevs, axioms = {}, [], []
        for claim_id in reference["claims"]:
            result = cited_results[claim_id]
            receives = RECEIVES.get((result["status"], result.get("verdict")))
            if receives is None:
                raise ValueError(f"{reference['id']}#{claim_id} は {result['status']} {result.get('verdict', '')} で、前提として受け取れない")
            abbrev = _declaration(cited_lean, "abbrev", claim_id)
            signature, body = re.split(r":=\s", abbrev, maxsplit=1)
            for name, binder_type in _binders(signature):
                opaques[name] = f"opaque {name} : {binder_type}"
            for name, declaration in definitions.items():
                if re.search(rf"\b{name}\b", body):
                    defined_by = [c for c in reference["claims"] if cited_claims[c].get("definition")
                                  and re.search(rf"(?:,|∧)\s*{name}\b[^=∧]*=", _declaration(cited_lean, "abbrev", c))]
                    if not defined_by:
                        raise ValueError(f"{reference['id']}#{claim_id} が使う {name} の定義の claims を引用していない")
                    opaques[name] = "noncomputable opaque " + declaration.split(":=", 1)[0].removeprefix("noncomputable ").removeprefix("def ").strip()
            abbrevs.append(abbrev)
            arguments = " ".join(name for name, _ in _binders(signature))
            statement = f"{claim_id} {arguments}".strip()
            axioms.append(f"axiom {claim_id}_cited : {statement if receives == 'P' else f'¬ ({statement})'}")
            citations.append({"claim": f"{reference['id']}#{claim_id}", "commit": commit, "status": result["status"],
                              "verdict": result.get("verdict"), "receives": receives, "axiom": f"{namespace}.{claim_id}_cited"})
        lines += [f"namespace {namespace}", f"-- {repository} の commit {commit}"] + list(opaques.values()) + abbrevs + axioms + [f"end {namespace}", ""]
    (FORMAL / "lean" / "References.lean").write_text("\n".join(lines), encoding="utf-8")
    return citations
