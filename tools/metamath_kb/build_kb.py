from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parents[2]
PDF_DIR = ROOT / "元数学基础"
KB_DIR = ROOT / "knowledge" / "metamath-foundations"


DOC_SPECS = [
    {
        "id": "MF1",
        "volume": 1,
        "volume_label": "第一卷",
        "short_title": "初始基本法则与有限性",
        "filename_contains": "第一卷",
        "chapter_span": "第1-4章",
    },
    {
        "id": "MF2",
        "volume": 2,
        "volume_label": "第二卷",
        "short_title": "基本实在无穷",
        "filename_contains": "第二卷",
        "chapter_span": "第5-8章",
    },
    {
        "id": "MF3",
        "volume": 3,
        "volume_label": "第三卷",
        "short_title": "CFZFC概念文字",
        "filename_contains": "第三卷",
        "chapter_span": "第9-12章",
    },
]


IMPORTANT_TERMS = [
    "CFZFC",
    "ZFC",
    "元语言",
    "形式语言",
    "具体证明",
    "逻辑公理",
    "演绎方法",
    "全域化方法",
    "集合论",
    "等式",
    "子集合",
    "关系",
    "函数",
    "自然数",
    "有限性",
    "无穷公理",
    "归纳法",
    "递归",
    "序数",
    "彻底有限集合",
    "二进制",
    "一阶逻辑",
    "表达式",
    "替换",
    "可替换性",
    "语义解释",
    "塔尔斯基",
    "真实性",
    "完备性",
]


@dataclass(frozen=True)
class Doc:
    id: str
    volume: int
    volume_label: str
    short_title: str
    chapter_span: str
    path: Path


def ensure_dirs() -> None:
    for sub in [
        KB_DIR,
        KB_DIR / "index",
        KB_DIR / "renders",
        KB_DIR / "notes",
    ]:
        sub.mkdir(parents=True, exist_ok=True)


def find_docs() -> list[Doc]:
    docs: list[Doc] = []
    for spec in DOC_SPECS:
        matches = sorted(PDF_DIR.glob(f"*{spec['filename_contains']}*.pdf"))
        if not matches:
            raise FileNotFoundError(f"Missing PDF for {spec['volume_label']} in {PDF_DIR}")
        if len(matches) > 1:
            names = ", ".join(p.name for p in matches)
            raise RuntimeError(f"Ambiguous PDF match for {spec['volume_label']}: {names}")
        docs.append(
            Doc(
                id=str(spec["id"]),
                volume=int(spec["volume"]),
                volume_label=str(spec["volume_label"]),
                short_title=str(spec["short_title"]),
                chapter_span=str(spec["chapter_span"]),
                path=matches[0],
            )
        )
    return docs


def sha256_prefix(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def outline_records(reader: PdfReader) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []

    def walk(items: list[Any], level: int, parent_path: list[str]) -> None:
        last_path = parent_path
        for item in items:
            if isinstance(item, list):
                walk(item, level + 1, last_path)
                continue
            title = str(getattr(item, "title", item)).strip()
            try:
                page = reader.get_destination_page_number(item) + 1
            except Exception:
                page = None
            path = [*parent_path, title]
            records.append(
                {
                    "level": level,
                    "title": title,
                    "pdf_page": page,
                    "path": path,
                }
            )
            last_path = path

    try:
        outline = reader.outline
    except Exception:
        outline = []
    walk(outline, 1, [])

    for i, rec in enumerate(records):
        next_page = None
        for later in records[i + 1 :]:
            if later["pdf_page"] is None:
                continue
            if later["level"] <= rec["level"]:
                next_page = later["pdf_page"]
                break
        if rec["pdf_page"] is None:
            rec["pdf_page_end"] = None
        elif next_page is None:
            rec["pdf_page_end"] = len(reader.pages)
        else:
            rec["pdf_page_end"] = max(rec["pdf_page"], next_page - 1)
    return records


def first_body_page(records: list[dict[str, Any]]) -> int | None:
    chapter_re = re.compile(r"第\s*\d+\s*章")
    for rec in records:
        if rec["pdf_page"] and chapter_re.search(rec["title"]):
            return int(rec["pdf_page"])
    return None


def book_page(pdf_page: int, body_start: int | None) -> int | None:
    if body_start is None or pdf_page < body_start:
        return None
    return pdf_page - body_start + 1


def current_section(records: list[dict[str, Any]], pdf_page: int) -> dict[str, Any] | None:
    current = None
    for rec in records:
        start = rec.get("pdf_page")
        if start is None or start > pdf_page:
            continue
        end = rec.get("pdf_page_end") or start
        if pdf_page <= end:
            if current is None or rec["level"] >= current["level"]:
                current = rec
    return current


def normalized_title_terms(title: str) -> list[str]:
    parts = re.split(r"[\s:：,，.。()（）/]+", title)
    terms = [p for p in parts if p and not re.fullmatch(r"\d+(?:\.\d+)*", p)]
    for term in IMPORTANT_TERMS:
        if term in title and term not in terms:
            terms.append(term)
    return terms


def load_catalog() -> dict[str, Any]:
    path = KB_DIR / "catalog.json"
    if not path.exists():
        raise FileNotFoundError(f"Run build first: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def load_sections() -> list[dict[str, Any]]:
    path = KB_DIR / "index" / "sections.jsonl"
    if not path.exists():
        raise FileNotFoundError(f"Run build first: {path}")
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            rows.append(json.loads(line))
    return rows


def write_json(path: Path, data: Any) -> None:
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as f:
        for rec in records:
            f.write(json.dumps(rec, ensure_ascii=False, sort_keys=True) + "\n")


def make_catalog(docs: list[Doc]) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    catalog_docs: list[dict[str, Any]] = []
    section_rows: list[dict[str, Any]] = []
    page_rows: list[dict[str, Any]] = []

    for doc in docs:
        reader = PdfReader(str(doc.path))
        records = outline_records(reader)
        body_start = first_body_page(records)
        digest = sha256_prefix(doc.path)
        meta = {str(k): str(v) for k, v in (reader.metadata or {}).items()}

        catalog_docs.append(
            {
                "id": doc.id,
                "volume": doc.volume,
                "volume_label": doc.volume_label,
                "short_title": doc.short_title,
                "chapter_span": doc.chapter_span,
                "pdf_path": str(doc.path.relative_to(ROOT)).replace("\\", "/"),
                "pages": len(reader.pages),
                "body_start_pdf_page": body_start,
                "sha256": digest,
                "pdf_metadata": meta,
                "text_layer_reliability": "weak-navigation-only",
                "source_of_truth": "PDF page rendering, not copied text",
            }
        )

        for idx, rec in enumerate(records, start=1):
            if rec["pdf_page"] is None:
                continue
            section_rows.append(
                {
                    "doc_id": doc.id,
                    "section_id": f"{doc.id}.S{idx:03d}",
                    "level": rec["level"],
                    "title": rec["title"],
                    "path": rec["path"],
                    "pdf_page": rec["pdf_page"],
                    "pdf_page_end": rec["pdf_page_end"],
                    "book_page": book_page(rec["pdf_page"], body_start),
                    "book_page_end": book_page(rec["pdf_page_end"], body_start)
                    if rec["pdf_page_end"]
                    else None,
                    "terms": normalized_title_terms(rec["title"]),
                    "citation": f"{doc.id}:p{rec['pdf_page']}",
                }
            )

        for pdf_page in range(1, len(reader.pages) + 1):
            sec = current_section(records, pdf_page)
            page_rows.append(
                {
                    "doc_id": doc.id,
                    "pdf_page": pdf_page,
                    "book_page": book_page(pdf_page, body_start),
                    "section_path": sec["path"] if sec else [],
                    "section_title": sec["title"] if sec else None,
                    "citation": f"{doc.id}:p{pdf_page}",
                    "render_hint": f"python tools/metamath_kb/build_kb.py render --doc {doc.id} --pages {pdf_page}",
                }
            )

    catalog = {
        "name": "元数学基础形式化知识库",
        "version": 1,
        "created_by": "tools/metamath_kb/build_kb.py",
        "principle": "书签和页码用于导航；文本层只作弱检索；定义、公式、证明必须回到页面图像核验。",
        "documents": catalog_docs,
    }
    return catalog, section_rows, page_rows


def outline_markdown(catalog: dict[str, Any], sections: list[dict[str, Any]]) -> str:
    lines = [
        "# 元数学基础章节导航",
        "",
        "引用格式：`MF1:p12` 表示第一卷 PDF 第 12 页。`book_page` 只在正文页有效。",
        "",
    ]
    for doc in catalog["documents"]:
        lines.append(f"## {doc['id']} {doc['volume_label']}：{doc['short_title']}")
        lines.append("")
        doc_sections = [s for s in sections if s["doc_id"] == doc["id"]]
        for s in doc_sections:
            if s["level"] > 4:
                continue
            indent = "  " * max(0, s["level"] - 1)
            body = (
                f"{indent}- {s['title']} "
                f"({s['citation']}, PDF {s['pdf_page']}-{s['pdf_page_end']}"
            )
            if s["book_page"] is not None:
                body += f", 书内 {s['book_page']}-{s['book_page_end']}"
            body += ")"
            lines.append(body)
        lines.append("")
    return "\n".join(lines) + "\n"


def readme_text(catalog: dict[str, Any]) -> str:
    docs_table = "\n".join(
        f"| {d['id']} | {d['volume_label']} | {d['short_title']} | {d['pages']} | "
        f"{d['body_start_pdf_page']} |"
        for d in catalog["documents"]
    )
    return f"""# 元数学基础形式化知识库

这个目录是给后续 Lean 形式化使用的文献导航层。

重要原则：这些 PDF 的文字层含有隐藏 OCR 和自定义字体映射，复制或抽取出的公式经常乱码。因此本知识库不把抽取文本当作证明依据。可信来源永远是 PDF 页面渲染图或人工核对后的摘录。

## 文献

| ID | 卷 | 主题 | PDF 页数 | 正文起始 PDF 页 |
| --- | --- | --- | ---: | ---: |
{docs_table}

## 入口文件

- `catalog.json`：三卷 PDF 的元数据、页数、SHA256、可靠性说明。
- `model-entry.md`：给大模型恢复上下文时优先读取的入口。
- `query-guide.md`：常见形式化问题应该查哪一卷、哪一章。
- `outline.md`：由 PDF 书签生成的章节导航。
- `index/sections.jsonl`：机器可读的章节/小节索引。
- `index/pages.jsonl`：每一 PDF 页对应的当前章节路径和渲染命令。
- `formalization-roadmap.md`：面向 Lean 的长期形式化路线。
- `reading-protocol.md`：处理乱码、引用、人工转写和页面核验的规则。
- `symbol-guide-seed.md`：基于“部分基本元语言符号说明”的初始符号表，所有条目均需按页核验。

## 常用命令

按需渲染页面：

```powershell
python tools/metamath_kb/build_kb.py render --doc MF1 --pages 10,12-15
```

索引搜索，优先查书签/章节标题：

```powershell
python tools/metamath_kb/build_kb.py search 自然数表示定理
```

慢速全文扫描仅用于补救：

```powershell
python tools/metamath_kb/build_kb.py search 自然数表示定理 --full-text
```

重建索引：

```powershell
python tools/metamath_kb/build_kb.py build
```

## 引用约定

- `MF1:p12`：第一卷 PDF 第 12 页。
- `MF2:p13/book1`：第二卷 PDF 第 13 页，正文书内第 1 页。
- 若 Lean 注释中引用文献，优先写 PDF 页码；书内页码可附在后面。
"""


def model_entry_text() -> str:
    return """# 模型入口

这是后续形式化时优先读取的短入口。完整导航见 `outline.md`。

## 最高优先级事实

- 三卷 PDF 是主要文献，但文字层不可信；公式、定义、证明必须回到页面图像核验。
- 引用格式固定为 `MF1:p12`、`MF2:p62`、`MF3:p365`。
- `index/sections.jsonl` 用来定位章节，`index/pages.jsonl` 用来从页码反查章节路径。
- 渲染页面命令：`python tools/metamath_kb/build_kb.py render --doc MF1 --pages 12-15`。
- 索引搜索命令：`python tools/metamath_kb/build_kb.py search 具体证明`。

## 三卷依赖关系

1. `MF1` 第一卷：从初始 CFZFC 元语法开始，到基本集合理论、自然离散线性序、有限性。
2. `MF2` 第二卷：无穷公理、omega、自然数表示、递归、彻底有限集合、二进制编码。
3. `MF3` 第三卷：一阶逻辑对象语言的集合编码、语义解释、真实性、完整 CFZFC 理论。

## 形式化时的默认策略

- 先建对象语言语法和证明关系，不急着证明书中所有编号步骤。
- 对大段机械证明，优先抽出可复用引理和自动化策略。
- Lean 注释使用中文，并标注来源页码。
- 区分三层：Lean 元层、书中的集合论对象层、书中的元语言解释层。

## 下一批最值得核验的页

- `MF1:p10`：基本元语言符号说明。
- `MF1:p12-p15`：初始 CFZFC 表达式、自由/约束变元、替换、逻辑公理和证明。
- `MF2:p13-p20`：无穷公理和 omega 定义入口。
- `MF3:p102-p107`：一阶语言集合表示入口。
- `MF3:p365-p369`：语义解释和真实性定义入口。
"""


def query_guide_text() -> str:
    return """# 查询手册

这个文件回答“我现在要形式化 X，应该先读哪里”。

| 目标 | 优先入口 | 备注 |
| --- | --- | --- |
| 具体表达式/公式语法 | `MF1:p12-p14`，1.1 | 先核验构造子和级别限制 |
| 自由变元、约束变元 | `MF1:p12-p13`，1.1.2 | 适合做递归函数和判定引理 |
| 替换、可替换性 | `MF1:p13`，1.1.3；`MF3:p315-p348`，9.2.5 | 第三卷是一阶语言版本 |
| 简写符号 | `MF1:p14`，1.1.4 | 注意书中简写不一定是 Lean 定义等式 |
| 逻辑公理模式 | `MF1:p14-p15`，1.2 | 建议建成模式生成器 |
| 具体证明/推导规则 | `MF1:p15-p17`，1.3 | 对象层 proof relation |
| 基本集合论公理 | `MF1:p55`，2.2 | 先列接口，后补证明 |
| 关系和函数 | `MF1:p87-p207`，2.4 | 后续多数章节的基础库 |
| 有限性 | `MF1:p671-p724`，第4章 | 与 Lean `Finite` 不可直接混同 |
| 无穷公理与 omega | `MF2:p13-p20`，5.1.1-5.1.2 | 自然数表示问题入口 |
| 自然数表示定理 | `MF2:p62-p65`，5.1.3 | 后续自然数编码的关键 |
| 递归定义 | `MF2:p147-p224`，5.5；`MF2:p314-p357`，6.2 | 建议先形式化抽象递归接口 |
| 彻底有限集合 | `MF2:p384-p447`，7.1-7.2 | 第三卷语法资源的基础 |
| 二进制编码 | `MF2:p491-p575`，7.6 | 适合做编码层库 |
| 一阶语言集合表示 | `MF3:p102-p106`，9.2.1-9.2.2 | 第三卷主线入口 |
| 项与项序列 | `MF3:p107-p189`，9.2.3 | 公式语法前置 |
| 表达式谓词 | `MF3:p190-p314`，9.2.4 | 大段机械证明，应策略化 |
| 演绎系统形式表述 | `MF3:p362-p364`，9.2.7 | 对象层 proof relation 的完整版本 |
| 语义解释 | `MF3:p365-p368`，10.1 | 模型/赋值接口 |
| 塔尔斯基真实性 | `MF3:p369-p372`，10.2.1 | 语义递归核心 |
| 完整 CFZFC | `MF3:p374-p382`，第11章 | 后期集成目标 |

## 检索建议

1. 优先查 `outline.md`。
2. 若只记得中文术语，用 `build_kb.py search` 做弱搜索。
3. 找到页码后必须渲染页面核验，尤其是含公式处。
"""


def roadmap_text() -> str:
    return """# Lean 形式化路线图

这份路线图按依赖顺序组织，而不是按阅读兴趣组织。

## 第 0 层：文献处理与引用规范

- 固定引用格式：`MFx:pN`。
- 所有定义、公式和证明转写必须从页面图像核验，不从复制文本直接进入 Lean。
- 每个 Lean 文件开头保留中文注释，说明对应章节和页码范围。

## 第 1 层：初始 CFZFC 元语法

来源：`MF1` 第 1 章，尤其 1.1-1.4。

目标：
- 有限变元符号、谓词符号、基本表达式。
- 表达式级别、自由变元、约束变元。
- 替换与可替换性。
- 逻辑公理模式、推导规则、具体证明。

Lean 方向：
- 先用归纳类型和有限索引实现语法对象。
- 证明递归定义和判定性，而不是急着复刻书中所有编号证明。
- 机械性语法引理应封装成通用 simp/decide/omega 风格工具。

## 第 2 层：基本集合理论接口

来源：`MF1` 第 2 章。

目标：
- 等式定理、非逻辑公理、子集合谓词、可定义子集合。
- 关系、函数、定义域、值域、像、复合等基础接口。

Lean 方向：
- 先抽象出“对象语言集合论”的语法和证明关系。
- 区分元层 Lean 集合/函数与目标语言内部集合/函数。

## 第 3 层：有限性与自然离散线性序

来源：`MF1` 第 3-4 章。

目标：
- 自然离散线性序、秩序、代数运算。
- 有穷性、势比较、戴德金有限性。

Lean 方向：
- 将高频证明模式整理成可复用的序结构、有限性、势比较接口。
- 对证明编号密集段优先形式化可复用定理，不逐行照搬。

## 第 4 层：无穷公理、自然数、递归

来源：`MF2` 第 5-8 章。

目标：
- 无穷公理、omega、自然数表示定理、数学归纳法。
- 序数性质、自然数算术、递归定义、超限递归。
- 彻底有限集合、自然数二进制表示、典型列表。

Lean 方向：
- 明确书中“自然数表示问题”和 Lean 内建 `Nat` 的关系。
- 优先构造编码层：有限序列、二进制、Vω 列表。

## 第 5 层：一阶逻辑与 CFZFC 概念文字

来源：`MF3` 第 9-12 章。

目标：
- 有限序列合并运算。
- 一阶语言的集合表示、项、公式、表达式、替换。
- 一阶逻辑演绎系统、语义解释、塔尔斯基真实性、完备性入口。
- 完整 CFZFC 理论与应用讨论。

Lean 方向：
- 先形式化语法编码和语义解释的接口。
- 完备性定理可作为后期目标；早期只建立依赖骨架和定义正确性。
"""


def protocol_text() -> str:
    return """# 阅读与转写协议

## PDF 文字层可靠性

本套 PDF 页面显示正常，但复制/抽取文本会在公式密集页出现乱码。原因包括隐藏 OCR 层、自定义 CID 字体、纵横排混合和私有符号映射。

因此：
- 章节书签可信，用作导航。
- 自然语言抽取可作弱检索。
- 公式、定义、证明编号、逻辑符号必须看页面图像核验。
- 不允许把复制出的乱码公式直接转成 Lean。

## 工作流程

1. 先在 `outline.md` 或 `index/sections.jsonl` 定位章节。
2. 用弱搜索找到候选页时，只把它当定位线索。
3. 渲染候选页：

```powershell
python tools/metamath_kb/build_kb.py render --doc MF2 --pages 13-16 --dpi 180
```

4. 人工从页面图像转写定义或定理，保留页码引用。
5. 转写进入 Lean 前，先写中文注释说明：
   - 文献位置；
   - 书中对象语言符号与 Lean 名称的对应；
   - 是否为忠实转写、结构化改写、或抽象接口。

## 引用格式

- 文档内：`MF3:p365`
- Lean 注释：`-- 来源：MF3:p365，10.1.1 相关结构概念`
- 笔记文件名：`MF3_p365_semantics.md`

## 精度等级

- `verified-image`：已从页面图人工核验。
- `weak-text`：仅由 PDF 文本层或 OCR 得到，只能用于检索。
- `inferred`：根据章节结构和上下文推断，必须标注。
"""


def symbol_seed_text() -> str:
    return """# 基本元语言符号种子表

来源页：`MF1:p10`、`MF2:p10`、`MF3:p10` 的“部分基本元语言符号说明”。由于文本层不稳定，下列条目是面向形式化的释义种子，不是逐字转写。

| 符号/记号 | 初步含义 | 形式化提示 | 状态 |
| --- | --- | --- | --- |
| `r_x` / `Γ_x` 风格记号 | 具体集合论公理组序列中由下标指定的理论 | Lean 中可建模为理论扩张序列或有限公理集索引 | needs-image-check |
| `T_x` | 具体证明中局部使用的集合理论假设组 | 建模为局部上下文/假设集合 | needs-image-check |
| `←` | 左侧理论或假设推出右侧命题 | 不要直接等同 Lean 的 `⊢`；需要对象层证明关系 | needs-image-check |
| `B_x` | 具体形式定义序列中的定义表达式 | 可对应定义注册表或缩写环境 | needs-image-check |
| 逻辑公理编号 | 具体逻辑公理序列中的条目 | 适合建模为公理模式实例生成器 | needs-image-check |
| 专有表达式编号 | 具体专有表达式序列中的条目 | 适合建模为命名表达式环境 | needs-image-check |
| 全局/局部标识表达式 | 书中用于复用长表达式的标识符 | Lean 中应显式区分 abbreviation 与 theorem label | needs-image-check |
| `≡` / “令 ... 为” | 标识符与表达式之间的恒等替换关系 | 可建模为局部记号展开规则 | needs-image-check |
| 方括号注释 | 说明当前定理/证明步骤来源 | Lean 注释保留，自动化证明不必逐字模拟 | needs-image-check |
| 证明行编号 | 证明内部的步骤标识，可能不连续 | Lean 中可用局部 lemma 名称或注释追踪 | needs-image-check |

下一步建议：先渲染 `MF1:p10`、`MF1:p12-p15`，人工建立一份可靠的“符号到 Lean 名称”对照表。
"""


def renders_readme_text() -> str:
    return """# 页面渲染缓存

这里存放 `build_kb.py render` 生成的页面图片。不要把图片当作派生文本；它们只是为了让模型和人核验 PDF 原页。

示例：

```powershell
python tools/metamath_kb/build_kb.py render --doc MF1 --pages 10,12-15
```
"""


def build(_args: argparse.Namespace) -> None:
    ensure_dirs()
    docs = find_docs()
    catalog, sections, pages = make_catalog(docs)
    write_json(KB_DIR / "catalog.json", catalog)
    write_jsonl(KB_DIR / "index" / "sections.jsonl", sections)
    write_jsonl(KB_DIR / "index" / "pages.jsonl", pages)
    (KB_DIR / "README.md").write_text(readme_text(catalog), encoding="utf-8", newline="\n")
    (KB_DIR / "model-entry.md").write_text(
        model_entry_text(), encoding="utf-8", newline="\n"
    )
    (KB_DIR / "query-guide.md").write_text(
        query_guide_text(), encoding="utf-8", newline="\n"
    )
    (KB_DIR / "outline.md").write_text(
        outline_markdown(catalog, sections), encoding="utf-8", newline="\n"
    )
    (KB_DIR / "formalization-roadmap.md").write_text(
        roadmap_text(), encoding="utf-8", newline="\n"
    )
    (KB_DIR / "reading-protocol.md").write_text(
        protocol_text(), encoding="utf-8", newline="\n"
    )
    (KB_DIR / "symbol-guide-seed.md").write_text(
        symbol_seed_text(), encoding="utf-8", newline="\n"
    )
    (KB_DIR / "renders" / "README.md").write_text(
        renders_readme_text(), encoding="utf-8", newline="\n"
    )
    print(f"Built knowledge base at {KB_DIR}")
    print(f"Documents: {len(catalog['documents'])}; sections: {len(sections)}; pages: {len(pages)}")


def parse_pages(spec: str) -> list[int]:
    pages: set[int] = set()
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            start_s, end_s = part.split("-", 1)
            start, end = int(start_s), int(end_s)
            if start > end:
                raise ValueError(f"Bad page range: {part}")
            pages.update(range(start, end + 1))
        else:
            pages.add(int(part))
    return sorted(pages)


def doc_path_from_catalog(doc_id: str) -> Path:
    catalog = load_catalog()
    for doc in catalog["documents"]:
        if doc["id"].lower() == doc_id.lower():
            return ROOT / doc["pdf_path"]
    ids = ", ".join(d["id"] for d in catalog["documents"])
    raise ValueError(f"Unknown doc id {doc_id!r}; expected one of {ids}")


def render(args: argparse.Namespace) -> None:
    ensure_dirs()
    pdf = doc_path_from_catalog(args.doc)
    pages = parse_pages(args.pages)
    out_dir = KB_DIR / "renders" / args.doc.upper()
    out_dir.mkdir(parents=True, exist_ok=True)
    for page in pages:
        prefix = out_dir / f"p{page:04d}"
        cmd = [
            "pdftoppm",
            "-png",
            "-f",
            str(page),
            "-l",
            str(page),
            "-singlefile",
            "-r",
            str(args.dpi),
            "-cropbox",
            "-q",
            str(pdf),
            str(prefix),
        ]
        subprocess.run(cmd, check=True)
        print(prefix.with_suffix(".png"))


def search(args: argparse.Namespace) -> None:
    sections = load_sections()
    query = " ".join(args.query).strip()
    if not query:
        raise ValueError("Empty query")
    q_lower = query.lower()
    hits: list[dict[str, Any]] = []

    for sec in sections:
        haystack = " ".join(
            [
                sec.get("doc_id", ""),
                sec.get("title", ""),
                " ".join(sec.get("terms", [])),
                " ".join(sec.get("path", [])),
            ]
        ).lower()
        if q_lower not in haystack:
            continue
        hits.append(
            {
                "doc_id": sec["doc_id"],
                "citation": sec["citation"],
                "excerpt": " / ".join(sec["path"]),
                "mode": "outline",
            }
        )
        if len(hits) >= args.limit:
            break

    if len(hits) < args.limit and args.full_text:
        catalog = load_catalog()
        for doc in catalog["documents"]:
            pdf_path = ROOT / doc["pdf_path"]
            reader = PdfReader(str(pdf_path))
            for i, page in enumerate(reader.pages, start=1):
                try:
                    text = page.extract_text() or ""
                except Exception:
                    continue
                normalized = " ".join(text.split())
                if q_lower not in normalized.lower():
                    continue
                pos = normalized.lower().find(q_lower)
                start = max(0, pos - 80)
                end = min(len(normalized), pos + len(query) + 120)
                hits.append(
                    {
                        "doc_id": doc["id"],
                        "pdf_page": i,
                        "book_page": book_page(i, doc.get("body_start_pdf_page")),
                        "citation": f"{doc['id']}:p{i}",
                        "excerpt": normalized[start:end],
                        "mode": "full-text",
                    }
                )
                if len(hits) >= args.limit:
                    break
            if len(hits) >= args.limit:
                break

    for hit in hits:
        if hit["mode"] == "outline":
            print(f"{hit['citation']}: {hit['excerpt']}")
        else:
            book = f"/book{hit['book_page']}" if hit["book_page"] is not None else ""
            print(f"{hit['citation']}{book}: {hit['excerpt']}")
            print(f"  render: python tools/metamath_kb/build_kb.py render --doc {hit['doc_id']} --pages {hit['pdf_page']}")
    if not hits:
        print("No outline hits. Try --full-text for slow PDF-page scanning or render likely chapter pages.")
    else:
        print("Note: outline hits are navigation hints; verify against rendered PDF pages.")


def main() -> None:
    parser = argparse.ArgumentParser(description="Build and use the 元数学基础 knowledge base")
    sub = parser.add_subparsers(dest="command", required=True)

    build_parser = sub.add_parser("build", help="Generate catalog, outline, and indices")
    build_parser.set_defaults(func=build)

    render_parser = sub.add_parser("render", help="Render PDF pages to PNG for visual reading")
    render_parser.add_argument("--doc", required=True, help="Document id: MF1, MF2, or MF3")
    render_parser.add_argument("--pages", required=True, help="Pages like 10,12-15")
    render_parser.add_argument("--dpi", type=int, default=180)
    render_parser.set_defaults(func=render)

    search_parser = sub.add_parser("search", help="Search outline index; optionally scan weak PDF text")
    search_parser.add_argument("query", nargs="+")
    search_parser.add_argument("--limit", type=int, default=12)
    search_parser.add_argument("--full-text", action="store_true")
    search_parser.set_defaults(func=search)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
